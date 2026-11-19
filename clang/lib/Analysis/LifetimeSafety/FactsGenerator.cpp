//===- FactsGenerator.cpp - Lifetime Facts Generation -----------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include <cassert>
#include <string>

#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/Expr.h"
#include "clang/AST/ExprCXX.h"
#include "clang/AST/OperationKinds.h"
#include "clang/Analysis/Analyses/LifetimeSafety/Facts.h"
#include "clang/Analysis/Analyses/LifetimeSafety/FactsGenerator.h"
#include "clang/Analysis/Analyses/LifetimeSafety/LifetimeAnnotations.h"
#include "clang/Analysis/Analyses/LifetimeSafety/Origins.h"
#include "clang/Analysis/Analyses/PostOrderCFGView.h"
#include "clang/Analysis/CFG.h"
#include "clang/Basic/OperatorKinds.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/Signals.h"
#include "llvm/Support/TimeProfiler.h"

namespace clang::lifetimes::internal {
using llvm::isa_and_present;

OriginList *FactsGenerator::getOriginsList(const ValueDecl &D) {
  return FactMgr.getOriginMgr().getOrCreateList(&D);
}
OriginList *FactsGenerator::getOriginsList(const Expr &E) {
  return FactMgr.getOriginMgr().getOrCreateList(&E);
}

bool FactsGenerator::hasOrigins(QualType QT) const {
  return FactMgr.getOriginMgr().hasOrigins(QT);
}

bool FactsGenerator::hasOrigins(const Expr *E) const {
  return FactMgr.getOriginMgr().hasOrigins(E);
}

/// Propagates origin information from Src to Dst through all levels of
/// indirection, creating OriginFlowFacts at each level.
///
/// This function enforces a critical type-safety invariant: both lists must
/// have the same shape (same depth/structure). This invariant ensures that
/// origins flow only between compatible types during expression evaluation.
///
/// Examples:
///   - `int* p = &x;` flows origins from `&x` (depth 1) to `p` (depth 1)
///   - `int** pp = &p;` flows origins from `&p` (depth 2) to `pp` (depth 2)
///     * Level 1: pp <- p's address
///     * Level 2: (*pp) <- what p points to (i.e., &x)
///   - `View v = obj;` flows origins from `obj` (depth 1) to `v` (depth 1)
///
/// \param Dst The destination origin list.
/// \param Src The source origin list.
/// \param Kill If true, the destination's existing loans are killed before
///             flowing.
/// \param Block Optional. If provided, the generated flow facts are appended to
///              this specific CFG block. Otherwise, they are appended to the
///              current block being visited.
void FactsGenerator::flow(OriginList *Dst, OriginList *Src, bool Kill,
                          const CFGBlock *Block) {
  if (!Dst)
    return;
  assert(Src &&
         "Dst is non-null but Src is null. List must have the same length");
  assert(Dst->getLength() == Src->getLength() &&
         "Lists must have the same length");

  while (Dst && Src) {
    Fact *F = FactMgr.createFact<OriginFlowFact>(Dst->getOuterOriginID(),
                                                 Src->getOuterOriginID(), Kill);
    if (Block)
      FactMgr.appendBlockFact(Block, F);
    else
      CurrentBlockFacts.push_back(F);
    Dst = Dst->peelOuterOrigin();
    Src = Src->peelOuterOrigin();
  }
}

/// Creates a loan for the storage path of a given declaration.
/// This function should be called whenever an expression naming \p VD
/// represents a borrow.
/// \param VD The declaration whose storage is borrowed.
/// \param IssueExpr The expression (DeclRefExpr or MemberExpr) that initiates
/// the borrow.
/// \return The new Loan on success, nullptr otherwise.
static const Loan *createLoan(FactManager &FactMgr, const ValueDecl &VD,
                              const Expr *IssueExpr) {
  return FactMgr.getLoanMgr().createLoan(AccessPath(&VD), IssueExpr);
}

/// Creates a loan for the storage location of a temporary object.
/// \param MTE The MaterializeTemporaryExpr that represents the temporary
/// binding.
/// \param IssueExpr The expression the loan is reported at, if not \p MTE.
/// \return The new Loan.
static const Loan *createLoan(FactManager &FactMgr,
                              const MaterializeTemporaryExpr *MTE,
                              const Expr *IssueExpr = nullptr) {
  return FactMgr.getLoanMgr().createLoan(AccessPath(MTE),
                                         IssueExpr ? IssueExpr : MTE);
}

/// Creates a loan for an allocation through 'new'
/// \param NE The CXXNewExpr that represents the allocation
/// \return The new Loan on success, nullptr otherwise
static const Loan *createLoan(FactManager &FactMgr, const CXXNewExpr *NE) {
  AccessPath Path(NE);
  return FactMgr.getLoanMgr().createLoan(Path, NE);
}

/// Creates a loan for a heap allocation made by a call (e.g. a function
/// annotated with `ownership_returns`, like `malloc`).
/// \param CE The CallExpr that represents the allocation
/// \return The new Loan on success, nullptr otherwise
static const Loan *createNewAllocLoan(FactManager &FactMgr,
                                      const CallExpr *CE) {
  AccessPath Path(CE);
  return FactMgr.getLoanMgr().createLoan(Path, CE);
}

void FactsGenerator::run() {
  llvm::TimeTraceScope TimeProfile("FactGenerator");
  const CFG &Cfg = *AC.getCFG();
  llvm::SmallVector<Fact *> PlaceholderLoanFacts = issuePlaceholderLoans();
  // Iterate through the CFG blocks in reverse post-order to ensure that
  // initializations and destructions are processed in the correct sequence.
  for (const CFGBlock *Block : *AC.getAnalysis<PostOrderCFGView>()) {
    CurrentBlockFacts.clear();
    EscapesInCurrentBlock.clear();
    CurrentBlock = Block;
    if (Block == &Cfg.getEntry())
      CurrentBlockFacts.append(PlaceholderLoanFacts.begin(),
                               PlaceholderLoanFacts.end());
    for (unsigned I = 0; I < Block->size(); ++I) {
      const CFGElement &Element = Block->Elements[I];
      if (std::optional<CFGStmt> CS = Element.getAs<CFGStmt>())
        Visit(CS->getStmt());
      else if (std::optional<CFGInitializer> Initializer =
                   Element.getAs<CFGInitializer>())
        handleCXXCtorInitializer(Initializer->getInitializer());
      else if (std::optional<CFGLifetimeEnds> LifetimeEnds =
                   Element.getAs<CFGLifetimeEnds>())
        handleLifetimeEnds(*LifetimeEnds);
      else if (std::optional<CFGFullExprCleanup> FullExprCleanup =
                   Element.getAs<CFGFullExprCleanup>()) {
        handleFullExprCleanup(*FullExprCleanup);
      }
    }
    if (Block == &Cfg.getExit())
      handleExitBlock();

    CurrentBlockFacts.append(EscapesInCurrentBlock.begin(),
                             EscapesInCurrentBlock.end());
    FactMgr.addBlockFacts(Block, CurrentBlockFacts);
  }
  FactMgr.computePersistentOrigins(Cfg);
}

OriginList *FactsGenerator::readValue(const Expr *E) {
  OriginList *List = getOriginsList(*E);
  if (!List)
    return nullptr;
  if (!E->isGLValue())
    return List;
  handleAccess(E);
  return List->peelOuterOrigin();
}

void FactsGenerator::VisitDeclStmt(const DeclStmt *DS) {
  for (const Decl *D : DS->decls())
    if (const auto *VD = dyn_cast<VarDecl>(D))
      if (const Expr *InitExpr = VD->getInit()) {
        OriginList *VDList = getOriginsList(*VD);
        if (!VDList)
          continue;
        OriginList *InitList = getOriginsList(*InitExpr);
        assert(InitList && "VarDecl had origins but InitExpr did not");
        flow(VDList, InitList, /*Kill=*/true);
      }
}

void FactsGenerator::VisitDeclRefExpr(const DeclRefExpr *DRE) {
  // Skip function references as their lifetimes are not interesting. Skip non
  // GLValues (like EnumConstants).
  if (DRE->getFoundDecl()->isFunctionOrFunctionTemplate() || !DRE->isGLValue())
    return;
  // For all declarations with storage (non-references), we issue a loan
  // representing the borrow of the variable's storage itself.
  //
  // Examples:
  //   - `int x; x` issues loan to x's storage
  //   - `int* p; p` issues loan to p's storage (the pointer variable)
  //   - `View v; v` issues loan to v's storage (the view object)
  //   - `int& r = x; r` issues no loan (r has no storage, it's an alias to x)
  if (doesDeclHaveStorage(DRE->getDecl())) {
    const Loan *L = createLoan(FactMgr, *DRE->getDecl(), DRE);
    assert(L);
    OriginList *List = getOriginsList(*DRE);
    assert(List &&
           "gl-value DRE of non-pointer type should have an origin list");
    // This loan specifically tracks borrowing the variable's storage location
    // itself and is issued to outermost origin (List->OID).
    CurrentBlockFacts.push_back(
        FactMgr.createFact<IssueFact>(L->getID(), List->getOuterOriginID()));
  }
}

/// Whether \p QT should be modelled by the `gsl::Pointer` heuristics.
///
/// A class that declares `LIFETIME_PARAMS` is modelled by those parameters
/// even if it is also a `gsl::Pointer`: its constructors and members carry
/// named signatures, while the heuristics assume a single borrowed origin and
/// handle only one-argument constructors.
static bool isHeuristicGslPointerType(const ASTContext &Ctx, QualType QT) {
  if (!isGslPointerType(QT))
    return false;
  const CXXRecordDecl *RD = QT->getAsCXXRecordDecl();
  const CXXRecordDecl *Def = RD ? RD->getDefinition() : nullptr;
  return !Def || getDeclaredLifetimeParams(Ctx, Def).empty();
}

void FactsGenerator::VisitCXXConstructExpr(const CXXConstructExpr *CCE) {
  if (isHeuristicGslPointerType(AC.getASTContext(), CCE->getType())) {
    handleGSLPointerConstruction(CCE);
    return;
  }
  // For defaulted (implicit or `= default`) copy/move constructors, propagate
  // origins directly. User-defined copy/move constructors are not handled here
  // as they have opaque semantics.
  if (CCE->getConstructor()->isCopyOrMoveConstructor() &&
      CCE->getConstructor()->isDefaulted() && CCE->getNumArgs() == 1 &&
      hasOrigins(CCE->getType())) {
    const Expr *Arg = CCE->getArg(0);
    if (OriginList *ArgList = readValue(Arg)) {
      flow(getOriginsList(*CCE), ArgList, /*Kill=*/true);
      return;
    }
  }
  // Standard library callable wrappers (e.g., std::function) propagate the
  // stored lambda's origins.
  if (const auto *RD = CCE->getType()->getAsCXXRecordDecl();
      RD && isStdCallableWrapperType(RD) && CCE->getNumArgs() == 1) {
    const Expr *Arg = CCE->getArg(0);
    if (OriginList *ArgList = readValue(Arg)) {
      flow(getOriginsList(*CCE), ArgList, /*Kill=*/true);
      return;
    }
  }
  handleFunctionCall(CCE, /*IsGslConstruction=*/false);
}

void FactsGenerator::VisitCXXDefaultArgExpr(const CXXDefaultArgExpr *DAE) {
  // The CFG does not visit a default argument's expression (GH13757), but it
  // does expire the temporaries it materializes.
  // Issue the loan here, reported at the call.
  // FIXME: Model temporaries nested deeper in the default argument.
  const auto *MTE = dyn_cast<MaterializeTemporaryExpr>(
      DAE->getExpr()->IgnoreParenBaseCasts());
  OriginList *List = getOriginsList(*DAE);
  if (!MTE || !List)
    return;
  const Loan *L = createLoan(FactMgr, MTE, /*IssueExpr=*/DAE);
  CurrentBlockFacts.push_back(
      FactMgr.createFact<IssueFact>(L->getID(), List->getOuterOriginID()));
}

void FactsGenerator::VisitCXXDefaultInitExpr(const CXXDefaultInitExpr *DIE) {
  if (const Expr *Init = DIE->getExpr())
    killAndFlowOrigin(*DIE, *Init);
}

void FactsGenerator::handleCXXCtorInitializer(const CXXCtorInitializer *CII) {
  // Flows origins from the initializer expression to the field.
  // Example: `MyObj(std::string s) : view(s) {}`
  if (const FieldDecl *FD = CII->getAnyMember())
    killAndFlowOrigin(*FD, *CII->getInit());
}

void FactsGenerator::VisitCXXMemberCallExpr(const CXXMemberCallExpr *MCE) {
  // Specifically for conversion operators,
  // like `std::string_view p = std::string{};`
  if (isHeuristicGslPointerType(AC.getASTContext(), MCE->getType()) &&
      isa_and_present<CXXConversionDecl>(MCE->getCalleeDecl()) &&
      isGslOwnerType(MCE->getImplicitObjectArgument()->getType())) {
    handleFunctionCall(MCE, /*IsGslConstruction=*/true);
    return;
  }
  handleFunctionCall(MCE, /*IsGslConstruction=*/false);
}

bool FactsGenerator::isFieldOfBaseRecord(const MemberExpr *ME) {
  // The base's origins are laid out by the base expression's own record type.
  // Only substitute when the field is declared directly in that record; a field
  // inherited from a base class refers to the base class's parameters, whose
  // origins are not tracked through the derived type. Look through
  // derived-to-base conversions, which Sema inserts when the field is
  // inherited: what matters is the record the origins belong to.
  const Expr *ObjExpr = ME->getBase()->IgnoreParens();
  while (const auto *CE = dyn_cast<CastExpr>(ObjExpr)) {
    if (CE->getCastKind() != CK_DerivedToBase &&
        CE->getCastKind() != CK_UncheckedDerivedToBase &&
        CE->getCastKind() != CK_NoOp && CE->getCastKind() != CK_LValueToRValue)
      break;
    ObjExpr = CE->getSubExpr()->IgnoreParens();
  }
  QualType BaseTy = ObjExpr->getType();
  if (ME->isArrow())
    BaseTy = BaseTy->getPointeeType();
  const RecordDecl *BaseRD =
      BaseTy.isNull() ? nullptr : BaseTy->getAsRecordDecl();
  const auto *FD = dyn_cast<FieldDecl>(ME->getMemberDecl());
  return FD && BaseRD &&
         BaseRD->getCanonicalDecl() == FD->getParent()->getCanonicalDecl();
}

void FactsGenerator::flowFieldParamSlots(const FieldDecl *FD,
                                         OriginList *FieldValue,
                                         OriginList *BaseParams,
                                         bool IntoField) {
  ASTContext &Ctx = AC.getASTContext();
  LifetimeList FieldLifetimes = getExplicitLifetimes(Ctx, FD->getType());
  if (FieldLifetimes.empty())
    return;
  LifetimeList ClassParams = getDeclaredLifetimeParams(Ctx, FD->getParent());
  for (const LifetimeVar &LV : FieldLifetimes) {
    if (!FieldValue)
      break;
    if (LV.getKind() == LifetimeVar::Kind::Named) {
      // Walk the base's parameter origins in declaration order. If the base
      // has fewer origin levels than the class declares parameters (which
      // should not happen for a well-formed record), leave the remaining slots
      // unsubstituted rather than asserting.
      OriginList *Slot = BaseParams;
      for (const LifetimeVar &Param : ClassParams) {
        if (!Slot)
          break;
        if (Param.getName() == LV.getName()) {
          // Reading substitutes the slot into the field (a strong update of
          // the fresh field origin). Storing adds the field's value to the
          // slot without killing it: the slot stands for every field that
          // names the parameter, so the update is weak.
          OriginID FieldID = FieldValue->getOuterOriginID();
          OriginID SlotID = Slot->getOuterOriginID();
          CurrentBlockFacts.push_back(FactMgr.createFact<OriginFlowFact>(
              IntoField ? FieldID : SlotID, IntoField ? SlotID : FieldID,
              /*Kill=*/IntoField));
          break;
        }
        Slot = Slot->peelOuterOrigin();
      }
    }
    FieldValue = FieldValue->peelOuterOrigin();
  }
}

OriginList *FactsGenerator::getPersistentValueOrigins(const Expr *E) {
  E = E->IgnoreParens();
  if (const auto *CE = dyn_cast<CastExpr>(E);
      CE &&
      (CE->getCastKind() == CK_LValueToRValue || CE->getCastKind() == CK_NoOp))
    return getPersistentValueOrigins(CE->getSubExpr());
  if (const auto *DRE = dyn_cast<DeclRefExpr>(E)) {
    const ValueDecl *VD = DRE->getDecl();
    if (!isa<VarDecl>(VD))
      return nullptr;
    OriginList *List = getOriginsList(*VD);
    if (List && VD->getType()->isReferenceType())
      List = List->peelOuterOrigin();
    return List;
  }
  if (const auto *UO = dyn_cast<UnaryOperator>(E);
      UO && UO->getOpcode() == UO_Deref) {
    OriginList *Pointer = getPersistentValueOrigins(UO->getSubExpr());
    return Pointer ? Pointer->peelOuterOrigin() : nullptr;
  }
  return nullptr;
}

void FactsGenerator::writeBackFieldStore(const MemberExpr *ME,
                                         OriginList *RHSList) {
  const auto *FD = dyn_cast<FieldDecl>(ME->getMemberDecl());
  const Expr *Base = ME->getBase();
  if (!FD || !RHSList || isa<CXXThisExpr>(Base->IgnoreParenImpCasts()) ||
      !isFieldOfBaseRecord(ME))
    return;
  OriginList *Object = getPersistentValueOrigins(Base);
  if (Object && ME->isArrow())
    Object = Object->peelOuterOrigin();
  if (Object)
    flowFieldParamSlots(FD, RHSList, Object, /*IntoField=*/false);
}

void FactsGenerator::VisitMemberExpr(const MemberExpr *ME) {
  auto *MD = ME->getMemberDecl();
  if (const auto *VD = dyn_cast<VarDecl>(MD); VD && doesDeclHaveStorage(VD)) {
    // A static data member: borrow its storage, as for a DeclRefExpr.
    const Loan *L = createLoan(FactMgr, *VD, ME);
    OriginList *List = getOriginsList(*ME);
    assert(List && "gl-value static member should have an origin list");
    CurrentBlockFacts.push_back(
        FactMgr.createFact<IssueFact>(L->getID(), List->getOuterOriginID()));
    return;
  }
  auto *FD = dyn_cast<FieldDecl>(MD);
  if (!FD)
    return;

  OriginList *Dst = getOriginsList(*ME);
  const Expr *Base = ME->getBase();
  OriginList *Src = getOriginsList(*Base);

  if (doesDeclHaveStorage(FD)) {
    assert(ME->isGLValue() && "Field member should be GL value");
    assert(Dst && "Field member should have an origin list as it is GL value");
    assert(Src && "Base expression should be a pointer/reference type");
    // The field's glvalue (outermost origin) holds the same loans as the base
    // expression.
    CurrentBlockFacts.push_back(FactMgr.createFact<OriginFlowFact>(
        Dst->getOuterOriginID(), Src->getOuterOriginID(),
        /*Kill=*/true));
  }

  // When accessing a field on a record with LIFETIME_PARAMS (other than through
  // `this`, whose fields share origins with the FieldDecl and receive their
  // named placeholder loans at function entry), substitute the base object's
  // lifetime-parameter origins into the field's corresponding annotated slots.
  if (!isa<CXXThisExpr>(Base->IgnoreParenImpCasts()) && Dst && Src &&
      isFieldOfBaseRecord(ME)) {
    OriginList *BaseParams =
        ME->isArrow() || Base->isGLValue() ? Src->peelOuterOrigin() : Src;
    OriginList *FieldValue =
        doesDeclHaveStorage(FD) ? Dst->peelOuterOrigin() : Dst;
    flowFieldParamSlots(FD, FieldValue, BaseParams, /*IntoField=*/true);
  }
}

void FactsGenerator::VisitCallExpr(const CallExpr *CE) {
  handleFunctionCall(CE);
}

void FactsGenerator::VisitCXXNullPtrLiteralExpr(
    const CXXNullPtrLiteralExpr *N) {
  /// TODO: Handle nullptr expr as a special 'null' loan. Uninitialized
  /// pointers can use the same type of loan.
  getOriginsList(*N);
}

void FactsGenerator::VisitCastExpr(const CastExpr *CE) {
  const Expr *SubExpr = CE->getSubExpr();
  // May be null: loading an `int` has no origins but still reads the operand.
  OriginList *Dest = getOriginsList(*CE);
  OriginList *Src = Dest ? getOriginsList(*SubExpr) : nullptr;

  switch (CE->getCastKind()) {
  case CK_LValueToRValue:
    // The result of an LValue-to-RValue cast on a pointer lvalue (like `q` in
    // `int *p, *q; p = q;`) should propagate the inner origin (what the pointer
    // points to), not the outer origin (the pointer's storage location).
    flow(Dest, readValue(SubExpr), /*Kill=*/true);
    return;
  case CK_Dynamic:
    handleAccess(SubExpr);
    return;
  case CK_NullToPointer:
    // TODO: Flow into them a null origin.
    return;
  case CK_NoOp:
  case CK_ConstructorConversion:
  case CK_UserDefinedConversion:
    flow(Dest, Src, /*Kill=*/true);
    return;
  case CK_UncheckedDerivedToBase:
  case CK_DerivedToBase:
  case CK_BaseToDerived:
    // The conversion cast doesn't change what it refers to, so preserve the
    // borrow if we can.
    // It is possible that the derived class and base class have different
    // gsl::Pointer annotations. Skip if their origin shape differ.
    if (Dest && Src && Dest->getLength() == Src->getLength())
      flow(Dest, Src, /*Kill=*/true);
    return;
  case CK_ArrayToPointerDecay:
    // va_arg(ap, array_type) is UB and does not provide addressable array
    // storage to model.
    if (!Dest || isa<VAArgExpr>(SubExpr->IgnoreParens()))
      return;
    assert(Src && "Array expression should have origins as it is GL value");
    CurrentBlockFacts.push_back(FactMgr.createFact<OriginFlowFact>(
        Dest->getOuterOriginID(), Src->getOuterOriginID(), /*Kill=*/true));
    return;
  case CK_FunctionToPointerDecay:
  case CK_BuiltinFnToFnPtr:
    // Ignore function-to-pointer decays.
    return;
  case CK_BitCast:
    // OriginLists for Src and Dst may differ here. For example when casting
    // from int** to void*
    if (Src && Dest && Dest->getLength() == Src->getLength())
      flow(Dest, Src, /*Kill=*/true);
    return;
  case CK_LValueToRValueBitCast:
  case CK_NonAtomicToAtomic:
  case CK_AtomicToNonAtomic: {
    // `__builtin_bit_cast`/`std::bit_cast` of a pointer, and
    // wrapping/unwrapping `_Atomic(T*)`, preserve the pointer value, so
    // propagate the borrow. readValue peels a glvalue operand's storage level
    // and records the read. A bit-cast that materializes a pointer from a
    // non-pointer representation has no matching source origin and is
    // untracked.
    OriginList *RVSrc = readValue(SubExpr);
    if (Dest && RVSrc && Dest->getLength() == RVSrc->getLength())
      flow(Dest, RVSrc, /*Kill=*/true);
    return;
  }
  default:
    return;
  }
}

void FactsGenerator::VisitUnaryOperator(const UnaryOperator *UO) {
  switch (UO->getOpcode()) {
  case UO_AddrOf: {
    const Expr *SubExpr = UO->getSubExpr();
    // Function addresses do not need lifetime tracking.
    if (SubExpr->getType()->isFunctionType())
      return;
    // Skip address-of on void expressions: GNU C permits them, but void itself
    // has no origins to track.
    if (IsCMode && SubExpr->getType()->isVoidType())
      return;
    assert(!SubExpr->getType()->isVoidType() &&
           "Taking address of void is not valid in C++");
    // The origin of an address-of expression (e.g., &x) is the origin of
    // its sub-expression (x). This fact will cause the dataflow analysis
    // to propagate any loans held by the sub-expression's origin to the
    // origin of this UnaryOperator expression.
    killAndFlowOrigin(*UO, *SubExpr);
    return;
  }
  case UO_Deref: {
    const Expr *SubExpr = UO->getSubExpr();
    killAndFlowOrigin(*UO, *SubExpr);
    return;
  }
  case UO_Plus: {
    // Unary plus on a pointer is the identity (`+p == p`), so the prvalue
    // result carries the operand's loans. Flow the operand's rvalue origins
    // (peeling storage only when the operand is itself a glvalue).
    if (!UO->getType()->isPointerType())
      return;
    const Expr *SubExpr = UO->getSubExpr();
    flow(getOriginsList(*UO), readValue(SubExpr), /*Kill=*/true);
    return;
  }
  case UO_PreInc:
  case UO_PostInc:
  case UO_PreDec:
  case UO_PostDec: {
    handleAccess(UO->getSubExpr());
    // Inc/dec keeps a pointer in the same allocation, so the result carries the
    // operand's loans. Peel the operand's storage origin when the *result* is a
    // prvalue (post-inc/dec, or any form in C).
    if (!UO->getType()->isPointerType())
      return;
    OriginList *SubList = getOriginsList(*UO->getSubExpr());
    flow(getOriginsList(*UO),
         UO->isGLValue() ? SubList : SubList->peelOuterOrigin(), /*Kill=*/true);
    return;
  }
  default:
    return;
  }
}

void FactsGenerator::VisitReturnStmt(const ReturnStmt *RS) {
  if (const Expr *RetExpr = RS->getRetValue()) {
    if (OriginList *List = getOriginsList(*RetExpr))
      for (OriginList *L = List; L != nullptr; L = L->peelOuterOrigin())
        EscapesInCurrentBlock.push_back(FactMgr.createFact<ReturnEscapeFact>(
            L->getOuterOriginID(), RetExpr));
  }
}

void FactsGenerator::handleAssignment(const Expr *TargetExpr,
                                      const Expr *LHSExpr,
                                      const Expr *RHSExpr) {
  LHSExpr = ignoreParensAndImpCasts(LHSExpr);
  handleAccess(LHSExpr);
  OriginList *RHSList = readValue(RHSExpr);
  OriginList *LHSList = nullptr;

  // The origins of the object written through `*p`, which outlives the
  // expression: the store must land there for later reads of `*p` to see it.
  OriginList *PersistentTarget = nullptr;
  if (const auto *DRE_LHS = dyn_cast<DeclRefExpr>(LHSExpr)) {
    LHSList = getOriginsList(*DRE_LHS);
    assert(LHSList && "LHS is a DRE and should have an origin list");
  }
  // Handle assignment to member fields (e.g., `this->view = s` or `view = s`).
  // This enables detection of dangling fields when local values escape to
  // fields.
  if (const auto *ME_LHS = dyn_cast<MemberExpr>(LHSExpr)) {
    LHSList = getOriginsList(*ME_LHS);
    assert(LHSList && "LHS is a MemberExpr and should have an origin list");
    writeBackFieldStore(ME_LHS, RHSList);
  }
  if (const auto *UO_LHS = dyn_cast<UnaryOperator>(LHSExpr);
      UO_LHS && UO_LHS->getOpcode() == UO_Deref) {
    LHSList = getOriginsList(*UO_LHS);
    PersistentTarget = getPersistentValueOrigins(UO_LHS);
  }
  if (!LHSList)
    return;

  if (!RHSList) {
    // RHS has no tracked origins (e.g., assigning a callable without origins
    // to std::function). Clear loans of the destination.
    for (OriginList *LHSInner = LHSList->peelOuterOrigin(); LHSInner;
         LHSInner = LHSInner->peelOuterOrigin())
      CurrentBlockFacts.push_back(
          FactMgr.createFact<KillOriginFact>(LHSInner->getOuterOriginID()));
    for (OriginList *Target = PersistentTarget; Target;
         Target = Target->peelOuterOrigin())
      CurrentBlockFacts.push_back(
          FactMgr.createFact<KillOriginFact>(Target->getOuterOriginID()));
    return;
  }
  // Kill the old loans of the destination origin and flow the new loans
  // from the source origin.
  flow(LHSList->peelOuterOrigin(), RHSList, /*Kill=*/true);
  if (PersistentTarget)
    flow(PersistentTarget, RHSList, /*Kill=*/true);

  // In C, assignment expressions are not GLValues, so the assignment result has
  // the assigned value origins, not the LHS storage origin.
  if (IsCMode)
    LHSList = LHSList->peelOuterOrigin();
  flow(getOriginsList(*TargetExpr), LHSList, /*Kill=*/true);
}

void FactsGenerator::handlePointerArithmetic(const BinaryOperator *BO) {
  if (Expr *RHS = BO->getRHS(); RHS->getType()->isPointerType()) {
    killAndFlowOrigin(*BO, *RHS);
    return;
  }
  Expr *LHS = BO->getLHS();
  assert(LHS->getType()->isPointerType() &&
         "Pointer arithmetic must have a pointer operand");
  killAndFlowOrigin(*BO, *LHS);
}

void FactsGenerator::VisitBinaryOperator(const BinaryOperator *BO) {
  if (BO->getOpcode() == BO_PtrMemD || BO->getOpcode() == BO_PtrMemI) {
    // `obj.*pm` / `objptr->*pm` names a member of the object, so a borrow of it
    // borrows the object; flow the object's origin into the result. For `.*`
    // the object is the LHS; for `->*` it is the LHS pointer's pointee.
    //
    // Only the result's outer (storage) origin relates to the object: borrowing
    // the member borrows the object's storage. Deeper levels of the result (a
    // pointer/view member's own pointee) are the member's value, with no
    // counterpart in the object's origin -- so the lists may differ in length
    // and we flow just the top level, leaving the member's value untouched.
    OriginList *Dst = getOriginsList(*BO);
    OriginList *ObjSrc = BO->getOpcode() == BO_PtrMemD
                             ? getOriginsList(*BO->getLHS())
                             : readValue(BO->getLHS());
    if (Dst && ObjSrc)
      CurrentBlockFacts.push_back(FactMgr.createFact<OriginFlowFact>(
          Dst->getOuterOriginID(), ObjSrc->getOuterOriginID(), /*Kill=*/true));
    return;
  }
  if (BO->getOpcode() == BO_Comma) {
    killAndFlowOrigin(*BO, *BO->getRHS());
    return;
  }
  if (BO->isCompoundAssignmentOp()) {
    handleAccess(BO->getLHS());
    // A pointer compound additive assignment (`p += n`) carries the LHS's loans
    // like inc/dec above; in C the result is a prvalue, so peel its outer
    // (storage) origin.
    if (BO->getType()->isPointerType()) {
      OriginList *LHSList = getOriginsList(*BO->getLHS());
      flow(getOriginsList(*BO), IsCMode ? LHSList->peelOuterOrigin() : LHSList,
           /*Kill=*/true);
    }
    return;
  }
  if (BO->getType()->isPointerType() && BO->isAdditiveOp())
    handlePointerArithmetic(BO);
  if (BO->isAssignmentOp())
    handleAssignment(BO, BO->getLHS(), BO->getRHS());
  // TODO: Propagate origins for assignments through a dereference (`*p = q`).
}

static const CFGBlock *findPredBlockForExpr(const CFGBlock *MergeBlock,
                                            const Expr *ArmExpr) {
  if (!ArmExpr)
    return nullptr;
  const Expr *Target = ignoreParensAndImpCasts(ArmExpr);
  if (const auto *OVE = dyn_cast<OpaqueValueExpr>(Target))
    if (const Expr *Src = OVE->getSourceExpr())
      Target = ignoreParensAndImpCasts(Src);

  for (const CFGBlock *Pred : MergeBlock->preds()) {
    if (!Pred)
      continue;
    for (const CFGElement &Elt : *Pred)
      if (auto CS = Elt.getAs<CFGStmt>())
        if (const auto *E = dyn_cast<Expr>(CS->getStmt()))
          if (ignoreParensAndImpCasts(E) == Target)
            return Pred;
  }
  return nullptr;
}

/// Visits conditional operators (e.g., `cond ? a : b`).
///
/// To prevent liveness leakage across loop backedges (which causes false
/// positives like in `while (...) { int x; consume(cond ? &x : nullptr); }`),
/// we generate the flow facts in the respective predecessor blocks of the arms
/// rather than in the merge block. This ensures that the liveness of the
/// temporary origin from one arm does not propagate into the other arm's path.
void FactsGenerator::VisitAbstractConditionalOperator(
    const AbstractConditionalOperator *CO) {
  if (!hasOrigins(CO))
    return;

  const Expr *TrueExpr = CO->getTrueExpr();
  const Expr *FalseExpr = CO->getFalseExpr();

  if (const CFGBlock *TBPred = findPredBlockForExpr(CurrentBlock, TrueExpr))
    flow(getOriginsList(*CO), getOriginsList(*TrueExpr), /*Kill=*/true, TBPred);
  if (const CFGBlock *FBPred = findPredBlockForExpr(CurrentBlock, FalseExpr))
    flow(getOriginsList(*CO), getOriginsList(*FalseExpr), /*Kill=*/true,
         FBPred);
}

void FactsGenerator::VisitCXXOperatorCallExpr(const CXXOperatorCallExpr *OCE) {
  // Assignment operators have special "kill-then-propagate" semantics
  // and are handled separately.
  if (OCE->getOperator() == OO_Equal && OCE->getNumArgs() == 2 &&
      hasOrigins(OCE->getArg(0)->getType())) {
    // Pointer-like types: assignment inherently propagates origins.
    QualType LHSTy = OCE->getArg(0)->getType();
    if (LHSTy->isPointerOrReferenceType() || isGslPointerType(LHSTy) ||
        isGslOwnerType(LHSTy)) {
      handleAssignment(OCE, OCE->getArg(0), OCE->getArg(1));
      return;
    }
    // Standard library callable wrappers (e.g., std::function) can propagate
    // the stored lambda's origins.
    if (const auto *RD = LHSTy->getAsCXXRecordDecl();
        RD && isStdCallableWrapperType(RD)) {
      handleAssignment(OCE, OCE->getArg(0), OCE->getArg(1));
      return;
    }
    // Other tracked types: only defaulted operator= propagates origins.
    // User-defined operator= has opaque semantics, so don't handle them now,
    // except for copy and move assignment of a record that declares lifetime
    // parameters: its type says the parameters are those of the source.
    if (const auto *MD =
            dyn_cast_or_null<CXXMethodDecl>(OCE->getDirectCallee());
        MD &&
        (MD->isDefaulted() ||
         ((MD->isCopyAssignmentOperator() || MD->isMoveAssignmentOperator()) &&
          !getDeclaredLifetimeParams(AC.getASTContext(), MD->getParent())
               .empty()))) {
      handleAssignment(OCE, OCE->getArg(0), OCE->getArg(1));
      return;
    }
  }

  handleFunctionCall(OCE);
}

void FactsGenerator::VisitCXXFunctionalCastExpr(
    const CXXFunctionalCastExpr *FCE) {
  // Check if this is a test point marker. If so, we are done with this
  // expression.
  if (handleTestPoint(FCE))
    return;
  VisitCastExpr(FCE);
}

void FactsGenerator::VisitInitListExpr(const InitListExpr *ILE) {
  if (!hasOrigins(ILE))
    return;
  if (const auto *RD = ILE->getType()->getAsCXXRecordDecl()) {
    if (const CXXRecordDecl *Def = RD->getDefinition()) {
      ASTContext &Ctx = AC.getASTContext();
      LifetimeList ClassParams = getDeclaredLifetimeParams(Ctx, Def);
      if (!ClassParams.empty()) {
        llvm::SmallDenseMap<llvm::StringRef, llvm::SmallVector<OriginID, 2>, 4>
            ByLifetime;
        // Pair each field with its initializer. In aggregate initialization,
        // initializers for direct base classes come first, followed by one
        // initializer per named field; a union has a single initializer for
        // its active member. Base class parameters are not propagated through
        // the derived type, so base initializers are skipped.
        llvm::SmallVector<std::pair<const FieldDecl *, const Expr *>, 4>
            FieldInits;
        if (Def->isUnion()) {
          if (const FieldDecl *Active = ILE->getInitializedFieldInUnion();
              Active && ILE->getNumInits() == 1)
            FieldInits.push_back({Active, ILE->getInit(0)});
        } else {
          unsigned InitIdx = Def->getNumBases();
          for (const FieldDecl *Field : Def->fields()) {
            if (Field->isUnnamedBitField())
              continue;
            if (InitIdx >= ILE->getNumInits())
              break;
            FieldInits.push_back({Field, ILE->getInit(InitIdx++)});
          }
        }
        for (auto [Field, Init] : FieldInits) {
          if (!Init)
            continue;
          LifetimeList FieldLifetimes =
              getExplicitLifetimes(Ctx, Field->getType());
          if (FieldLifetimes.empty())
            continue;
          OriginList *InitList = getOriginsList(*Init);
          for (const LifetimeVar &LV : FieldLifetimes) {
            if (!InitList)
              break;
            if (LV.getKind() == LifetimeVar::Kind::Named)
              ByLifetime[LV.getName()].push_back(InitList->getOuterOriginID());
            InitList = InitList->peelOuterOrigin();
          }
        }
        OriginList *ResultLevel = getOriginsList(*ILE);
        for (const LifetimeVar &Param : ClassParams) {
          if (!ResultLevel)
            break;
          bool KillSrc = true;
          for (OriginID Src : ByLifetime.lookup(Param.getName())) {
            CurrentBlockFacts.push_back(FactMgr.createFact<OriginFlowFact>(
                ResultLevel->getOuterOriginID(), Src, KillSrc));
            KillSrc = false;
          }
          ResultLevel = ResultLevel->peelOuterOrigin();
        }
        // The generic single-element handling below must not run as well: it
        // would flow the first initializer's origins into the first slot
        // regardless of which lifetime that field actually names.
        return;
      }
    }
  }
  // For list initialization with a single element, like `View{...}`, the
  // origin of the list itself is the origin of its single element.
  if (ILE->getNumInits() == 1) {
    // A type with origins may be list-initialized from an element with none
    // (e.g., an int). Only flow if the element carries any.
    if (!hasOrigins(ILE->getInit(0)))
      return;
    killAndFlowOrigin(*ILE, *ILE->getInit(0));
  }
}

void FactsGenerator::VisitCXXBindTemporaryExpr(
    const CXXBindTemporaryExpr *BTE) {
  killAndFlowOrigin(*BTE, *BTE->getSubExpr());
}

void FactsGenerator::VisitMaterializeTemporaryExpr(
    const MaterializeTemporaryExpr *MTE) {
  assert(MTE->isGLValue());
  OriginList *MTEList = getOriginsList(*MTE);
  if (!MTEList)
    return;
  OriginList *SubExprList = getOriginsList(*MTE->getSubExpr());
  assert((!SubExprList ||
          MTEList->getLength() == (SubExprList->getLength() + 1)) &&
         "MTE top level origin should contain a loan to the MTE itself");

  OriginList *RValMTEList = MTEList->peelOuterOrigin();
  flow(RValMTEList, SubExprList, /*Kill=*/true);
  OriginID OuterMTEID = MTEList->getOuterOriginID();
  const Loan *L = createLoan(FactMgr, MTE);
  CurrentBlockFacts.push_back(
      FactMgr.createFact<IssueFact>(L->getID(), OuterMTEID));
  // A temporary extended to static or thread storage duration does not expire
  // within the function.
  // Thread termination is not modeled; a thread-local value used after its
  // thread exits is not diagnosed.
  if (MTE->getStorageDuration() == SD_Automatic)
    if (const ValueDecl *ExtendingDecl = MTE->getExtendingDecl())
      ExtendedTemporaries[ExtendingDecl].push_back(MTE);
}

void FactsGenerator::VisitLambdaExpr(const LambdaExpr *LE) {
  for (const LambdaCapture &C : LE->captures()) {
    if (C.capturesThis())
      FactMgr.setThisCapturedByLambda();
    else if (C.capturesVariable() && C.getCapturedVar()->isInitCapture()) {
      const Expr *Init = cast<VarDecl>(C.getCapturedVar())->getInit();
      if (!Init)
        continue;
      if (const auto *ME =
              dyn_cast<MemberExpr>(ignoreParensAndImpCasts(Init))) {
        if (const auto *FD = dyn_cast<FieldDecl>(ME->getMemberDecl()))
          FactMgr.addCapturedField(FD);
      }
    }
  }

  // The lambda gets a single merged origin that aggregates all captured
  // pointer-like origins. Currently we only need to detect whether the lambda
  // outlives any capture.
  OriginList *LambdaList = getOriginsList(*LE);
  if (!LambdaList)
    return;
  bool Kill = true;
  for (const Expr *Init : LE->capture_inits()) {
    if (!Init)
      continue;
    // The lambda body may dereference a capture to any depth.
    handleUse(Init);
    OriginList *InitList = getOriginsList(*Init);
    if (!InitList)
      continue;
    // FIXME: Consider flowing all origin levels once lambdas support more than
    // one origin. Currently only the outermost origin is flowed, so by-ref
    // captures like `[&p]` (where p is string_view) miss inner-level
    // invalidation.
    CurrentBlockFacts.push_back(FactMgr.createFact<OriginFlowFact>(
        LambdaList->getOuterOriginID(), InitList->getOuterOriginID(), Kill));
    Kill = false;
  }
}

void FactsGenerator::VisitArraySubscriptExpr(const ArraySubscriptExpr *ASE) {
  // Some C subscripts do not refer to addressable storage with origins, such as
  // GNU void-pointer subscripts and vector element extraction from rvalues.
  if (IsCMode && !ASE->isGLValue())
    return;
  assert(ASE->isGLValue() && "Array subscript should be a GL value");
  OriginList *Dst = getOriginsList(*ASE);
  assert(Dst && "Array subscript should have origins as it is a GL value");
  OriginList *Src = getOriginsList(*ASE->getBase());
  assert(Src && "Base of array subscript should have origins");
  CurrentBlockFacts.push_back(FactMgr.createFact<OriginFlowFact>(
      Dst->getOuterOriginID(), Src->getOuterOriginID(), /*Kill=*/true));
}

bool FactsGenerator::handlePlacementNew(const CXXNewExpr *NE,
                                        OriginList *NewList) {
  // Model only the standard single-argument placement new form, where the
  // placement argument corresponds to a void* allocation-function parameter.
  // Other placement forms, such as std::nothrow, are not modeled as providing
  // storage for the returned pointer.
  if (NE->getNumPlacementArgs() != 1)
    return false;

  const FunctionDecl *OperatorNew = NE->getOperatorNew();
  if (OperatorNew->getNumParams() <= 1)
    return false;

  const auto *Arg =
      OperatorNew->getParamDecl(1)->getType()->getAs<PointerType>();
  if (!Arg || !Arg->isVoidPointerType())
    return false;

  // Use the placement argument before the implicit conversion to void*, so
  // inner origins are still available.
  const Expr *PlacementArg = NE->getPlacementArg(0);
  if (const auto *ICE = dyn_cast<ImplicitCastExpr>(PlacementArg);
      ICE && ICE->getCastKind() == CK_BitCast &&
      PlacementArg->getType()->isVoidPointerType())
    PlacementArg = ICE->getSubExpr();
  OriginList *PlacementList = getOriginsList(*PlacementArg);
  // FIXME: General placement arguments need separate handling to overwrite
  // the right origins.

  handleAccess(PlacementArg);

  // The pointer returned by placement new comes from the placement
  // argument.
  if (PlacementList)
    CurrentBlockFacts.push_back(FactMgr.createFact<OriginFlowFact>(
        NewList->getOuterOriginID(), PlacementList->getOuterOriginID(), true));
  return true;
}

void FactsGenerator::VisitCXXNewExpr(const CXXNewExpr *NE) {
  OriginList *NewList = getOriginsList(*NE);
  const Expr *Init = NE->getInitializer();

  bool HandledAsPlacementNew = false;
  if (NE->getNumPlacementArgs() == 1)
    HandledAsPlacementNew = handlePlacementNew(NE, NewList);

  // Treat ordinary new and replaceable global allocation forms as heap
  // allocations.
  const FunctionDecl *OperatorNew = NE->getOperatorNew();
  if (!HandledAsPlacementNew &&
      (NE->getNumPlacementArgs() == 0 ||
       (OperatorNew && OperatorNew->isReplaceableGlobalAllocationFunction()))) {
    const Loan *L = createLoan(FactMgr, NE);
    CurrentBlockFacts.push_back(
        FactMgr.createFact<IssueFact>(L->getID(), NewList->getOuterOriginID()));
  }

  NewList = NewList->peelOuterOrigin();

  if (!NewList || !Init)
    return;

  // FIXME: OriginList is null for `new[]` initializers. Remove this `Init`
  // check once array origins are supported.
  if (OriginList *InitList = getOriginsList(*Init); InitList)
    flow(NewList, InitList, true);
}

// TODO: An escape fact may fit `throw` and asm better than a use.
void FactsGenerator::VisitCXXThrowExpr(const CXXThrowExpr *TE) {
  if (const Expr *Sub = TE->getSubExpr())
    handleUse(Sub);
}

void FactsGenerator::VisitGCCAsmStmt(const GCCAsmStmt *AS) {
  for (const Expr *Input : AS->inputs())
    handleUse(Input);
  for (unsigned I = 0, N = AS->getNumOutputs(); I != N; ++I)
    if (AS->isOutputPlusConstraint(I)) // Also read.
      handleUse(AS->getOutputExpr(I));
    else
      handleAccess(AS->getOutputExpr(I));
}

void FactsGenerator::VisitCXXTypeidExpr(const CXXTypeidExpr *TE) {
  if (TE->isPotentiallyEvaluated())
    handleAccess(TE->getExprOperand());
}

void FactsGenerator::VisitCXXDeleteExpr(const CXXDeleteExpr *DE) {
  // The destructor may dereference to any depth.
  handleUse(DE->getArgument());
  OriginList *List = getOriginsList(*DE->getArgument());
  CurrentBlockFacts.push_back(
      FactMgr.createFact<InvalidateOriginFact>(List->getOuterOriginID(), DE));
}

void FactsGenerator::VisitStmtExpr(const StmtExpr *SE) {
  // A statement expression (`({ ...; e; })`) yields the value of its final
  // expression `e`. Flow `e`'s origins into the statement expression's origin
  // so a borrow `e` carries reaches the value's users.
  const auto *CS = SE->getSubStmt();
  if (!CS || CS->body_empty())
    return;
  const auto *Last = dyn_cast<Expr>(CS->body_back());
  if (!Last)
    return;
  if (OriginList *Dst = getOriginsList(*SE))
    if (OriginList *Src = readValue(Last))
      flow(Dst, Src, /*Kill=*/true);
}

bool FactsGenerator::escapesViaReturn(OriginID OID) const {
  return llvm::any_of(EscapesInCurrentBlock, [OID](const Fact *F) {
    if (const auto *EF = F->getAs<ReturnEscapeFact>())
      return EF->getEscapedOriginID() == OID;
    return false;
  });
}

void FactsGenerator::handleLifetimeEnds(const CFGLifetimeEnds &LifetimeEnds) {
  const VarDecl *LifetimeEndsVD = LifetimeEnds.getVarDecl();
  if (!LifetimeEndsVD)
    return;
  SourceLocation EndLoc = LifetimeEnds.getTriggerStmt()->getEndLoc();
  // A cleanup callback or a non-trivial destructor (other than an owner's) run
  // at scope exit may read the borrows the variable holds.
  QualType Ty = LifetimeEndsVD->getType();
  bool HasCleanup = LifetimeEndsVD->hasAttr<CleanupAttr>();
  bool IsDestructorUse =
      LSOpts.CheckDestructorUses &&
      Ty.isDestructedType() == QualType::DK_cxx_destructor &&
      !isGslOwnerType(AC.getASTContext().getBaseElementType(Ty));
  if (HasCleanup || IsDestructorUse)
    if (OriginList *List = getOriginsList(*LifetimeEndsVD))
      CurrentBlockFacts.push_back(FactMgr.createFact<UseFact>(
          UseSite::scopeExit(EndLoc, *LifetimeEndsVD,
                             HasCleanup ? UseKind::Cleanup
                                        : UseKind::Destructor),
          List));
  // Expire the origin when its variable's lifetime ends to ensure liveness
  // doesn't persist through loop back-edges.
  std::optional<OriginID> ExpiredOID;
  if (OriginList *List = getOriginsList(*LifetimeEndsVD)) {
    OriginID OID = List->getOuterOriginID();
    // Skip origins that escape via return; the escape checker needs their loans
    // to remain until the return statement is processed.
    if (!escapesViaReturn(OID))
      ExpiredOID = OID;
  }
  CurrentBlockFacts.push_back(FactMgr.createFact<ExpireFact>(
      AccessPath(LifetimeEndsVD), EndLoc, ExpiredOID));
  if (auto It = ExtendedTemporaries.find(LifetimeEndsVD);
      It != ExtendedTemporaries.end())
    for (const MaterializeTemporaryExpr *MTE : It->second)
      CurrentBlockFacts.push_back(
          FactMgr.createFact<ExpireFact>(AccessPath(MTE), EndLoc));
}

void FactsGenerator::handleFullExprCleanup(
    const CFGFullExprCleanup &FullExprCleanup) {
  for (const auto *MTE : FullExprCleanup.getExpiringMTEs())
    CurrentBlockFacts.push_back(FactMgr.createFact<ExpireFact>(
        AccessPath(MTE), FullExprCleanup.getCleanupLoc()));
}

void FactsGenerator::handleExitBlock() {
  bool IsDestructor = isa_and_nonnull<CXXDestructorDecl>(AC.getDecl());
  for (const Origin &O : FactMgr.getOriginMgr().getOrigins())
    // Create FieldEscapeFacts for all field origins that remain live at exit.
    // Fields in destructors do not escape since the object is being destroyed.
    if (auto *FD = dyn_cast_if_present<FieldDecl>(O.getDecl());
        FD && !IsDestructor)
      EscapesInCurrentBlock.push_back(
          FactMgr.createFact<FieldEscapeFact>(O.ID, FD));
    else if (auto *VD = dyn_cast_if_present<VarDecl>(O.getDecl())) {
      // Create GlobalEscapeFacts for all origins with global-storage that
      // remain live at exit.
      if (VD->hasGlobalStorage()) {
        EscapesInCurrentBlock.push_back(
            FactMgr.createFact<GlobalEscapeFact>(O.ID, VD));
      }
    }

  // Keep the never-expiring `this` origin live at exit: the object outlives
  // the method, so whatever it holds (e.g. borrows captured via
  // [[clang::lifetime_capture_by_this]], or loans reachable through its
  // fields) is considered used after the method returns. This is emitted for
  // every method with a `this` origin, not only those that capture something.
  // Destructors are skipped since the object is being destroyed.
  // Every level escapes: captures land in the object (`*this`), not in the
  // `this` pointer.
  if (auto ThisOrigins = FactMgr.getOriginMgr().getThisOrigins();
      ThisOrigins && !IsDestructor)
    for (OriginList *L = *ThisOrigins; L; L = L->peelOuterOrigin())
      EscapesInCurrentBlock.push_back(FactMgr.createFact<ThisEscapeFact>(
          L->getOuterOriginID(), AC.getDecl()->getEndLoc()));
}

void FactsGenerator::handleGSLPointerConstruction(const CXXConstructExpr *CCE) {
  assert(isGslPointerType(CCE->getType()));
  // Only lifetimebound parameters propagate for a constructor taking several
  // arguments; the owner heuristic applies to single-argument construction.
  if (CCE->getNumArgs() != 1) {
    handleFunctionCall(CCE, /*IsGslConstruction=*/true);
    return;
  }

  const Expr *Arg = CCE->getArg(0);
  if (isGslPointerType(Arg->getType())) {
    // GSL pointer is constructed from another gsl pointer.
    // Example:
    //  View(View v);
    //  View(const View &v);
    OriginList *ArgList = readValue(Arg);
    assert(ArgList && "GSL pointer argument should have an origin list");
    flow(getOriginsList(*CCE), ArgList, /*Kill=*/true);
  } else if (Arg->getType()->isPointerType()) {
    // GSL pointer is constructed from a raw pointer. Flow only the outermost
    // raw pointer. Example:
    //  View(const char*);
    //  Span<int*>(const in**);
    OriginList *ArgList = getOriginsList(*Arg);
    CurrentBlockFacts.push_back(FactMgr.createFact<OriginFlowFact>(
        getOriginsList(*CCE)->getOuterOriginID(), ArgList->getOuterOriginID(),
        /*Kill=*/true));
  } else {
    // This could be a new borrow.
    // TODO: Add code example here.
    handleFunctionCall(CCE, /*IsGslConstruction=*/true);
  }
}

void FactsGenerator::handleMovedArgsInCall(const FunctionDecl *FD,
                                           ArrayRef<const Expr *> Args) {
  // std::unique_ptr::release() transfers ownership.
  // Treat it as a move to prevent false-positive warnings when the unique_ptr
  // destructor runs after ownership has been transferred.
  if (const auto *MD = dyn_cast<CXXMethodDecl>(FD);
      MD && hasImplicitObjectArg(*FD) && isUniquePtrRelease(*MD)) {
    const Expr *UniquePtrExpr = Args[0];
    OriginList *MovedOrigins = getOriginsList(*UniquePtrExpr);
    if (MovedOrigins)
      CurrentBlockFacts.push_back(FactMgr.createFact<MovedOriginFact>(
          UniquePtrExpr, MovedOrigins->getOuterOriginID()));
  }

  for (unsigned I = 0; I < Args.size(); ++I) {
    // Null for the implicit 'this' arg, which cannot be moved.
    const ParmVarDecl *PVD = getParamForArg(*FD, I);
    if (!PVD)
      continue;
    // In principle, explicit object parameters can be moved, but skip marking
    // them as moved for consistency with implicit 'this'.
    if (PVD->isExplicitObjectParameter())
      continue;
    if (!PVD->getType()->isRValueReferenceType())
      continue;
    // Skip lifetime annotated r-value reference parameters. Lifetime annotation
    // indicates that the parameter is borrowed (not consumed), so it should not
    // be marked as moved even though it's an r-value reference.
    if (PVD->hasAttr<LifetimeBoundAttr>() ||
        PVD->hasAttr<LifetimeCaptureByAttr>())
      continue;
    const Expr *Arg = Args[I];
    OriginList *MovedOrigins = getOriginsList(*Arg);
    assert(MovedOrigins->getLength() >= 1 &&
           "unexpected length for r-value reference param");
    // Arg is being moved to this parameter. Mark the origin as moved.
    CurrentBlockFacts.push_back(FactMgr.createFact<MovedOriginFact>(
        Arg, MovedOrigins->getOuterOriginID()));
  }
}

void FactsGenerator::handleInvalidatingCall(const Expr *Call,
                                            const FunctionDecl *FD,
                                            ArrayRef<const Expr *> Args) {
  const auto *MD = dyn_cast<CXXMethodDecl>(FD);
  if (!MD || !MD->isInstance())
    return;

  if (!isInvalidationMethod(*MD))
    return;

  // Heuristics to turn-down false positives. Skip member field expressions for
  // now. This is not a perfect filter and will still surface some false
  // positives (e.g. `auto& r = s.v`). Static data members are not fields.
  const Expr *Obj = ignoreParensAndImpCasts(Args[0]);
  if (const auto *ME = dyn_cast<MemberExpr>(Obj);
      !isa<DeclRefExpr>(Obj) && !(ME && isa<VarDecl>(ME->getMemberDecl())))
    return;

  OriginList *ThisList = getOriginsList(*Args[0]);
  if (ThisList)
    CurrentBlockFacts.push_back(FactMgr.createFact<InvalidateOriginFact>(
        ThisList->getOuterOriginID(), Call));
}

void FactsGenerator::handleDestructiveCall(const Expr *Call,
                                           const FunctionDecl *FD,
                                           ArrayRef<const Expr *> Args) {
  if (!destructsFirstArg(*FD))
    return;
  OriginList *ArgList = getOriginsList(*Args[0]);
  if (ArgList)
    CurrentBlockFacts.push_back(FactMgr.createFact<InvalidateOriginFact>(
        ArgList->getOuterOriginID(), Call));
}

void FactsGenerator::handleImplicitObjectFieldUses(const Expr *Call,
                                                   const FunctionDecl *FD) {
  const auto *MemberCall = dyn_cast_or_null<CXXMemberCallExpr>(Call);
  if (!MemberCall)
    return;

  if (!isa_and_present<CXXThisExpr>(
          ignoreParensAndImpCasts(MemberCall->getImplicitObjectArgument())))
    return;

  const auto *MD = dyn_cast<CXXMethodDecl>(FD);
  assert(MD && "Function must be a CXXMethodDecl for member calls");

  const auto *ClassDecl = MD->getParent()->getDefinition();
  if (!ClassDecl)
    return;

  const auto UseFields = [&](const CXXRecordDecl *RD) {
    for (const auto *Field : RD->fields())
      if (auto *FieldList = getOriginsList(*Field))
        CurrentBlockFacts.push_back(
            FactMgr.createFact<UseFact>(*Call, FieldList));
  };

  UseFields(ClassDecl);

  ClassDecl->forallBases([&](const CXXRecordDecl *Base) {
    UseFields(Base);
    return true;
  });
}

void FactsGenerator::handleLifetimeCaptureBy(const FunctionDecl *FD,
                                             ArrayRef<const Expr *> Args) {
  if (Args.empty())
    return;
  // FIXME: Add support for capture_by on constructors.
  if (isa<CXXConstructorDecl>(FD))
    return;
  auto getArgCaptureByAttr =
      [FD](unsigned I) -> std::pair<const LifetimeCaptureByAttr *, QualType> {
    if (I == 0 && hasImplicitObjectArg(*FD))
      return {getCaptureByAttrFromFunctionType(FD),
              cast<CXXMethodDecl>(FD)->getFunctionObjectParameterType()};
    if (const ParmVarDecl *PVD = getParamForArg(*FD, I))
      return {PVD->getAttr<LifetimeCaptureByAttr>(), PVD->getType()};
    return {nullptr, QualType()};
  };
  for (unsigned I = 0; I < Args.size(); ++I) {
    auto [Attr, ParamType] = getArgCaptureByAttr(I);
    if (!Attr)
      continue;
    OriginList *CapturedOriginList = getOriginsList(*Args[I]);
    if (!CapturedOriginList)
      continue;
    // For references to pointer-like types, peel the outer origin (the pointer
    // object itself) so that we capture the underlying data (the inner origin).
    if (!ParamType.isNull() &&
        (ParamType->isReferenceType() &&
         isPointerLikeType(ParamType->getPointeeType())) &&
        CapturedOriginList->getLength() > 1)
      CapturedOriginList = CapturedOriginList->peelOuterOrigin();
    for (int CapturingArgIdx : Attr->params()) {
      // FIXME: Add support for capturing to Global/unknown.
      if (CapturingArgIdx == LifetimeCaptureByAttr::Global ||
          CapturingArgIdx == LifetimeCaptureByAttr::Unknown ||
          CapturingArgIdx == LifetimeCaptureByAttr::Invalid)
        continue;
      // FIXME: Diagnose bad CapturingArgIdx.
      if (CapturingArgIdx != LifetimeCaptureByAttr::This &&
          (CapturingArgIdx < 0 ||
           static_cast<size_t>(CapturingArgIdx) >= Args.size()))
        continue;
      const Expr *CapturedByArg = Args[CapturingArgIdx];
      assert(CapturedByArg && "Capturer expression must be valid");

      OriginList *Dest = readValue(CapturedByArg);
      if (!Dest)
        continue;
      // A pointer capturer (`this`, or a `T*` argument) refers to its pointee:
      // the capture is stored in the pointed-to object, not in the pointer.
      // A glvalue capturer has already been read down to the object's value.
      if (CapturedByArg->isPRValue() &&
          CapturedByArg->getType()->isPointerType())
        if (OriginList *Pointee = Dest->peelOuterOrigin())
          Dest = Pointee;
      // KillDest=false because we cannot know if previous captures are being
      // replaced or accumulated. Multiple successive captures into the same
      // destination must all be tracked, so captured lifetimes are always
      // merged.
      CurrentBlockFacts.push_back(FactMgr.createFact<OriginFlowFact>(
          Dest->getOuterOriginID(), CapturedOriginList->getOuterOriginID(),
          /*KillDest=*/false));
    }
  }
}

namespace {
/// What the signature says about one argument of a call.
struct ArgLifetimeInfo {
  /// The lifetimes written for this argument, or null if it writes none.
  const LifetimeList *Lifetimes = nullptr;
  /// The parameter the argument binds to, or null for the implicit object
  /// argument, which has no `ParmVarDecl`.
  const ParmVarDecl *Param = nullptr;
};
} // namespace

/// Returns what the signature says about argument \p I.
///
/// For instance methods (other than constructors) `Args[0]` is the implicit
/// object argument. Its lifetimes are written after the parameter list, which
/// is where `LifetimeSignature` records them as `FunctionType`.
static ArgLifetimeInfo getLifetimesForArg(const FunctionDecl *FD,
                                          const LifetimeSignature &Sig,
                                          unsigned I) {
  if (const auto *Method = dyn_cast<CXXMethodDecl>(FD);
      Method && Method->isInstance() && !isa<CXXConstructorDecl>(FD)) {
    if (I == 0)
      return {&Sig.FunctionType, /*Param=*/nullptr};
    --I;
  }
  if (I >= Sig.Params.size())
    return {};
  return {&Sig.Params[I],
          I < FD->getNumParams() ? FD->getParamDecl(I) : nullptr};
}

bool FactsGenerator::handleNamedLifetimeCall(const FunctionDecl *FD,
                                             llvm::ArrayRef<const Expr *> Args,
                                             OriginList *CallList) {
  LifetimeSignature Sig = getLifetimeSignature(AC.getASTContext(), FD);
  if (Sig.empty())
    return false;

  // Walk the arguments once, collecting the origins written with each named
  // lifetime and recording the obligations `$static` positions impose.
  llvm::SmallDenseMap<llvm::StringRef, llvm::SmallVector<OriginID, 2>, 4>
      ByLifetime;
  for (unsigned I = 0; I < Args.size(); ++I) {
    auto [Lifetimes, Param] = getLifetimesForArg(FD, Sig, I);
    if (!Lifetimes || Lifetimes->empty())
      continue;
    OriginList *ArgList = getOriginsList(*Args[I]);
    if (!ArgList)
      continue;
    // The lifetime list and the origin list are both ordered outermost-first.
    // Shapes can still disagree (for example when an lvalue argument carries
    // an extra synthetic level), so stop at whichever runs out rather than
    // asserting; the cost of a mismatch is a missed flow, not a wrong one.
    for (const LifetimeVar &LV : *Lifetimes) {
      if (!ArgList)
        break;
      switch (LV.getKind()) {
      case LifetimeVar::Kind::Named:
        ByLifetime[LV.getName()].push_back(ArgList->getOuterOriginID());
        break;
      case LifetimeVar::Kind::Static:
        // Unlike a named lifetime, which the caller instantiates with whatever
        // it has, `$static` is a fixed demand: the argument must be storage
        // that never expires. That is a check, not a flow.
        CurrentBlockFacts.push_back(FactMgr.createFact<StaticObligationFact>(
            ArgList->getOuterOriginID(), Args[I], Param));
        break;
      case LifetimeVar::Kind::Unknown:
      case LifetimeVar::Kind::Elided:
        break;
      }
      ArgList = ArgList->peelOuterOrigin();
    }
  }

  if (!CallList)
    return false;

  // Substitution only governs the result, so it only applies when the return
  // position actually says something. A signature that annotates parameters
  // but leaves the return bare says nothing about what the call yields; in
  // that case `lifetimebound` remains the best available information and the
  // existing path is left alone.
  if (llvm::all_of(Sig.Return, [](const LifetimeVar &LV) {
        return LV.getKind() == LifetimeVar::Kind::Elided;
      }))
    return false;

  // Flow the collected origins into each result level naming that lifetime.
  // A `$static` or `$unknown` level contributes nothing: the first cannot
  // dangle, and the second is an explicit assertion that no lifetime applies.
  // Both therefore leave the result with an empty loan set, which is also what
  // suppresses the `lifetimebound` union for an `$unknown` return.
  //
  // A level named with the lifetime of `this` also receives what the object
  // was built from. The callee may return a value borrowed from any of the
  // class's lifetimes under the lifetime of `this` (the implied bound in
  // `Checker.cpp`: an object cannot outlive its own lifetime parameters), so
  // the caller must treat such a result as borrowing from those lifetimes as
  // well as from the object. This holds whether the lifetime of `this` was
  // written or supplied by elision. It is Rust's rule: `&'t Holder<'a>` is
  // well formed only if `'a: 't`, which the borrow checker enforces at the
  // call.
  llvm::StringRef ThisLifetime;
  LifetimeList ClassLifetimes;
  if (const auto *MD = dyn_cast<CXXMethodDecl>(FD);
      MD && MD->isInstance() && !isa<CXXConstructorDecl>(MD) &&
      !Sig.FunctionType.empty() &&
      Sig.FunctionType.front().getKind() == LifetimeVar::Kind::Named) {
    ThisLifetime = Sig.FunctionType.front().getName();
    ClassLifetimes = getEnclosingClassLifetimeParams(AC.getASTContext(), FD);
  }
  auto SourcesFor = [&](llvm::StringRef Name) {
    auto Own = ByLifetime.lookup(Name);
    llvm::SmallVector<OriginID, 4> Sources(Own.begin(), Own.end());
    if (Name != ThisLifetime)
      return Sources;
    for (const LifetimeVar &Class : ClassLifetimes) {
      if (Class.getKind() != LifetimeVar::Kind::Named ||
          Class.getName() == Name)
        continue;
      for (OriginID Src : ByLifetime.lookup(Class.getName()))
        if (!llvm::is_contained(Sources, Src))
          Sources.push_back(Src);
    }
    return Sources;
  };
  OriginList *ResultLevel = CallList;
  for (const LifetimeVar &LV : Sig.Return) {
    if (!ResultLevel)
      break;
    if (LV.getKind() == LifetimeVar::Kind::Named) {
      // A lifetime that appears on the return but on no argument borrows from
      // nothing, so the result is left with an empty loan set.
      bool KillSrc = true;
      for (OriginID Src : SourcesFor(LV.getName())) {
        CurrentBlockFacts.push_back(FactMgr.createFact<OriginFlowFact>(
            ResultLevel->getOuterOriginID(), Src, KillSrc));
        KillSrc = false;
      }
    }
    ResultLevel = ResultLevel->peelOuterOrigin();
  }
  return true;
}

void FactsGenerator::handleFreeingCall(const Expr *Call, const FunctionDecl *FD,
                                       ArrayRef<const Expr *> Args) {
  if (!isFreeingFunction(*FD))
    return;
  auto InvalidateArg = [&](unsigned ArgIndex) {
    assert(ArgIndex < Args.size() && "Arg index should be in bounds");

    OriginList *ArgList = getOriginsList(*Args[ArgIndex]);
    if (!ArgList)
      return;
    CurrentBlockFacts.push_back(FactMgr.createFact<InvalidateOriginFact>(
        ArgList->getOuterOriginID(), Call));
  };

  bool HasOwnershipTakesAttr = false;
  for (const OwnershipAttr *Attr : FD->specific_attrs<OwnershipAttr>()) {
    if (Attr->getOwnKind() != OwnershipAttr::Takes)
      continue;
    HasOwnershipTakesAttr = true;
    for (const ParamIdx &Idx : Attr->args()) {
      // Attribute indices count implicit 'this', but constructor Args omits it:
      // the first explicit parameter (2) maps to Args[0], not Args[1].
      InvalidateArg(Idx.getLLVMIndex() - isa<CXXConstructorDecl>(FD));
    }
  }
  // Allocating/freeing builtins (e.g. `free`, `realloc`) free their first
  // argument.
  if (!HasOwnershipTakesAttr) {
    assert(!Args.empty() && "freeing builtins take at least one argument");
    InvalidateArg(0);
  }
}

void FactsGenerator::handleAllocatingCall(const Expr *Call,
                                          const FunctionDecl *FD) {
  if (!isAllocatingFunction(*FD))
    return;
  const auto *CE = dyn_cast<CallExpr>(Call);
  if (!CE)
    return;
  OriginList *CallList = getOriginsList(*Call);
  if (!CallList)
    return;
  const Loan *L = createNewAllocLoan(FactMgr, CE);
  CurrentBlockFacts.push_back(
      FactMgr.createFact<IssueFact>(L->getID(), CallList->getOuterOriginID()));
}

void FactsGenerator::handleFunctionCall(const Expr *Call,
                                        bool IsGslConstruction) {
  FunctionCallInfo CallInfo(Call);
  llvm::ArrayRef<const Expr *> Args = CallInfo.Args;
  // The callee may dereference any argument to any depth.
  for (const Expr *Arg : Args)
    handleUse(Arg);
  if (!CallInfo.FD)
    return;
  OriginList *CallList = getOriginsList(*Call);
  // Ignore functions returning values with no origin.
  const FunctionDecl *FD = getDeclWithMergedLifetimeBoundAttrs(CallInfo.FD);
  if (!FD)
    return;
  handleInvalidatingCall(Call, FD, Args);
  handleDestructiveCall(Call, FD, Args);
  handleMovedArgsInCall(FD, Args);
  handleImplicitObjectFieldUses(Call, FD);
  handleLifetimeCaptureBy(FD, Args);
  // A named lifetime signature is strictly more precise than `lifetimebound`,
  // so where one governs the result it wins outright and the union below is
  // skipped entirely. See "Q5: signatures and lifetimebound".
  //
  // This runs before the bails below because the obligations a `$static`
  // parameter imposes on its argument do not depend on the result: a `void`
  // function has no result at all, and it still has to be checked.
  bool SignatureGovernsResult = handleNamedLifetimeCall(FD, Args, CallList);
  handleAllocatingCall(Call, FD);
  handleFreeingCall(Call, FD, Args);
  if (!CallList)
    return;
  if (isStdReferenceCast(FD)) {
    assert(Args.size() == 1 &&
           "std reference cast builtins take exactly one argument");
    // std reference-cast functions like std::move return a result that refers
    // to the same object as the argument, so propagate the full origins.
    flow(CallList, getOriginsList(*Args[0]), /*Kill=*/true);
    return;
  }
  auto shouldTrackPointerImplicitObjectArg = [this, FD,
                                              &Args](unsigned I) -> bool {
    if (I != 0 || !hasObjectArg(*FD))
      return false;
    // A by-value explicit object parameter takes a prvalue copy, which is
    // handled as an ordinary argument below.
    if (!hasImplicitObjectArg(*FD) && !Args[0]->isGLValue())
      return false;
    const auto *Method = cast<CXXMethodDecl>(FD);
    return isHeuristicGslPointerType(AC.getASTContext(),
                                     Method->getFunctionObjectParameterType()) &&
           shouldTrackImplicitObjectArg(*Args[0], Method,
                                        /*RunningUnderLifetimeSafety=*/true);
  };
  if (Args.empty())
    return;
  if (SignatureGovernsResult)
    return;
  bool KillSrc = true;
  for (unsigned I = 0; I < Args.size(); ++I) {
    OriginList *ArgList = getOriginsList(*Args[I]);
    if (!ArgList)
      continue;
    bool ShouldTrackArg = getTrackedArgInfo(FD, Args, I).has_value();
    if (IsGslConstruction) {
      // TODO: document with code example.
      // std::string_view(const std::string_view& from)
      if (isGslPointerType(Args[I]->getType())) {
        assert(!Args[I]->isGLValue() || ArgList->getLength() >= 2);
        ArgList = readValue(Args[I]);
      }
      if (isGslOwnerType(Args[I]->getType()) &&
          (Args.size() == 1 || ShouldTrackArg)) {
        // The constructed gsl::Pointer borrows from the Owner's storage, not
        // from what the Owner itself borrows, so only the outermost origin is
        // needed.
        CurrentBlockFacts.push_back(FactMgr.createFact<OriginFlowFact>(
            CallList->getOuterOriginID(), ArgList->getOuterOriginID(),
            KillSrc));
        KillSrc = false;
      } else if (ShouldTrackArg) {
        // Only flow the outer origin here. For lifetimebound args in
        // gsl::Pointer construction, we do not have enough information to
        // safely match inner origins, so the source and
        // destination origin lists may have different lengths.
        // FIXME: Handle origin-shape mismatches gracefully so we can also flow
        // inner origins.
        CurrentBlockFacts.push_back(FactMgr.createFact<OriginFlowFact>(
            CallList->getOuterOriginID(), ArgList->getOuterOriginID(),
            KillSrc));
        KillSrc = false;
      }
    } else if (shouldTrackPointerImplicitObjectArg(I)) {
      assert(ArgList->getLength() >= 2 &&
             "Object arg of pointer type should have at least two origins");
      // See through the GSLPointer reference to see the pointer's value.
      CurrentBlockFacts.push_back(FactMgr.createFact<OriginFlowFact>(
          CallList->getOuterOriginID(),
          ArgList->peelOuterOrigin()->getOuterOriginID(), KillSrc));
      KillSrc = false;
    } else if (ShouldTrackArg) {
      // Lifetimebound on a non-GSL-ctor function means the returned
      // pointer/reference itself must not outlive the arguments. This
      // only constrains the top-level origin.
      CurrentBlockFacts.push_back(FactMgr.createFact<OriginFlowFact>(
          CallList->getOuterOriginID(), ArgList->getOuterOriginID(), KillSrc));
      KillSrc = false;
    }
  }
}

/// Checks if the expression is a `void("__lifetime_test_point_...")` cast.
/// If so, creates a `TestPointFact` and returns true.
bool FactsGenerator::handleTestPoint(const CXXFunctionalCastExpr *FCE) {
  if (!FCE->getType()->isVoidType())
    return false;

  const auto *SubExpr = ignoreParensAndImpCasts(FCE->getSubExpr());
  if (const auto *SL = dyn_cast<StringLiteral>(SubExpr)) {
    llvm::StringRef LiteralValue = SL->getString();
    const std::string Prefix = "__lifetime_test_point_";

    if (LiteralValue.starts_with(Prefix)) {
      StringRef Annotation = LiteralValue.drop_front(Prefix.length());
      CurrentBlockFacts.push_back(
          FactMgr.createFact<TestPointFact>(Annotation));
      return true;
    }
  }
  return false;
}

bool FactsGenerator::namesDeclStorage(const OriginList *List) const {
  return FactMgr.getOriginMgr()
      .getOrigin(List->getOuterOriginID())
      .NamesDeclStorage;
}

void FactsGenerator::handleAccess(const Expr *E) {
  OriginList *List = getOriginsList(*E);
  if (!List || namesDeclStorage(List))
    return;
  CurrentBlockFacts.push_back(FactMgr.createFact<UseFact>(
      *E,
      FactMgr.getOriginMgr().createSingleOriginList(List->getOuterOriginID())));
}

void FactsGenerator::handleUse(const Expr *E) {
  OriginList *List = getOriginsList(*E);
  if (List && namesDeclStorage(List))
    List = List->peelOuterOrigin();
  if (List)
    CurrentBlockFacts.push_back(FactMgr.createFact<UseFact>(*E, List));
}

// Issues a placeholder loan (this->field) for each origin-carrying field of the
// class and its bases. It represents the storage the field refers to, as
// opposed to the field itself (covered by $this).
void FactsGenerator::issueFieldPlaceholderLoans(
    const CXXRecordDecl *ClassDef, llvm::SmallVectorImpl<Fact *> &Facts) {
  assert(ClassDef && "class methods have a defined parent");
  // Eagerly instantiated methods may see their class still being defined.
  assert(ClassDef->isCompleteDefinition() || ClassDef->isBeingDefined());
  auto IssueForRecord = [&](const CXXRecordDecl *RD) {
    for (const FieldDecl *Field : RD->fields()) {
      // Skip private fields of bases as they cannot be named in ClassDef.
      if (RD != ClassDef && Field->getAccess() == AS_private)
        continue;

      if (Field->isAnonymousStructOrUnion()) {
        if (const CXXRecordDecl *Sub = Field->getType()->getAsCXXRecordDecl()) {
          if (const CXXRecordDecl *SubDef = Sub->getDefinition()) {
            // Anonymous records cannot have base classes and they can only have
            // public fields. Sema rejects them with an error otherwise.
            issueFieldPlaceholderLoans(SubDef, Facts);
            continue;
          }
        }
      }
      OriginList *FieldList = getOriginsList(*Field);
      if (!FieldList)
        continue;
      const Loan *L = FactMgr.getLoanMgr().createPlaceholderLoan(Field);
      Facts.push_back(FactMgr.createFact<IssueFact>(
          L->getID(), FieldList->getOuterOriginID()));
    }
    return true;
  };
  IssueForRecord(ClassDef);
  ClassDef->forallBases(IssueForRecord);
}

// Creates an IssueFact for a new placeholder loan for each pointer or reference
// parameter, the implicit 'this', and (if enabled) each origin-carrying field
// at the function's entry.
llvm::SmallVector<Fact *> FactsGenerator::issuePlaceholderLoans() {
  const auto *FD = dyn_cast<FunctionDecl>(AC.getDecl());
  if (!FD)
    return {};

  llvm::SmallVector<Fact *> PlaceholderLoanFacts;
  LifetimeSignature Sig = getLifetimeSignature(AC.getASTContext(), FD);

  // Positions annotated with a named lifetime additionally borrow from that
  // lifetime, so that a value derived from any `$a` position is
  // indistinguishable from one derived from any other. The loan is additive:
  // the position keeps its own placeholder loan, which is what `lifetimebound`
  // verification and the "aliases the storage of" notes rely on.
  //
  // The lifetime list and the origin list are both ordered outermost-first, so
  // they zip positionally. A list that is too long has already been diagnosed;
  // stop at whichever runs out first.
  auto issueNamedLoans = [&](const LifetimeList &Lifetimes, OriginList *List) {
    for (const LifetimeVar &LV : Lifetimes) {
      if (!List)
        break;
      if (LV.getKind() == LifetimeVar::Kind::Named) {
        const Loan *NamedLoan =
            FactMgr.getLoanMgr().getOrCreateNamedPlaceholderLoan(LV.getName());
        PlaceholderLoanFacts.push_back(FactMgr.createFact<IssueFact>(
            NamedLoan->getID(), List->getOuterOriginID(),
            /*Additive=*/true));
      }
      List = List->peelOuterOrigin();
    }
  };

  if (auto ThisOrigins = FactMgr.getOriginMgr().getThisOrigins()) {
    OriginList *List = *ThisOrigins;
    const auto *MD = cast<CXXMethodDecl>(FD);
    const Loan *L = FactMgr.getLoanMgr().createPlaceholderLoan(MD);
    PlaceholderLoanFacts.push_back(
        FactMgr.createFact<IssueFact>(L->getID(), List->getOuterOriginID()));
    // Lifetimes written after the parameter list belong to the implicit
    // object parameter. For a class with `LIFETIME_PARAMS`, the signature
    // also places the class's parameters on its inner levels.
    issueNamedLoans(Sig.FunctionType, List);

    // Trunk's `this->field` placeholder loans replace the field origin's
    // loans, so they go first and the additive named loans below add to them.
    if (LSOpts.CheckFieldOriginEscape && !isa<CXXConstructorDecl>(MD))
      issueFieldPlaceholderLoans(MD->getParent()->getDefinition(),
                                 PlaceholderLoanFacts);

    // `this->field` shares origins with the `FieldDecl`, so issue any named
    // loans written on the field's type directly onto the field's origins.
    // Constructors initialize the fields rather than reading them from an
    // already-constructed object, so skip issuing pre-existing field loans
    // there.
    if (const CXXRecordDecl *RD = MD->getParent()->getDefinition();
        RD && !isa<CXXConstructorDecl>(MD)) {
      ASTContext &Ctx = AC.getASTContext();
      for (const FieldDecl *Field : RD->fields()) {
        LifetimeList FieldLifetimes =
            getExplicitLifetimes(Ctx, Field->getType());
        if (FieldLifetimes.empty())
          continue;
        if (OriginList *FieldList = getOriginsList(*Field))
          issueNamedLoans(FieldLifetimes, FieldList);
      }
    }

  }

  unsigned ParamIdx = 0;
  for (const ParmVarDecl *PVD : FD->parameters()) {
    const unsigned Idx = ParamIdx++;
    OriginList *List = getOriginsList(*PVD);
    if (!List)
      continue;
    const Loan *L = FactMgr.getLoanMgr().createPlaceholderLoan(PVD);
    PlaceholderLoanFacts.push_back(
        FactMgr.createFact<IssueFact>(L->getID(), List->getOuterOriginID()));

    if (Idx < Sig.Params.size())
      issueNamedLoans(Sig.Params[Idx], List);
  }
  return PlaceholderLoanFacts;
}

} // namespace clang::lifetimes::internal
