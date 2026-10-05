//===- LifetimeAnnotations.cpp -  -*--------------- C++------------------*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
#include "clang/Analysis/Analyses/LifetimeSafety/LifetimeAnnotations.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Attr.h"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/DeclTemplate.h"
#include "clang/AST/Expr.h"
#include "clang/AST/ExprCXX.h"
#include "clang/AST/Type.h"
#include "clang/AST/TypeLoc.h"
#include "clang/Analysis/AnyCall.h"
#include "clang/Basic/OperatorKinds.h"
#include "clang/Basic/SourceManager.h"
#include "llvm/ADT/StringSet.h"

namespace clang::lifetimes {

const FunctionDecl *
getDeclWithMergedLifetimeBoundAttrs(const FunctionDecl *FD) {
  return FD != nullptr ? FD->getMostRecentDecl() : nullptr;
}

const CXXMethodDecl *
getDeclWithMergedLifetimeBoundAttrs(const CXXMethodDecl *CMD) {
  const FunctionDecl *FD = CMD;
  return cast_if_present<CXXMethodDecl>(
      getDeclWithMergedLifetimeBoundAttrs(FD));
}

bool isNormalAssignmentOperator(const FunctionDecl *FD) {
  OverloadedOperatorKind OO = FD->getDeclName().getCXXOverloadedOperator();
  bool IsAssignment = OO == OO_Equal || isCompoundAssignmentOperator(OO);
  if (!IsAssignment)
    return false;
  QualType RetT = FD->getReturnType();
  if (!RetT->isLValueReferenceType())
    return false;
  ASTContext &Ctx = FD->getASTContext();
  QualType LHST;
  auto *MD = dyn_cast<CXXMethodDecl>(FD);
  if (MD && MD->isCXXInstanceMember())
    LHST = Ctx.getLValueReferenceType(MD->getFunctionObjectParameterType());
  else
    LHST = FD->getParamDecl(0)->getType();
  return Ctx.hasSameType(RetT, LHST);
}

bool isAssignmentOperatorLifetimeBound(const CXXMethodDecl *CMD) {
  CMD = getDeclWithMergedLifetimeBoundAttrs(CMD);
  return CMD && isNormalAssignmentOperator(CMD) && CMD->param_size() == 1 &&
         CMD->getParamDecl(0)->hasAttr<clang::LifetimeBoundAttr>();
}

/// Check if a function has a lifetimebound attribute on its function type
/// (which represents the implicit 'this' parameter for methods).
/// Returns the attribute if found, nullptr otherwise.
static const LifetimeBoundAttr *
getLifetimeBoundAttrFromFunctionType(const TypeSourceInfo &TSI) {
  // Walk through the type layers looking for a lifetimebound attribute.
  TypeLoc TL = TSI.getTypeLoc();
  while (true) {
    auto ATL = TL.getAsAdjusted<AttributedTypeLoc>();
    if (!ATL)
      break;
    if (auto *LBAttr = ATL.getAttrAs<LifetimeBoundAttr>())
      return LBAttr;
    TL = ATL.getModifiedLoc();
  }
  return nullptr;
}

const LifetimeBoundAttr *
getDirectImplicitObjectLifetimeBoundAttr(const FunctionDecl *FD) {
  if (const TypeSourceInfo *TSI = FD->getTypeSourceInfo())
    if (const auto *Attr = getLifetimeBoundAttrFromFunctionType(*TSI))
      return Attr;
  return nullptr;
}

const LifetimeBoundAttr *
getImplicitObjectParamLifetimeBoundAttr(const FunctionDecl *FD) {
  FD = getDeclWithMergedLifetimeBoundAttrs(FD);
  // Attribute merging doesn't work well with attributes on function types (like
  // 'this' param). We need to check all redeclarations.
  auto CheckRedecls = [](const FunctionDecl *F) -> const LifetimeBoundAttr * {
    for (const FunctionDecl *Redecl : F->redecls())
      if (const auto *Attr = getDirectImplicitObjectLifetimeBoundAttr(Redecl))
        return Attr;
    return nullptr;
  };

  if (const auto *Attr = CheckRedecls(FD))
    return Attr;
  if (const FunctionDecl *Pattern = FD->getTemplateInstantiationPattern())
    return CheckRedecls(Pattern);
  return nullptr;
}

bool implicitObjectParamIsLifetimeBound(const FunctionDecl *FD) {
  if (getImplicitObjectParamLifetimeBoundAttr(FD))
    return true;
  return isNormalAssignmentOperator(FD);
}

FunctionCallInfo::FunctionCallInfo(const Expr *Call) {
  if (!Call)
    return;

  std::optional<AnyCall> AC = AnyCall::forExpr(Call->IgnoreParenImpCasts());
  if (!AC)
    return;

  Args = AC->arguments();
  FD = dyn_cast_or_null<FunctionDecl>(AC->getDecl());
}

std::optional<LifetimeBoundParamInfo>
getTrackedArgInfo(const FunctionDecl *FD, llvm::ArrayRef<const Expr *> Args,
                  unsigned I) {
  FD = getDeclWithMergedLifetimeBoundAttrs(FD);
  if (!FD || I >= Args.size())
    return std::nullopt;

  const ParmVarDecl *PVD = nullptr;

  if (const auto *Method = dyn_cast<CXXMethodDecl>(FD);
      Method && Method->isInstance() && !isa<CXXConstructorDecl>(FD)) {
    if (I == 0) {
      // For the 'this' argument, the attribute is on the method itself.
      if (implicitObjectParamIsLifetimeBound(Method) ||
          shouldTrackImplicitObjectArg(*Args[0], Method,
                                       /*RunningUnderLifetimeSafety=*/true))
        return LifetimeBoundParamInfo(Method);
      return std::nullopt;
    }
    if ((I - 1) < Method->getNumParams())
      // For explicit arguments, find the corresponding parameter declaration.
      PVD = Method->getParamDecl(I - 1);
  } else if (I == 0 && shouldTrackFirstArgument(FD)) {
    return LifetimeBoundParamInfo(FD->getParamDecl(I));
  } else if (I == 1 && shouldTrackSecondArgument(FD)) {
    return LifetimeBoundParamInfo(FD->getParamDecl(I));
  } else if (I < FD->getNumParams()) {
    // For free functions or static methods.
    PVD = FD->getParamDecl(I);
  }

  if (PVD && PVD->hasAttr<clang::LifetimeBoundAttr>())
    return LifetimeBoundParamInfo(PVD);

  return std::nullopt;
}

std::optional<LifetimeBoundParamInfo>
getTrackingInfoForCallArg(const Expr *Call, const Expr *Source) {
  if (!Call || !Source)
    return std::nullopt;

  auto [FD, Args] = FunctionCallInfo(Call);
  if (!FD)
    return std::nullopt;

  for (unsigned I = 0; I < Args.size(); ++I)
    if (Args[I]->IgnoreParenImpCasts() == Source->IgnoreParenImpCasts())
      if (std::optional<LifetimeBoundParamInfo> ParamInfo =
              getTrackedArgInfo(FD, Args, I))
        return ParamInfo;

  return std::nullopt;
}

bool isInStlNamespace(const Decl *D) {
  for (const DeclContext *DC = D->getDeclContext(); DC; DC = DC->getParent()) {
    if (DC->isStdNamespace())
      return true;
    if (const auto *ND = dyn_cast<NamespaceDecl>(DC))
      if (const IdentifierInfo *II = ND->getIdentifier()) {
        StringRef Name = II->getName();
        if (Name.size() >= 2 && Name.front() == '_' &&
            (Name[1] == '_' || isUppercase(Name[1])))
          return true;
      }
  }
  return false;
}

bool isPointerLikeType(QualType QT) {
  return isGslPointerType(QT) || QT->isPointerType() || QT->isNullPtrType();
}

static bool isReferenceOrPointerLikeType(QualType QT) {
  return QT->isReferenceType() || isPointerLikeType(QT);
}

bool shouldTrackImplicitObjectArg(const Expr &ImplicitObjectArgument,
                                  const CXXMethodDecl *Callee,
                                  bool RunningUnderLifetimeSafety) {
  if (!Callee)
    return false;
  // Check both the declaring class and the call-site object: a gsl::Owner
  // may inherit its accessors from a non-Owner base (e.g. libc++ optional).
  const bool IsGslOwnerImplicitObject =
      isGslOwnerType(Callee->getFunctionObjectParameterType()) ||
      (RunningUnderLifetimeSafety &&
       isGslOwnerType(ImplicitObjectArgument.getBestDynamicClassType()));
  if (auto *Conv = dyn_cast<CXXConversionDecl>(Callee))
    if (isGslPointerType(Conv->getConversionType()) && IsGslOwnerImplicitObject)
      return true;
  if (!isGslPointerType(Callee->getFunctionObjectParameterType()) &&
      !IsGslOwnerImplicitObject)
    return false;

  // Begin and end iterators.
  static const llvm::StringSet<> IteratorMembers = {
      "begin", "end", "rbegin", "rend", "cbegin", "cend", "crbegin", "crend"};
  static const llvm::StringSet<> InnerPointerGetters = {
      // Inner pointer getters.
      "c_str", "data", "get"};
  static const llvm::StringSet<> ContainerFindFns = {
      // Map and set types.
      "find", "equal_range", "lower_bound", "upper_bound"};
  // Track dereference operator and transparent functions like begin(), get(),
  // etc. for all GSL pointers. Only do so for lifetime safety analysis and not
  // for Sema's statement-local analysis as it starts to have false-positives.
  if (RunningUnderLifetimeSafety &&
      isGslPointerType(Callee->getFunctionObjectParameterType()) &&
      isReferenceOrPointerLikeType(Callee->getReturnType())) {
    // Propagate origins through GSL pointer arithmetic and dereference
    // operators.
    switch (Callee->getOverloadedOperator()) {
    case OO_Arrow:
    case OO_Star:
    case OO_Plus:
    case OO_Minus:
    case OO_PlusPlus:
    case OO_MinusMinus:
      return true;
    default:
      break;
    }
    if (Callee->getIdentifier() &&
        (IteratorMembers.contains(Callee->getName()) ||
         InnerPointerGetters.contains(Callee->getName())))
      return true;
  }

  if (!isInStlNamespace(Callee->getParent()))
    return false;

  if (isPointerLikeType(Callee->getReturnType())) {
    if (!Callee->getIdentifier())
      // e.g., std::optional<T>::operator->() returns T*.
      return RunningUnderLifetimeSafety
                 ? IsGslOwnerImplicitObject &&
                       Callee->getOverloadedOperator() ==
                           OverloadedOperatorKind::OO_Arrow
                 : false;
    return IteratorMembers.contains(Callee->getName()) ||
           InnerPointerGetters.contains(Callee->getName()) ||
           ContainerFindFns.contains(Callee->getName());
  }
  if (Callee->getReturnType()->isReferenceType()) {
    if (!Callee->getIdentifier()) {
      auto OO = Callee->getOverloadedOperator();
      if (!IsGslOwnerImplicitObject)
        return false;
      return OO == OverloadedOperatorKind::OO_Subscript ||
             OO == OverloadedOperatorKind::OO_Star;
    }
    return llvm::StringSwitch<bool>(Callee->getName())
        .Cases({"front", "back", "at", "top", "value"}, true)
        .Default(false);
  }
  return false;
}

bool shouldTrackFirstArgument(const FunctionDecl *FD) {
  if (!FD->getIdentifier() || FD->getNumParams() < 1)
    return false;
  if (!FD->isInStdNamespace())
    return false;
  // Track std:: algorithm functions that return an iterator whose lifetime is
  // bound to the first argument.
  if (FD->getNumParams() >= 2 && FD->isInStdNamespace() &&
      isGslPointerType(FD->getReturnType())) {
    if (llvm::StringSwitch<bool>(FD->getName())
            .Cases(
                {
                    "find",
                    "find_if",
                    "find_if_not",
                    "find_first_of",
                    "adjacent_find",
                    "search",
                    "find_end",
                    "lower_bound",
                    "upper_bound",
                    "partition_point",
                },
                true)
            .Default(false))
      return true;
  }
  const auto *RD = FD->getParamDecl(0)->getType()->getPointeeCXXRecordDecl();
  if (!RD || !RD->isInStdNamespace())
    return false;
  if (!RD->hasAttr<PointerAttr>() && !RD->hasAttr<OwnerAttr>())
    return false;

  if (FD->getNumParams() != 1)
    return false;

  if (FD->getReturnType()->isPointerType() ||
      isGslPointerType(FD->getReturnType())) {
    return llvm::StringSwitch<bool>(FD->getName())
        .Cases({"begin", "rbegin", "cbegin", "crbegin"}, true)
        .Cases({"end", "rend", "cend", "crend"}, true)
        .Case("data", true)
        .Default(false);
  }
  if (FD->getReturnType()->isReferenceType()) {
    return llvm::StringSwitch<bool>(FD->getName())
        .Cases({"get", "any_cast"}, true)
        .Default(false);
  }
  return false;
}

bool shouldTrackSecondArgument(const FunctionDecl *FD) {
  if (FD->getNumParams() < 2)
    return false;
  const auto *RD = FD->getParamDecl(1)->getType()->getAsCXXRecordDecl();
  if (!RD)
    return false;
  // For free-standing `+`/`-` operators annotated with `gsl::Pointer`, track
  // the second parameter when its type matches the return type.
  return RD->hasAttr<PointerAttr>() &&
         (FD->getOverloadedOperator() == OO_Plus ||
          FD->getOverloadedOperator() == OO_Minus) &&
         ASTContext::hasSameUnqualifiedType(FD->getParamDecl(1)->getType(),
                                            FD->getReturnType()) &&
         !isa<CXXMethodDecl>(FD);
}

template <typename T> static bool isRecordWithAttr(const CXXRecordDecl *RD) {
  if (!RD)
    return false;
  // Generally, if a primary template class declaration is annotated with an
  // attribute, all its specializations generated from template instantiations
  // should inherit the attribute.
  //
  // However, since lifetime analysis occurs during parsing, we may encounter
  // cases where a full definition of the specialization is not required. In
  // such cases, the specialization declaration remains incomplete and lacks the
  // attribute. Therefore, we fall back to checking the primary template class.
  //
  // Note: it is possible for a specialization declaration to have an attribute
  // even if the primary template does not.
  //
  // FIXME: What if the primary template and explicit specialization
  // declarations have conflicting attributes? We should consider diagnosing
  // this scenario.
  bool Result = RD->hasAttr<T>();

  if (auto *CTSD = dyn_cast<ClassTemplateSpecializationDecl>(RD))
    Result |= CTSD->getSpecializedTemplate()->getTemplatedDecl()->hasAttr<T>();

  return Result;
}

template <typename T> static bool isRecordWithAttr(QualType Type) {
  return isRecordWithAttr<T>(Type->getAsCXXRecordDecl());
}

bool isGslPointerType(QualType QT) { return isRecordWithAttr<PointerAttr>(QT); }
bool isGslOwnerType(QualType QT) { return isRecordWithAttr<OwnerAttr>(QT); }
bool isGslOwnerType(const CXXRecordDecl *RD) {
  return isRecordWithAttr<OwnerAttr>(RD);
}

bool isOwnerPtrCtor(const CXXConstructorDecl *Ctor, const ParmVarDecl *PVD) {
  return Ctor && PVD->getType()->isPointerType() &&
         isGslOwnerType(Ctor->getParent());
}

static StringRef getName(const CXXRecordDecl &RD) {
  if (const auto *CTSD = dyn_cast<ClassTemplateSpecializationDecl>(&RD))
    return CTSD->getSpecializedTemplate()->getName();
  if (RD.getIdentifier())
    return RD.getName();
  return "";
}

static StringRef getName(const FunctionDecl &FD) {
  if (FD.getIdentifier())
    return FD.getName();
  return "";
}

static bool isStdUniquePtr(const CXXRecordDecl &RD) {
  return RD.isInStdNamespace() && getName(RD) == "unique_ptr";
}

bool isUniquePtrRelease(const CXXMethodDecl &MD) {
  return MD.getIdentifier() && MD.getName() == "release" &&
         MD.getNumParams() == 0 && isStdUniquePtr(*MD.getParent());
}

bool isInvalidationMethod(const CXXMethodDecl &MD) {
  const CXXRecordDecl *RD = MD.getParent();
  if (!isInStlNamespace(RD))
    return false;

  // `pop_back` is excluded: it only invalidates references to the removed
  // element, not to other elements.
  static const llvm::StringSet<> Vector = {// Insertion
                                           "insert", "emplace", "emplace_back",
                                           "push_back", "insert_range",
                                           "append_range",
                                           // Removal
                                           "erase", "clear",
                                           // Memory management
                                           "reserve", "resize", "shrink_to_fit",
                                           // Assignment
                                           "assign", "assign_range"};

  // `pop_*` methods are excluded: they only invalidate references to the
  // removed element, not to other elements.
  static const llvm::StringSet<> Deque = {// Insertion
                                          "insert", "emplace", "insert_range",
                                          // Removal
                                          "erase", "clear",
                                          // Memory management
                                          "resize", "shrink_to_fit",
                                          // Assignment
                                          "assign", "assign_range"};

  static const llvm::StringSet<> String = {
      // Insertion
      "insert", "push_back", "append", "replace", "replace_with_range",
      "insert_range", "append_range",
      // Removal
      "pop_back", "erase", "clear",
      // Memory management
      "reserve", "resize", "resize_and_overwrite", "shrink_to_fit",
      // Assignment
      "swap", "assign", "assign_range"};

  // FIXME: Add queue and stack and check for underlying container
  // (e.g. no invalidation for std::list).
  static const llvm::StringSet<> PriorityQueue = {// Insertion
                                                  "push", "emplace",
                                                  "push_range",
                                                  // Removal
                                                  "pop"};

  // `erase` and `extract` are excluded: they only affect the removed element,
  // not to other elements.
  static const llvm::StringSet<> NodeBased = {// Removal
                                              "clear"};

  // For `flat_*` container adaptors, `try_emplace` and `insert_or_assign`
  // only exist on `flat_map`. Listing them here is harmless since the methods
  // won't be found on other types.
  static const llvm::StringSet<> Flat = {// Insertion
                                         "insert", "emplace", "emplace_hint",
                                         "try_emplace", "insert_or_assign",
                                         "insert_range", "merge",
                                         // Removal
                                         "extract", "erase", "clear",
                                         // Assignment
                                         "replace"};

  static const llvm::StringSet<> UniquePtr = {// Reallocation
                                              "reset"};

  const StringRef RecordName = getName(*RD);
  // TODO: Consider caching this lookup by CXXMethodDecl pointer if this
  // StringSwitch becomes a performance bottleneck.
  const llvm::StringSet<> *InvalidatingMethods =
      llvm::StringSwitch<const llvm::StringSet<> *>(RecordName)
          .Case("vector", &Vector)
          .Case("basic_string", &String)
          .Case("deque", &Deque)
          .Case("priority_queue", &PriorityQueue)
          .Cases({"set", "multiset", "map", "multimap", "unordered_set",
                  "unordered_multiset", "unordered_map", "unordered_multimap"},
                 &NodeBased)
          .Cases({"flat_map", "flat_set", "flat_multimap", "flat_multiset"},
                 &Flat)
          .Case("unique_ptr", &UniquePtr)
          .Default(nullptr);

  if (!InvalidatingMethods)
    return false;

  // Handle Operators via OverloadedOperatorKind
  OverloadedOperatorKind OO = MD.getOverloadedOperator();
  if (OO != OO_None) {
    switch (OO) {
    case OO_Equal:     // operator= : Always invalidates (Assignment)
    case OO_PlusEqual: // operator+= : Append (String/Vector)
      return true;
    case OO_Subscript: // operator[] : Invalidation only for
                       // `flat_map` (Insert-or-access).
                       // `map` and `unordered_map` are excluded.
      return RecordName == "flat_map";
    default:
      return false;
    }
  }

  if (!MD.getIdentifier())
    return false;

  return InvalidatingMethods->contains(MD.getName());
}

bool destructsFirstArg(const FunctionDecl &FD) {
  if (isa<CXXDestructorDecl>(FD))
    return true;
  return isInStlNamespace(&FD) && getName(FD) == "destroy_at";
}

bool isStdCallableWrapperType(const CXXRecordDecl *RD) {
  if (!RD || !isInStlNamespace(RD))
    return false;
  StringRef Name = getName(*RD);
  return Name == "function" || Name == "move_only_function";
}

bool isStdReferenceCast(const FunctionDecl *FD) {
  if (!FD)
    return false;
  switch (FD->getBuiltinID()) {
  case Builtin::BImove:
  case Builtin::BImove_if_noexcept:
  case Builtin::BIforward:
  case Builtin::BIforward_like:
  case Builtin::BIas_const:
    return true;
  default:
    return false;
  }
}

//===----------------------------------------------------------------------===//
// Named lifetimes
//===----------------------------------------------------------------------===//

LifetimeVar::LifetimeVar(llvm::StringRef Name) : Name(Name) {
  if (Name == "static")
    K = Kind::Static;
  else if (Name == "unknown")
    K = Kind::Unknown;
  else
    K = Kind::Named;
}

void LifetimeVar::dump(llvm::raw_ostream &OS) const {
  if (isElided()) {
    OS << "<elided>";
    return;
  }
  OS << "$" << Name;
}

namespace {

/// Extracts the value of a string-literal attribute argument.
///
/// Sema constant-folds `annotate`/`annotate_type` arguments and applies
/// array-to-pointer decay, so a `"a"` argument arrives here as an LValue whose
/// base is the StringLiteral rather than as a string.
std::optional<llvm::StringRef> evaluateAsStringLiteral(const ASTContext &Ctx,
                                                       const Expr *E) {
  if (!E || E->isValueDependent() || E->isTypeDependent())
    return std::nullopt;
  Expr::EvalResult Eval;
  if (!E->EvaluateAsConstantExpr(Eval, Ctx) || !Eval.Val.isLValue())
    return std::nullopt;
  const auto *Base = Eval.Val.getLValueBase().dyn_cast<const Expr *>();
  const auto *SL = dyn_cast_or_null<StringLiteral>(Base);
  if (!SL)
    return std::nullopt;
  return SL->getString();
}

/// Appends the lifetimes named by a single `annotate_type("lifetime", ...)`.
///
/// Arguments are appended in reverse so that the single reversal performed by
/// getExplicitLifetimesAtLevel restores source order for both spellings
/// (`$(a) $(b)` and a hypothetical `$(a, b)`).
void appendLifetimesReversed(const ASTContext &Ctx,
                             const AnnotateTypeAttr *Attr, LifetimeList &Out) {
  for (const Expr *Arg : llvm::reverse(Attr->args()))
    if (std::optional<llvm::StringRef> Name = evaluateAsStringLiteral(Ctx, Arg))
      Out.push_back(LifetimeVar(*Name));
}

} // namespace

QualType getExplicitLifetimesAtLevel(const ASTContext &Ctx, QualType QT,
                                     LifetimeList &Out) {
  const size_t FirstNew = Out.size();
  while (const Type *T = QT.getTypePtrOrNull()) {
    // Every macro-spelled attribute is wrapped in a MacroQualifiedType; missing
    // this would hide all annotations written through the `$` macros.
    if (const auto *MQT = dyn_cast<MacroQualifiedType>(T)) {
      QT = MQT->getUnderlyingType();
      continue;
    }
    // Deliberately dyn_cast rather than Type::getAs<>(): getAs<>() looks
    // through all sugar and would skip past the level being inspected.
    if (const auto *AT = dyn_cast<AttributedType>(T)) {
      if (const auto *ATA = dyn_cast_or_null<AnnotateTypeAttr>(AT->getAttr()))
        if (ATA->getAnnotation() == LifetimeAnnotationCategory)
          appendLifetimesReversed(Ctx, ATA, Out);
      QT = AT->getModifiedType();
      continue;
    }
    break;
  }
  // Attributes nest with the last-written one outermost, so reverse the
  // lifetimes found at this level to recover source order.
  std::reverse(Out.begin() + FirstNew, Out.end());
  return QT;
}

unsigned getLifetimeSlotsAtLevel(const ASTContext &Ctx, QualType QT) {
  if (QT.isNull())
    return 0;
  if (QT->isPointerOrReferenceType())
    return 1;
  // A class type carries exactly the lifetimes its definition declares.
  // Nothing is inferred from its members.
  if (const auto *RD = QT->getAsCXXRecordDecl())
    if (const CXXRecordDecl *Def = RD->getDefinition())
      return getDeclaredLifetimeParams(Ctx, Def).size();
  return 0;
}

LifetimeList getExplicitLifetimes(const ASTContext &Ctx, QualType QT) {
  LifetimeList Result;
  // Mirror the levels built by OriginManager::buildListForType so that the
  // result can be zipped against an OriginList.
  while (!QT.isNull()) {
    const size_t LevelStart = Result.size();
    // Collect everything written at this level. `_Atomic(T)` is transparent
    // for lifetime purposes, so it does not begin a level of its own and any
    // annotations on either side of it belong together.
    for (;;) {
      QT = getExplicitLifetimesAtLevel(Ctx, QT, Result);
      const auto *AT = QT.isNull() ? nullptr : QT->getAs<AtomicType>();
      if (!AT)
        break;
      QT = AT->getValueType();
    }
    if (QT.isNull())
      break;

    // Each level is annotated independently, so a level with nothing written
    // on it still occupies its slots, and a level with too much written on it
    // does not spill onto the next. Normalising every level to exactly its own
    // size keeps the levels that follow aligned with their origins; without it
    // an annotation on an inner level would be attributed to an outer one, and
    // the ill-formed `int **$a $b` would silently acquire the meaning of the
    // well-formed `int *$a *$b`. The excess is diagnosed in SignatureCheck.
    Result.resize(LevelStart + getLifetimeSlotsAtLevel(Ctx, QT),
                  LifetimeVar::elided());

    if (!QT->isPointerOrReferenceType())
      break;
    QT = QT->getPointeeType();
  }
  // Trailing holes say nothing that the list's length does not already say.
  // Dropping them keeps a type with no annotations at all elaborating to the
  // empty list.
  while (!Result.empty() && Result.back().isElided())
    Result.pop_back();
  return Result;
}

LifetimeList getDeclaredLifetimeParams(const ASTContext &Ctx, const Decl *D) {
  LifetimeList Result;
  if (!D)
    return Result;
  for (const auto *Attr : D->specific_attrs<AnnotateAttr>()) {
    if (Attr->getAnnotation() != LifetimeParamsAnnotationCategory)
      continue;
    for (const Expr *Arg : Attr->args())
      if (std::optional<llvm::StringRef> Name =
              evaluateAsStringLiteral(Ctx, Arg))
        Result.push_back(LifetimeVar(*Name));
  }
  return Result;
}

bool LifetimeSignature::empty() const {
  if (!Declared.empty() || !FunctionType.empty() || !Return.empty())
    return false;
  return llvm::all_of(Params, [](const LifetimeList &L) { return L.empty(); });
}

void LifetimeSignature::dump(llvm::raw_ostream &OS,
                             const FunctionDecl *FD) const {
  auto PrintList = [&OS](llvm::StringRef Label, const LifetimeList &L) {
    OS << "  " << Label << ": ";
    if (L.empty()) {
      OS << "<none>\n";
      return;
    }
    for (size_t I = 0; I < L.size(); ++I) {
      if (I)
        OS << ", ";
      L[I].dump(OS);
    }
    OS << "\n";
  };

  OS << "Lifetime signature for "
     << (FD ? FD->getQualifiedNameAsString() : "<null>") << ":\n";
  PrintList("declared", Declared);
  PrintList("function-type", FunctionType);
  PrintList("return", Return);
  for (size_t I = 0; I < Params.size(); ++I) {
    std::string Label = "param " + std::to_string(I);
    if (FD && I < FD->getNumParams())
      if (const IdentifierInfo *II = FD->getParamDecl(I)->getIdentifier())
        Label += " ('" + II->getName().str() + "')";
    PrintList(Label, Params[I]);
  }
}

/// Reads the signature spelled on one particular declaration of a function.
LifetimeSignature getDirectLifetimeSignature(const ASTContext &Ctx,
                                             const FunctionDecl *FD) {
  LifetimeSignature Sig;
  // An attribute written after the parameter list wraps the whole function
  // type; peeling it here also exposes the FunctionProtoType underneath.
  getExplicitLifetimesAtLevel(Ctx, FD->getType(), Sig.FunctionType);
  Sig.Return = getExplicitLifetimes(Ctx, FD->getReturnType());
  Sig.Params.reserve(FD->getNumParams());
  for (const ParmVarDecl *PVD : FD->parameters())
    Sig.Params.push_back(getExplicitLifetimes(Ctx, PVD->getType()));
  return Sig;
}

LifetimeSignature getLifetimeSignature(const ASTContext &Ctx,
                                       const FunctionDecl *FD) {
  LifetimeSignature Sig;
  if (!FD)
    return Sig;

  // `annotate` is an inheritable declaration attribute, so it is visible on any
  // redeclaration.
  Sig.Declared = getDeclaredLifetimeParams(Ctx, FD);

  // Attributes on types do not merge across redeclarations, so the annotations
  // are only visible on the declaration that spelled them.
  auto ScanRedecls =
      [&](const FunctionDecl *F) -> std::optional<LifetimeSignature> {
    for (const FunctionDecl *Redecl : F->redecls()) {
      LifetimeSignature Candidate = getDirectLifetimeSignature(Ctx, Redecl);
      if (!Candidate.empty())
        return Candidate;
    }
    return std::nullopt;
  };

  // TODO: Diagnose conflicting signatures across redeclarations rather than
  // taking the first one that carries annotations.
  std::optional<LifetimeSignature> Found = ScanRedecls(FD);
  if (!Found)
    if (const FunctionDecl *Pattern = FD->getTemplateInstantiationPattern())
      Found = ScanRedecls(Pattern);

  if (Found) {
    Sig.FunctionType = std::move(Found->FunctionType);
    Sig.Return = std::move(Found->Return);
    Sig.Params = std::move(Found->Params);
  } else {
    Sig.Params.resize(FD->getNumParams());
  }
  return Sig;
}

bool haveSameWrittenLifetimes(const LifetimeSignature &A,
                              const LifetimeSignature &B) {
  return A.FunctionType == B.FunctionType && A.Return == B.Return &&
         A.Params == B.Params;
}

//===----------------------------------------------------------------------===//
// Locations
//===----------------------------------------------------------------------===//

namespace {

/// Collects the lifetimes written at the outermost level of \p TL.
///
/// This mirrors getExplicitLifetimesAtLevel, but over TypeLoc, which is the
/// only representation that records where each individual annotation was
/// written. Returns the TypeLoc with this level's annotation sugar removed.
TypeLoc collectUsesAtLevel(const ASTContext &Ctx, TypeLoc TL,
                           LifetimeUseList &Out,
                           SourceLocation &NonLiteralArgLoc) {
  const size_t FirstNew = Out.size();
  // The innermost enclosing macro expansion, which is where the user actually
  // wrote `$a`. The attribute's own location points into the macro definition.
  SourceLocation MacroLoc;
  while (TL) {
    if (auto MQL = TL.getAs<MacroQualifiedTypeLoc>()) {
      MacroLoc = MQL.getExpansionLoc();
      TL = MQL.getInnerLoc();
      continue;
    }
    if (auto ATL = TL.getAs<AttributedTypeLoc>()) {
      const auto *ATA = dyn_cast_or_null<AnnotateTypeAttr>(ATL.getAttr());
      if (ATA && ATA->getAnnotation() == LifetimeAnnotationCategory) {
        SourceLocation Loc = MacroLoc.isValid()
                                 ? MacroLoc
                                 : ATL.getLocalSourceRange().getBegin();
        // Arguments are appended in reverse so that the single reversal below
        // restores source order; see appendLifetimesReversed.
        for (const Expr *Arg : llvm::reverse(ATA->args())) {
          std::optional<llvm::StringRef> Name =
              evaluateAsStringLiteral(Ctx, Arg);
          if (!Name) {
            if (NonLiteralArgLoc.isInvalid())
              NonLiteralArgLoc = Loc;
            continue;
          }
          Out.push_back({LifetimeVar(*Name), Loc});
        }
      }
      MacroLoc = SourceLocation();
      TL = ATL.getModifiedLoc();
      continue;
    }
    break;
  }
  // Attributes nest with the last-written one outermost.
  std::reverse(Out.begin() + FirstNew, Out.end());
  return TL;
}

} // namespace

WrittenLifetimes getWrittenLifetimes(const ASTContext &Ctx, TypeLoc TL) {
  WrittenLifetimes Result;
  while (TL) {
    WrittenLifetimeLevel Level;
    // `_Atomic(T)` and parentheses are transparent for lifetime purposes:
    // neither begins a level of its own, so annotations written on either side
    // of one belong together. This mirrors getExplicitLifetimes, which must
    // agree with this walk on which annotations belong to which level.
    for (;;) {
      TL = collectUsesAtLevel(Ctx, TL, Level.Uses, Result.NonLiteralArgLoc);
      if (!TL)
        break;
      if (auto ATL = TL.getAs<AtomicTypeLoc>()) {
        TL = ATL.getValueLoc();
        continue;
      }
      if (auto PTL = TL.getAs<ParenTypeLoc>()) {
        TL = PTL.getInnerLoc();
        continue;
      }
      break;
    }
    if (!TL)
      break;

    Level.Type = TL.getType();
    Result.Levels.push_back(std::move(Level));

    if (auto PTL = TL.getAs<PointerTypeLoc>()) {
      TL = PTL.getPointeeLoc();
      continue;
    }
    if (auto RTL = TL.getAs<ReferenceTypeLoc>()) {
      TL = RTL.getPointeeLoc();
      continue;
    }
    break;
  }
  return Result;
}

DeclaredLifetimes getDeclaredLifetimes(const ASTContext &Ctx, const Decl *D) {
  DeclaredLifetimes Result;
  if (!D)
    return Result;
  const SourceManager &SM = Ctx.getSourceManager();
  for (const auto *Attr : D->specific_attrs<AnnotateAttr>()) {
    if (Attr->getAnnotation() != LifetimeParamsAnnotationCategory)
      continue;
    // The attribute itself is spelled inside the LIFETIME_PARAMS macro, so its
    // own location points at the macro definition.
    Result.AttrLocs.push_back(SM.getFileLoc(Attr->getLocation()));
    for (const Expr *Arg : Attr->args()) {
      // Unlike the `$a` type annotations, these arguments are written by the
      // user at the use site. getFileLoc recovers that spelling location,
      // where getExpansionLoc would collapse them all onto the macro name.
      SourceLocation Loc = SM.getFileLoc(Arg->getExprLoc());
      std::optional<llvm::StringRef> Name = evaluateAsStringLiteral(Ctx, Arg);
      if (!Name) {
        if (Result.NonLiteralArgLoc.isInvalid())
          Result.NonLiteralArgLoc = Loc;
        continue;
      }
      Result.Params.push_back({LifetimeVar(*Name), Loc});
    }
  }
  return Result;
}

} // namespace clang::lifetimes
