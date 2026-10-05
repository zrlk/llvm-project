//===- SignatureCheck.cpp - Named lifetime well-formedness -*----- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "clang/Analysis/Analyses/LifetimeSafety/SignatureCheck.h"
#include "clang/AST/Decl.h"
#include "clang/AST/TypeLoc.h"
#include "clang/Analysis/Analyses/LifetimeSafety/LifetimeAnnotations.h"
#include "clang/Basic/SourceManager.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/StringMap.h"
#include "llvm/ADT/StringSet.h"

namespace clang::lifetimes::internal {
namespace {

/// Validates the annotations written on one declaration of a function.
class SignatureChecker {
public:
  SignatureChecker(const ASTContext &Ctx, LifetimeSafetySemaHelper &Helper)
      : Ctx(Ctx), Helper(Helper) {}

  /// Collects the lifetimes introduced by \p FD, reporting any that are
  /// introduced more than once.
  void collectDeclared(const FunctionDecl *FD) {
    DeclaredLifetimes Declared = getDeclaredLifetimes(Ctx, FD);

    if (Declared.NonLiteralArgLoc.isValid())
      Helper.reportNonLiteralLifetimeArgument(Declared.NonLiteralArgLoc);

    // Clang keeps every `annotate` attribute written on a declaration, and
    // their parameter lists simply concatenate. That is easy to misread, so
    // point out the second one.
    for (size_t I = 1; I < Declared.AttrLocs.size(); ++I)
      Helper.reportRepeatedLifetimeParams(Declared.AttrLocs[I],
                                          Declared.AttrLocs[0]);

    llvm::StringMap<SourceLocation> SeenHere;
    for (const LifetimeUse &Use : Declared.Params) {
      // `$static` and `$unknown` already denote something fixed, so declaring
      // them introduces nothing. Crubit takes the same view from the other
      // direction: `BindingContext::new` pre-seeds both as builtin bindings,
      // so a user declaration of either is redundant at best.
      if (Use.Var.getKind() != LifetimeVar::Kind::Named) {
        Helper.reportReservedLifetimeParam(Use.Loc, Use.Var.getName());
        continue;
      }
      auto [It, Inserted] = SeenHere.try_emplace(Use.Var.getName(), Use.Loc);
      if (!Inserted)
        Helper.reportDuplicateLifetimeParam(Use.Loc, It->second,
                                            Use.Var.getName());
      // A lifetime introduced on any declaration is in scope for all of them.
      InScope.insert(Use.Var.getName());
    }
  }

  /// Checks the types written on \p FD against the lifetimes in scope.
  void checkTypes(const FunctionDecl *FD) {
    const TypeSourceInfo *TSI = FD->getTypeSourceInfo();
    if (!TSI)
      return;
    TypeLoc TL = TSI->getTypeLoc();

    // A lifetime written after the parameter list attaches to the function
    // type. On an instance method that is where the implicit object parameter
    // lives -- the same position `lifetimebound` uses for it -- so the
    // annotation binds to `this`. Crubit reads it the same way, in
    // `rs_bindings_from_cc/importers/function.cc`.
    WrittenLifetimes Trailing = getWrittenLifetimes(Ctx, TL);
    const auto *MD = dyn_cast<CXXMethodDecl>(FD);
    if (MD && MD->isInstance()) {
      if (Trailing.NonLiteralArgLoc.isValid())
        Helper.reportNonLiteralLifetimeArgument(Trailing.NonLiteralArgLoc);
      // The lifetimes are written on the function type but describe `this`, so
      // they are validated against `S *`, which has room for exactly one.
      if (!Trailing.Levels.empty())
        checkLevel(Trailing.Levels.front().Uses, MD->getThisType());
    } else {
      for (const WrittenLifetimeLevel &Level : Trailing.Levels)
        for (const LifetimeUse &Use : Level.Uses)
          Helper.reportLifetimeOnFunctionType(Use.Loc);
    }

    if (auto FTL = TL.getAsAdjusted<FunctionTypeLoc>())
      checkType(FTL.getReturnLoc());

    for (const ParmVarDecl *PVD : FD->parameters())
      if (const TypeSourceInfo *ParmTSI = PVD->getTypeSourceInfo())
        checkType(ParmTSI->getTypeLoc());
  }

private:
  void checkType(TypeLoc TL) {
    if (!TL)
      return;
    WrittenLifetimes Written = getWrittenLifetimes(Ctx, TL);
    if (Written.NonLiteralArgLoc.isValid())
      Helper.reportNonLiteralLifetimeArgument(Written.NonLiteralArgLoc);
    for (const WrittenLifetimeLevel &Level : Written.Levels)
      checkLevel(Level.Uses, Level.Type);
  }

  /// Checks the lifetimes written at one indirection level against \p
  /// LevelType, the type at that level.
  ///
  /// Arity is a property of a single level, not of the type as a whole: a
  /// pointer level carries one lifetime and a class type carries the ones it
  /// declares. Crubit draws the line in the same place -- `RsTypeKind`
  /// rejects a pointer with more than one lifetime argument outright -- so
  /// `int **$a $b` is ill-formed here even though `int *$a *$b` is fine.
  void checkLevel(const LifetimeUseList &Uses, QualType LevelType) {
    if (Uses.empty())
      return;

    // Writing fewer lifetimes than a level can carry is fine: the remaining
    // slots are simply unconstrained. Writing more cannot be given a meaning.
    unsigned Slots = getLifetimeSlotsAtLevel(Ctx, LevelType);
    if (Uses.size() > Slots)
      Helper.reportLifetimeArityMismatch(Uses.front().Loc, LevelType,
                                         Uses.size(), Slots);

    for (const LifetimeUse &Use : Uses) {
      // `$static` and `$unknown` are not parameters and need no introduction.
      if (Use.Var.getKind() != LifetimeVar::Kind::Named)
        continue;
      if (!InScope.contains(Use.Var.getName()))
        Helper.reportUndeclaredLifetime(Use.Loc, Use.Var.getName());
    }
  }

  const ASTContext &Ctx;
  LifetimeSafetySemaHelper &Helper;
  llvm::StringSet<> InScope;
};

/// Reports declarations whose written lifetimes disagree.
///
/// Annotations on types are not merged across redeclarations, so two
/// declarations can silently describe different contracts; whichever one a
/// consumer happens to look at then decides the meaning.
void checkRedeclarationsAgree(const ASTContext &Ctx, const FunctionDecl *FD,
                              LifetimeSafetySemaHelper &Helper) {
  llvm::SmallVector<std::pair<const FunctionDecl *, LifetimeSignature>, 2>
      Annotated;
  for (const FunctionDecl *Redecl : FD->redecls()) {
    LifetimeSignature Sig = getDirectLifetimeSignature(Ctx, Redecl);
    // A declaration that says nothing does not disagree with anything.
    if (!Sig.empty())
      Annotated.emplace_back(Redecl, std::move(Sig));
  }
  if (Annotated.size() < 2)
    return;

  // redecls() is not guaranteed to be in source order, but the diagnostic
  // reads best pointing at the later declaration.
  const SourceManager &SM = Ctx.getSourceManager();
  llvm::stable_sort(Annotated, [&](const auto &A, const auto &B) {
    return SM.isBeforeInTranslationUnit(A.first->getLocation(),
                                        B.first->getLocation());
  });

  const auto &[First, FirstSig] = Annotated.front();
  for (const auto &[Redecl, Sig] : llvm::drop_begin(Annotated))
    if (!haveSameWrittenLifetimes(FirstSig, Sig))
      Helper.reportConflictingLifetimeSignature(Redecl, First);
}

/// Reports disagreement between a function's lifetime signature and the
/// `lifetimebound` attributes written on the same function.
///
/// The two notations overlap: `lifetimebound` on a set of parameters asserts
/// that the result may borrow from their union, while a signature says exactly
/// which parameters the result borrows from. A signature is therefore strictly
/// more precise, and the analysis lets it win at call sites. But
/// `lifetimebound` is still read by other consumers -- Crubit, and Clang's own
/// `-Wdangling` -- so the two must be kept consistent rather than one silently
/// overriding the other.
void checkLifetimeboundAgreement(const ASTContext &Ctx, const FunctionDecl *FD,
                                 LifetimeSafetySemaHelper &Helper,
                                 const LifetimeSafetyOpts &Opts) {
  LifetimeSignature Sig = getLifetimeSignature(Ctx, FD);
  // A return type that names no lifetime states no contract to compare
  // against.
  if (Sig.Return.empty() ||
      Sig.Return.front().getKind() == LifetimeVar::Kind::Elided)
    return;
  LifetimeVar::Kind ReturnKind = Sig.Return.front().getKind();
  llvm::StringRef ReturnLifetime = Sig.Return.front().getName();

  // Find the annotation that spelled the return lifetime so the note can point
  // at it. Type annotations do not merge across redeclarations, so it may have
  // been written on any one of them.
  SourceLocation ReturnLoc;
  for (const FunctionDecl *Redecl : FD->redecls()) {
    const TypeSourceInfo *TSI = Redecl->getTypeSourceInfo();
    if (!TSI)
      continue;
    auto FTL = TSI->getTypeLoc().getAsAdjusted<FunctionTypeLoc>();
    if (!FTL)
      continue;
    WrittenLifetimes Written = getWrittenLifetimes(Ctx, FTL.getReturnLoc());
    if (const LifetimeUse *Use = Written.firstUse()) {
      ReturnLoc = Use->Loc;
      break;
    }
  }

  const FunctionDecl *Merged = getDeclWithMergedLifetimeBoundAttrs(FD);
  if (!Merged)
    Merged = FD;

  unsigned NumParams = Merged->getNumParams() < FD->getNumParams()
                           ? Merged->getNumParams()
                           : FD->getNumParams();

  // An inferred attribute is not something the user wrote, so neither
  // diagnostic below would be actionable.
  auto writtenLifetimeBound = [&](unsigned I) {
    const auto *LB = Merged->getParamDecl(I)->getAttr<LifetimeBoundAttr>();
    return LB && !LB->isImplicit();
  };

  // `$static` and `$unknown` returns borrow from nothing the caller passes in:
  // the first is already valid forever, the second is an explicit opt-out. So
  // a `lifetimebound` anywhere on the same function asserts a relationship the
  // signature denies, and since the signature is what the analysis follows,
  // the attribute would simply be ignored.
  if (ReturnKind != LifetimeVar::Kind::Named) {
    if (Opts.CheckLifetimeboundConflict) {
      for (unsigned I = 0; I != NumParams; ++I)
        if (writtenLifetimeBound(I))
          Helper.reportLifetimeboundDistinguishedConflict(
              FD->getParamDecl(I), /*MD=*/nullptr, /*IsObjectParam=*/false,
              ReturnLifetime, ReturnLoc);
      if (const auto *MD = dyn_cast<CXXMethodDecl>(FD);
          MD && MD->isInstance() && getImplicitObjectParamLifetimeBoundAttr(FD))
        Helper.reportLifetimeboundDistinguishedConflict(
            /*PVD=*/nullptr, MD, /*IsObjectParam=*/true, ReturnLifetime,
            ReturnLoc);
    }
    return;
  }

  for (unsigned I = 0, E = Sig.Params.size(); I != E; ++I) {
    if (I >= NumParams)
      break;
    const LifetimeList &Param = Sig.Params[I];
    // A parameter that names no lifetime of its own is simply unconstrained by
    // the signature, and says nothing either way about `lifetimebound`.
    if (Param.empty() || Param.front().getKind() != LifetimeVar::Kind::Named)
      continue;

    bool IsBound = writtenLifetimeBound(I);

    // Diagnose on the declaration under analysis rather than on whichever one
    // happened to carry the merged attributes.
    const ParmVarDecl *PVD = FD->getParamDecl(I);

    if (Param.front().getName() == ReturnLifetime) {
      if (!IsBound && Opts.SuggestNamedLifetimebound)
        Helper.suggestLifetimeboundForNamedLifetime(PVD, ReturnLifetime,
                                                    ReturnLoc);
    } else if (IsBound && Opts.CheckLifetimeboundConflict) {
      Helper.reportLifetimeboundLifetimeConflict(PVD, Param.front().getName(),
                                                 ReturnLifetime, ReturnLoc);
    }
  }

  // The implicit object parameter, whose lifetime is written after the
  // parameter list. This is the case that matters most: a trailing lifetime
  // that disagrees with the return suppresses the flow `lifetimebound` would
  // otherwise have contributed, which is the one way a signature can leave the
  // result *less* constrained than the attribute alone would have.
  const auto *MD = dyn_cast<CXXMethodDecl>(FD);
  if (!MD || !MD->isInstance() || Sig.FunctionType.empty())
    return;
  const LifetimeVar &ThisLifetime = Sig.FunctionType.front();
  if (ThisLifetime.getKind() != LifetimeVar::Kind::Named)
    return;

  // Use the attribute rather than `implicitObjectParamIsLifetimeBound`, which
  // also reports the implicit rule for assignment operators; that is not
  // something the user wrote, so neither diagnostic would be actionable.
  bool IsBound = getImplicitObjectParamLifetimeBoundAttr(FD) != nullptr;

  if (ThisLifetime.getName() == ReturnLifetime) {
    if (!IsBound && Opts.SuggestNamedLifetimebound)
      Helper.suggestLifetimeboundForImplicitThis(MD, ReturnLifetime, ReturnLoc);
  } else if (IsBound && Opts.CheckLifetimeboundConflict) {
    Helper.reportLifetimeboundConflictOnImplicitThis(MD, ThisLifetime.getName(),
                                                     ReturnLifetime, ReturnLoc);
  }
}

} // namespace

void checkNamedLifetimes(AnalysisDeclContext &AC,
                         LifetimeSafetySemaHelper *SemaHelper,
                         const LifetimeSafetyOpts &Opts) {
  if (!SemaHelper)
    return;
  const auto *FD = dyn_cast_if_present<FunctionDecl>(AC.getDecl());
  if (!FD)
    return;
  // `annotate_type` arguments are not substituted when a template is
  // instantiated, so an instantiation carries the pattern's annotations
  // verbatim, at the pattern's source locations. Checking instantiations would
  // therefore repeat the same diagnostic once per instantiation.
  //
  // TODO: This leaves templates unchecked entirely, since the analysis never
  // visits an uninstantiated pattern (its body is dependent, so it has no CFG).
  // Catching these needs a hook that runs on the pattern itself.
  if (FD->isTemplateInstantiation())
    return;

  const ASTContext &Ctx = AC.getASTContext();

  if (Opts.CheckNamedLifetimes) {
    SignatureChecker Checker(Ctx, *SemaHelper);

    // Lifetimes introduced on any declaration are in scope for all of them, so
    // they must all be collected before any use is checked.
    for (const FunctionDecl *Redecl : FD->redecls())
      Checker.collectDeclared(Redecl);
    for (const FunctionDecl *Redecl : FD->redecls())
      Checker.checkTypes(Redecl);

    checkRedeclarationsAgree(Ctx, FD, *SemaHelper);
  }

  if (Opts.CheckLifetimeboundConflict || Opts.SuggestNamedLifetimebound)
    checkLifetimeboundAgreement(Ctx, FD, *SemaHelper, Opts);
}

} // namespace clang::lifetimes::internal
