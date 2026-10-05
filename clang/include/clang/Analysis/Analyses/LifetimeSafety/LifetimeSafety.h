//===- LifetimeSafety.h - C++ Lifetime Safety Analysis -*----------- C++-*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file defines the main entry point and orchestrator for the C++ Lifetime
// Safety Analysis. It coordinates the entire analysis pipeline: fact
// generation, loan propagation, live origins analysis, and enforcement of
// lifetime safety policy.
//
// The analysis is based on the concepts of "origins" and "loans" to track
// pointer lifetimes and detect issues like use-after-free and dangling
// pointers. See the RFC for more details:
// https://discourse.llvm.org/t/rfc-intra-procedural-lifetime-analysis-in-clang/86291
//
//===----------------------------------------------------------------------===//
#ifndef LLVM_CLANG_ANALYSIS_ANALYSES_LIFETIMESAFETY_H
#define LLVM_CLANG_ANALYSIS_ANALYSES_LIFETIMESAFETY_H

#include "clang/AST/Decl.h"
#include "clang/Analysis/Analyses/LifetimeSafety/Facts.h"
#include "clang/Analysis/Analyses/LifetimeSafety/LifetimeStats.h"
#include "clang/Analysis/Analyses/LifetimeSafety/LiveOrigins.h"
#include "clang/Analysis/Analyses/LifetimeSafety/LoanPropagation.h"
#include "clang/Analysis/Analyses/LifetimeSafety/MovedLoans.h"
#include "clang/Analysis/Analyses/LifetimeSafety/Origins.h"
#include "clang/Analysis/AnalysisDeclContext.h"
#include "llvm/ADT/PointerUnion.h"
#include <cstddef>
#include <memory>

namespace clang::lifetimes {

struct LifetimeSafetyOpts {
  /// Maximum number of CFG blocks to analyze. Functions with larger CFGs will
  /// be skipped.
  size_t MaxCFGBlocks;

  /// Whether to suggest lifetime annotations.
  bool SuggestAnnotations;

  bool CheckNoescapeViolations;
  bool CheckLifetimeboundViolations;
  bool CheckMisplacedLifetimebound;
  bool CheckInapplicableLifetimebound;

  /// Whether to check that named lifetime annotations (`$a`, `LIFETIME_PARAMS`)
  /// are well formed.
  bool CheckNamedLifetimes;

  /// Whether to check that a function body honours the lifetimes its signature
  /// declares.
  bool CheckNamedLifetimeViolations;

  /// Whether to report a parameter marked `lifetimebound` whose named lifetime
  /// differs from the one the return type declares.
  bool CheckLifetimeboundConflict;

  /// Whether to suggest `lifetimebound` on a parameter that shares the return
  /// type's named lifetime but is not marked.
  bool SuggestNamedLifetimebound;
};

/// Enum to track functions visible across or within TU.
enum class WarningScope {
  CrossTU, // For warnings on declarations visible across Translation Units.
  IntraTU  // For warnings on functions local to a Translation Unit.
};

/// Abstract interface for operations requiring Sema access.
///
/// This class exists to break a circular dependency: the LifetimeSafety
/// analysis target cannot directly depend on clangSema (which would create the
/// cycle: clangSema -> clangAnalysis -> clangAnalysisLifetimeSafety ->
/// clangSema).
///
/// Instead, this interface is implemented in AnalysisBasedWarnings.cpp (part of
/// clangSema), allowing the analysis to report diagnostics and modify the AST
/// through Sema without introducing a circular dependency.
class LifetimeSafetySemaHelper {
public:
  LifetimeSafetySemaHelper() = default;
  virtual ~LifetimeSafetySemaHelper() = default;

  virtual void reportUseAfterScope(const Expr *IssueExpr, const Expr *UseExpr,
                                   const Expr *MovedExpr,
                                   SourceLocation FreeLoc,
                                   llvm::ArrayRef<const Expr *> ExprChain) {}

  // TODO: Pass the expiry location and aliasing chain like
  // reportUseAfterScope.
  virtual void reportUseAfterReturn(const Expr *IssueExpr,
                                    const Expr *ReturnExpr,
                                    const Expr *MovedExpr) {}

  virtual void reportDanglingField(const Expr *IssueExpr,
                                   const FieldDecl *Field,
                                   const Expr *MovedExpr,
                                   bool IsCapturedByLambda,
                                   SourceLocation ExpiryLoc) {}

  virtual void reportDanglingGlobal(const Expr *IssueExpr,
                                    const VarDecl *DanglingGlobal,
                                    const Expr *MovedExpr,
                                    SourceLocation ExpiryLoc,
                                    bool IsMain = false) {}

  // Reports when a reference/iterator is used after the container operation
  // that invalidated it.
  virtual void
  reportUseAfterInvalidation(const Expr *IssueExpr, const Expr *UseExpr,
                             const Expr *InvalidationExpr,
                             llvm::ArrayRef<const Expr *> ExprChain) {}
  virtual void
  reportUseAfterInvalidation(const ParmVarDecl *PVD, const Expr *UseExpr,
                             const Expr *InvalidationExpr,
                             llvm::ArrayRef<const Expr *> ExprChain) {}
  virtual void reportInvalidatedField(const Expr *IssueExpr,
                                      const FieldDecl *Field,
                                      const Expr *InvalidationExpr) {}
  virtual void reportInvalidatedField(const ParmVarDecl *PVD,
                                      const FieldDecl *Field,
                                      const Expr *InvalidationExpr) {}
  virtual void reportInvalidatedGlobal(const Expr *IssueExpr,
                                       const VarDecl *Global,
                                       const Expr *InvalidationExpr) {}
  virtual void reportInvalidatedGlobal(const ParmVarDecl *PVD,
                                       const VarDecl *Global,
                                       const Expr *InvalidationExpr) {}

  using EscapingTarget =
      llvm::PointerUnion<const Expr *, const FieldDecl *, const VarDecl *>;

  // Suggests lifetime bound annotations for function parameters.
  virtual void suggestLifetimeboundToParmVar(WarningScope Scope,
                                             const ParmVarDecl *ParmToAnnotate,
                                             EscapingTarget Target) {}

  // Reports misuse of [[clang::noescape]] when parameter escapes through return
  virtual void reportNoescapeViolation(const ParmVarDecl *ParmWithNoescape,
                                       const Expr *EscapeExpr) {}
  // Reports misuse of [[clang::noescape]] when parameter escapes through field
  virtual void reportNoescapeViolation(const ParmVarDecl *ParmWithNoescape,
                                       const FieldDecl *EscapeField) {}
  // Reports misuse of [[clang::noescape]] when parameter escapes through
  // assignment to a global variable
  virtual void reportNoescapeViolation(const ParmVarDecl *ParmWithNoescape,
                                       const VarDecl *EscapeGlobal) {}

  // Reports misuse of [[clang::lifetimebound]] when parameter doesn't escape
  // through return.
  virtual void
  reportLifetimeboundViolation(const ParmVarDecl *ParmWithLifetimebound) {}

  // Reports misuse of [[clang::lifetimebound]] when implicit this parameter
  // doesn't escape through return.
  virtual void
  reportLifetimeboundViolation(const CXXMethodDecl *MDWithLifetimebound) {}

  // Reports a member function definition that has [[clang::lifetimebound]] on
  // the implicit this parameter when the canonical declaration does not.
  virtual void reportMisplacedLifetimebound(WarningScope Scope,
                                            const CXXMethodDecl *FDef,
                                            const CXXMethodDecl *FDecl) {}

  // Reports a function definition parameter that has [[clang::lifetimebound]]
  // when the corresponding parameter in the canonical declaration.
  virtual void reportMisplacedLifetimebound(WarningScope Scope,
                                            const ParmVarDecl *PVDDef,
                                            const ParmVarDecl *PVDDecl) {}

  virtual void reportInapplicableLifetimebound(const ParmVarDecl *PVD) {}

  // Suggests lifetime bound annotations for implicit this.
  virtual void suggestLifetimeboundToImplicitThis(WarningScope Scope,
                                                  const CXXMethodDecl *MD,
                                                  const Expr *EscapeExpr) {}

  // Adds inferred lifetime bound attribute for implicit this to its
  // TypeSourceInfo.
  virtual void addLifetimeBoundToImplicitThis(const CXXMethodDecl *MD) {}

  //===--------------------------------------------------------------------===//
  // Named lifetimes
  //
  // These report on the well-formedness of the annotation itself, so they take
  // source locations rather than expressions: the finding is a property of the
  // declaration, not of anything in the body.
  //===--------------------------------------------------------------------===//

  /// Reports \p Found lifetimes written on a type that can only carry
  /// \p Expected of them. \p Expected of zero means the type cannot carry a
  /// lifetime at all.
  virtual void reportLifetimeArityMismatch(SourceLocation Loc, QualType T,
                                           unsigned Found, unsigned Expected) {}

  /// Reports a lifetime that is used but never introduced by `LIFETIME_PARAMS`.
  virtual void reportUndeclaredLifetime(SourceLocation Loc,
                                        llvm::StringRef Name) {}

  /// Reports a lifetime written after the parameter list, where it attaches to
  /// the function type and is therefore ignored.
  virtual void reportLifetimeOnFunctionType(SourceLocation Loc) {}

  /// Reports a lifetime introduced more than once by `LIFETIME_PARAMS`.
  virtual void reportDuplicateLifetimeParam(SourceLocation Loc,
                                            SourceLocation PrevLoc,
                                            llvm::StringRef Name) {}

  /// Reports a second `LIFETIME_PARAMS` on the same declaration.
  virtual void reportRepeatedLifetimeParams(SourceLocation Loc,
                                            SourceLocation PrevLoc) {}

  /// Reports an annotation argument that is not a string literal, which
  /// includes template-dependent arguments: Clang does not substitute
  /// `annotate_type` arguments when a template is instantiated.
  virtual void reportNonLiteralLifetimeArgument(SourceLocation Loc) {}

  /// Reports a definition whose written lifetimes disagree with those on a
  /// previous declaration. Type annotations do not merge across
  /// redeclarations, so the two would otherwise silently describe different
  /// contracts.
  virtual void reportConflictingLifetimeSignature(const FunctionDecl *FDef,
                                                  const FunctionDecl *FDecl) {}

  /// Reports a lifetime introduced by `LIFETIME_PARAMS` that is one of the
  /// distinguished names. `$static` and `$unknown` mean something fixed, so a
  /// declaration of them cannot introduce anything.
  virtual void reportReservedLifetimeParam(SourceLocation Loc,
                                           llvm::StringRef Name) {}

  /// Reports a returned value that borrows from lifetime \p Found where the
  /// return type declares \p Required.
  virtual void reportNamedLifetimeViolation(const Expr *ReturnExpr,
                                            llvm::StringRef Found,
                                            llvm::StringRef Required) {}

  /// Reports a returned value that borrows from the caller's storage where the
  /// return type declares `$static`. Unlike a named lifetime, `$static` is not
  /// satisfied by an arbitrary caller-supplied position.
  virtual void reportStaticReturnViolation(const Expr *ReturnExpr) {}

  /// Reports an argument passed to a parameter declaring `$static` whose
  /// storage is not known to live that long. \p PVD is null for the implicit
  /// object argument.
  virtual void reportStaticArgumentViolation(const Expr *ArgExpr,
                                             const ParmVarDecl *PVD) {}

  /// Reports a parameter marked `lifetimebound` -- asserting the result may
  /// borrow from it -- whose named lifetime differs from the one the return
  /// type declares. \p ReturnLoc points at the return type's annotation.
  virtual void reportLifetimeboundLifetimeConflict(
      const ParmVarDecl *PVD, llvm::StringRef ParamLifetime,
      llvm::StringRef ReturnLifetime, SourceLocation ReturnLoc) {}

  /// Suggests `lifetimebound` on a parameter that already shares the return
  /// type's named lifetime \p Lifetime. \p ReturnLoc points at the return
  /// type's annotation.
  virtual void suggestLifetimeboundForNamedLifetime(const ParmVarDecl *PVD,
                                                    llvm::StringRef Lifetime,
                                                    SourceLocation ReturnLoc) {}

  /// As above, for the implicit object parameter, whose lifetime is written
  /// after the parameter list.
  virtual void reportLifetimeboundConflictOnImplicitThis(
      const CXXMethodDecl *MD, llvm::StringRef ThisLifetime,
      llvm::StringRef ReturnLifetime, SourceLocation ReturnLoc) {}

  virtual void suggestLifetimeboundForImplicitThis(const CXXMethodDecl *MD,
                                                   llvm::StringRef Lifetime,
                                                   SourceLocation ReturnLoc) {}

  /// Reports a `lifetimebound` position on a function whose return declares
  /// `$static` or `$unknown`. Neither borrows from anything the caller passes
  /// in, so the two annotations describe different contracts; the signature is
  /// the one the analysis follows. \p IsObjectParam selects the implicit
  /// object parameter, in which case \p PVD is null.
  virtual void reportLifetimeboundDistinguishedConflict(
      const ParmVarDecl *PVD, const CXXMethodDecl *MD, bool IsObjectParam,
      llvm::StringRef ReturnLifetime, SourceLocation ReturnLoc) {}
};

/// The main entry point for the analysis.
void runLifetimeSafetyAnalysis(AnalysisDeclContext &AC,
                               LifetimeSafetySemaHelper *SemaHelper,
                               const LifetimeSafetyOpts &Opts,
                               LifetimeSafetyStats &Stats, bool CollectStats);

namespace internal {

void collectLifetimeStats(AnalysisDeclContext &AC, OriginManager &OM,
                          LifetimeSafetyStats &Stats);

/// An object to hold the factories for immutable collections, ensuring
/// that all created states share the same underlying memory management.
struct LifetimeFactory {
  OriginLoanMap::Factory OriginMapFactory;
  LoanSet::Factory LoanSetFactory;
  MovedLoansMap::Factory MovedLoansMapFactory;
  LivenessMap::Factory LivenessMapFactory;
};

/// Running the lifetime safety analysis and querying its results. It
/// encapsulates the various dataflow analyses.
class LifetimeSafetyAnalysis {
public:
  LifetimeSafetyAnalysis(AnalysisDeclContext &AC,
                         LifetimeSafetySemaHelper *SemaHelper,
                         const LifetimeSafetyOpts &LSOpts);

  void run();

  /// \note These are provided only for testing purposes.
  LoanPropagationAnalysis &getLoanPropagation() const {
    return *LoanPropagation;
  }
  LiveOriginsAnalysis &getLiveOrigins() const { return *LiveOrigins; }
  FactManager &getFactManager() { return *FactMgr; }

private:
  AnalysisDeclContext &AC;
  LifetimeSafetySemaHelper *SemaHelper;
  const LifetimeSafetyOpts LSOpts;
  LifetimeFactory Factory;
  std::unique_ptr<FactManager> FactMgr;
  std::unique_ptr<LiveOriginsAnalysis> LiveOrigins;
  std::unique_ptr<LoanPropagationAnalysis> LoanPropagation;
  std::unique_ptr<MovedLoansAnalysis> MovedLoans;
};
} // namespace internal
} // namespace clang::lifetimes

#endif // LLVM_CLANG_ANALYSIS_ANALYSES_LIFETIMESAFETY_H
