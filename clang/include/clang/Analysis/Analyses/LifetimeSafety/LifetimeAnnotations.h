//===- LifetimeAnnotations.h -  -*--------------- C++--------------------*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
// Helper functions to inspect and infer lifetime annotations.
//===----------------------------------------------------------------------===//
#ifndef LLVM_CLANG_ANALYSIS_ANALYSES_LIFETIMEANNOTATIONS_H
#define LLVM_CLANG_ANALYSIS_ANALYSES_LIFETIMEANNOTATIONS_H

#include "clang/AST/DeclCXX.h"
#include "clang/AST/TypeLoc.h"
#include "clang/Basic/SourceLocation.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/PointerUnion.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/raw_ostream.h"
#include <optional>

namespace clang {
class ASTContext;
class LifetimeBoundAttr;
} // namespace clang

namespace clang ::lifetimes {

// This function is needed because Decl::isInStdNamespace will return false for
// iterators in some STL implementations due to them being defined in a
// namespace outside of the std namespace.
bool isInStlNamespace(const Decl *D);

bool isPointerLikeType(QualType QT);

/// Returns the most recent declaration of the method to ensure all
/// lifetime-bound attributes from redeclarations are considered.
const FunctionDecl *getDeclWithMergedLifetimeBoundAttrs(const FunctionDecl *FD);

/// Returns the most recent declaration of the method to ensure all
/// lifetime-bound attributes from redeclarations are considered.
const CXXMethodDecl *
getDeclWithMergedLifetimeBoundAttrs(const CXXMethodDecl *CMD);

// Return true if this is an "normal" assignment operator.
// We assume that a normal assignment operator always returns *this, that is,
// an lvalue reference that is the same type as the implicit object parameter
// (or the LHS for a non-member operator==).
bool isNormalAssignmentOperator(const FunctionDecl *FD);

/// Returns true if this is an assignment operator where the parameter
/// has the lifetimebound attribute.
bool isAssignmentOperatorLifetimeBound(const CXXMethodDecl *CMD);

/// Returns the lifetimebound attribute for the implicit this parameter, if it
/// exists on the current type.
const LifetimeBoundAttr *
getDirectImplicitObjectLifetimeBoundAttr(const FunctionDecl *FD);

/// Returns the lifetimebound attribute for the implicit this parameter, if it
/// exists on any redeclaration.
const LifetimeBoundAttr *
getImplicitObjectParamLifetimeBoundAttr(const FunctionDecl *FD);

/// Returns true if the implicit object parameter (this) should be considered
/// lifetimebound, either due to an explicit lifetimebound attribute on the
/// method or because it's a normal assignment operator.
bool implicitObjectParamIsLifetimeBound(const FunctionDecl *FD);

using LifetimeBoundParamInfo =
    llvm::PointerUnion<const ParmVarDecl *, const CXXMethodDecl *>;

/// Stores the callee and normalized arguments for a function call.
struct FunctionCallInfo {
  const FunctionDecl *FD = nullptr;
  llvm::SmallVector<const Expr *, 4> Args;

  explicit FunctionCallInfo(const Expr *Call);
};

/// Returns the parameter corresponding to argument I when the argument should
/// be tracked for lifetime safety.
std::optional<LifetimeBoundParamInfo>
getTrackedArgInfo(const FunctionDecl *FD, llvm::ArrayRef<const Expr *> Args,
                  unsigned I);

/// Returns lifetime safety tracking info for the call argument containing
/// Source.
std::optional<LifetimeBoundParamInfo>
getTrackingInfoForCallArg(const Expr *Call, const Expr *Source);

// Returns true if the implicit object argument (this) of a method call should
// be tracked for GSL lifetime analysis. This applies to STL methods that return
// pointers or references that depend on the lifetime of the object, such as
// container iterators (begin, end), data accessors (c_str, data, get),
// element accessors (operator[], operator*, front, back, at), or propagating
// operations (operator+, operator-, operator++, operator--).
bool shouldTrackImplicitObjectArg(const Expr &ImplicitObjectArgument,
                                  const CXXMethodDecl *Callee,
                                  bool RunningUnderLifetimeSafety);

// Returns true if the first argument of a free function should be tracked for
// GSL lifetime analysis. This applies to STL free functions that take a pointer
// to a GSL Owner or Pointer and return a pointer or reference that depends on
// the lifetime of the argument, such as std::begin, std::data, std::get, or
// std::any_cast.
bool shouldTrackFirstArgument(const FunctionDecl *FD);

// Returns true if the second argument of a free function should be tracked for
// lifetime analysis. This applies to free operator functions that take a
// GSL Pointer as their second argument.
bool shouldTrackSecondArgument(const FunctionDecl *FD);

// Tells whether the type is annotated with [[gsl::Pointer]].
bool isGslPointerType(QualType QT);
// Tells whether the type is annotated with [[gsl::Owner]].
bool isGslOwnerType(QualType QT);
bool isGslOwnerType(const CXXRecordDecl *RD);

// Tells whether the given constructor belongs to an Owner type and the
// parameter is of pointer type. This is useful to disable inference on owning
// pointers being captured by owners.
bool isOwnerPtrCtor(const CXXConstructorDecl *Ctor, const ParmVarDecl *PVD);

// Returns true if the given method is std::unique_ptr::release().
// This is treated as a move in lifetime analysis to avoid false-positives
// when ownership is manually transferred.
bool isUniquePtrRelease(const CXXMethodDecl &MD);

// Returns true if the given method invalidates references tracked by lifetime
// analysis (e.g. vector::push_back). Methods that only invalidate iterators but
// not references (e.g. unordered_map::emplace) are not considered invalidating
// here.
//
// Container invalidation rules are based on:
// https://en.cppreference.com/w/cpp/container#Iterator_invalidation
bool isInvalidationMethod(const CXXMethodDecl &MD);

// Returns true if the function destroys its first argument
// (e.g., destructors via implicit 'this', std::destroy_at).
bool destructsFirstArg(const FunctionDecl &FD);

/// Returns true for standard library callable wrappers (e.g., std::function)
/// that can propagate the stored lambda's origins.
bool isStdCallableWrapperType(const CXXRecordDecl *RD);

/// Returns true for std reference-cast builtins (e.g., std::move). Their result
/// refers to the same object as the argument, so all origins propagate from
/// argument to result.
bool isStdReferenceCast(const FunctionDecl *FD);

//===----------------------------------------------------------------------===//
// Named lifetimes
//
// Support for Crubit-style named lifetime annotations, spelled:
//
//   #define $(l) [[clang::annotate_type("lifetime", #l)]]
//   #define LIFETIME_PARAMS(...) [[clang::annotate("lifetime_params", \
//                                                  __VA_ARGS__)]]
//
//   LIFETIME_PARAMS("a")
//   int& $a f(int& $a x, int& $b y);
//
// These are currently only read and reported; they do not yet influence the
// dataflow analysis.
//===----------------------------------------------------------------------===//

/// The `annotate_type` category identifying a named lifetime.
inline constexpr llvm::StringLiteral LifetimeAnnotationCategory = "lifetime";

/// The `annotate` category identifying a declaration's lifetime parameters.
inline constexpr llvm::StringLiteral LifetimeParamsAnnotationCategory =
    "lifetime_params";

/// A single lifetime as written in an annotation, e.g. the `a` of `$a`.
///
/// Two names are distinguished: `$static` denotes storage that outlives
/// everything, and `$unknown` is an escape hatch asserting that no lifetime
/// applies.
class LifetimeVar {
public:
  enum class Kind : uint8_t {
    Named,   ///< An ordinary lifetime parameter, e.g. `$a`.
    Static,  ///< The distinguished `$static` lifetime.
    Unknown, ///< The distinguished `$unknown` lifetime.
    Elided,  ///< A slot the author left unannotated.
  };

  LifetimeVar() = default;
  explicit LifetimeVar(llvm::StringRef Name);

  /// A slot that carries no written lifetime.
  ///
  /// Levels of a type are annotated independently, so a list has to be able to
  /// say "nothing was written here" in order to keep the levels that follow it
  /// aligned. Without this, `int* $a *` and `int** $a` would both elaborate to
  /// [`$a`] and the annotation would be attributed to the wrong level.
  static LifetimeVar elided() {
    LifetimeVar LV;
    LV.K = Kind::Elided;
    return LV;
  }

  Kind getKind() const { return K; }
  bool isStatic() const { return K == Kind::Static; }
  bool isUnknown() const { return K == Kind::Unknown; }
  bool isElided() const { return K == Kind::Elided; }

  /// The lifetime name as written, without the leading `$`.
  llvm::StringRef getName() const { return Name; }

  bool operator==(const LifetimeVar &Other) const {
    return K == Other.K && Name == Other.Name;
  }
  bool operator!=(const LifetimeVar &Other) const { return !(*this == Other); }

  /// Prints the lifetime in its source spelling, e.g. `$a`.
  void dump(llvm::raw_ostream &OS) const;

private:
  llvm::StringRef Name;
  Kind K = Kind::Named;
};

/// The lifetimes written on one type, ordered outermost-slot-first.
///
/// The ordering matches the levels of an `OriginList`, so the two can be
/// zipped: for `int* $b * $a p` the list is [`$a`, `$b`], corresponding to the
/// origin for `p` and the origin for `*p` respectively.
///
/// Levels are annotated independently, and an unannotated level occupies its
/// slot as `LifetimeVar::elided()` so that the levels after it stay aligned.
/// `int* $a *` is therefore [elided, `$a`] and not [`$a`]. Trailing elided
/// slots carry no information and are dropped, so a type with nothing written
/// on it still yields an empty list.
using LifetimeList = llvm::SmallVector<LifetimeVar, 2>;

/// The lifetime annotations written on a function, as spelled in the source.
struct LifetimeSignature {
  /// Lifetimes declared by `LIFETIME_PARAMS(...)` on the function.
  LifetimeList Declared;

  /// Lifetimes written on the function type itself, i.e. after the parameter
  /// list, as in `int& f() $a`.
  ///
  /// This is the position `[[clang::lifetimebound]]` uses for the implicit
  /// object parameter. Its meaning for named lifetimes is not yet settled, so
  /// it is collected separately rather than folded into the return lifetimes.
  LifetimeList FunctionType;

  /// Lifetimes written on the return type, as in `int& $a f()`.
  LifetimeList Return;

  /// Lifetimes written on each explicit parameter, indexed by parameter.
  llvm::SmallVector<LifetimeList, 4> Params;

  /// Whether any lifetime annotation at all was written on this function.
  bool empty() const;

  void dump(llvm::raw_ostream &OS, const FunctionDecl *FD) const;
};

/// Collects the lifetimes written at the outermost level of \p QT, and returns
/// the type with that level's annotation sugar removed.
///
/// This peels `MacroQualifiedType` (which wraps every macro-spelled attribute)
/// and `AttributedType`, and does not look through any other sugar, so the
/// caller stays in control of which indirection level is being inspected.
QualType getExplicitLifetimesAtLevel(const ASTContext &Ctx, QualType QT,
                                     LifetimeList &Out);

/// Collects the lifetimes written across every indirection level of \p QT,
/// outermost first.
///
/// The levels walked mirror those of `OriginManager::buildListForType`, so the
/// result can be zipped against an `OriginList`.
LifetimeList getExplicitLifetimes(const ASTContext &Ctx, QualType QT);

/// Reads the lifetimes declared by `LIFETIME_PARAMS(...)` on \p D.
///
/// \note Clang drops a second `annotate` attribute carrying the same category,
/// so only the first `LIFETIME_PARAMS` on a declaration survives to here.
LifetimeList getDeclaredLifetimeParams(const ASTContext &Ctx, const Decl *D);

/// Computes the lifetime signature written on \p FD.
///
/// Annotations on types do not merge across redeclarations, so all
/// redeclarations (and the template instantiation pattern) are scanned.
LifetimeSignature getLifetimeSignature(const ASTContext &Ctx,
                                       const FunctionDecl *FD);

/// Reads the signature spelled on one particular declaration of \p FD, without
/// consulting any redeclaration.
LifetimeSignature getDirectLifetimeSignature(const ASTContext &Ctx,
                                             const FunctionDecl *FD);

/// Compares two signatures ignoring `Declared`, which is an inheritable
/// declaration attribute and therefore already shared by all redeclarations.
bool haveSameWrittenLifetimes(const LifetimeSignature &A,
                              const LifetimeSignature &B);

//===----------------------------------------------------------------------===//
// Locations
//
// The annotations are always written through macros, so the `Attr` hanging off
// an `AttributedType` reports the location of the *macro definition*, not of
// the use. Worse, `AttributedType` nodes are uniqued in a `FoldingSet` that
// includes the `Attr`, so two identical annotations in different places share
// one node. Diagnostics must therefore go through `TypeLoc`, which records the
// macro expansion location per occurrence.
//===----------------------------------------------------------------------===//

/// A lifetime as written, together with the location to point a diagnostic at.
struct LifetimeUse {
  LifetimeVar Var;

  /// The location of the annotation as written. For a macro-spelled annotation
  /// (the only spelling in practice) this is the expansion location, i.e. the
  /// `$a` token itself.
  SourceLocation Loc;
};

using LifetimeUseList = llvm::SmallVector<LifetimeUse, 2>;

/// The lifetimes written at one indirection level of a type.
struct WrittenLifetimeLevel {
  /// The type at this level, with this level's annotation sugar removed.
  ///
  /// This is the type an arity diagnostic should name: `int **` for the outer
  /// level of `int **`, and `int *` for its inner one.
  QualType Type;

  /// The lifetimes written at this level, in source order.
  LifetimeUseList Uses;
};

/// Everything the well-formedness checks need to know about one written type.
///
/// Lifetimes are kept grouped by level rather than flattened, because each
/// level is annotated independently and carries its own capacity. `int **$a $b`
/// writes two lifetimes on a level that can hold only one, even though the type
/// as a whole has room for two; a flat list cannot tell that apart from the
/// well-formed `int *$a *$b`.
struct WrittenLifetimes {
  /// One entry per indirection level, outermost first.
  llvm::SmallVector<WrittenLifetimeLevel, 2> Levels;

  /// Set if some annotation argument could not be reduced to a string literal.
  ///
  /// This is how a template-dependent argument shows up: Clang does not
  /// substitute `annotate_type` arguments when instantiating a template, so
  /// such an annotation can never mean anything.
  SourceLocation NonLiteralArgLoc;

  /// The first lifetime written anywhere in the type, or null if there is none.
  const LifetimeUse *firstUse() const {
    for (const WrittenLifetimeLevel &Level : Levels)
      if (!Level.Uses.empty())
        return &Level.Uses.front();
    return nullptr;
  }
};

/// Collects the lifetimes written on \p TL, with source locations.
///
/// The levels walked mirror those of `getExplicitLifetimes`, so the two agree
/// on which annotations belong to the type.
WrittenLifetimes getWrittenLifetimes(const ASTContext &Ctx, TypeLoc TL);

/// The number of lifetimes the outermost level of \p QT can carry.
///
/// A pointer or reference level carries one, and a class type carries as many
/// as its definition declares with `LIFETIME_PARAMS`. Note that no lifetimes
/// are inferred: a class that merely *contains* references still carries none
/// unless it says otherwise.
///
/// This is deliberately per-level rather than a total over the whole type: a
/// lifetime binds to the level it is written on, so `int **$a $b` is ill-formed
/// even though `int **` has two levels between them.
unsigned getLifetimeSlotsAtLevel(const ASTContext &Ctx, QualType QT);

/// The `LIFETIME_PARAMS` declared on a declaration, with source locations.
struct DeclaredLifetimes {
  /// The declared lifetimes, in source order, concatenated across all
  /// `LIFETIME_PARAMS` attributes on the declaration.
  LifetimeUseList Params;

  /// The location of each `LIFETIME_PARAMS` attribute, in source order.
  llvm::SmallVector<SourceLocation, 1> AttrLocs;

  /// Set if some argument could not be reduced to a string literal.
  SourceLocation NonLiteralArgLoc;
};

/// Reads the `LIFETIME_PARAMS` declared on \p D, with source locations.
DeclaredLifetimes getDeclaredLifetimes(const ASTContext &Ctx, const Decl *D);

} // namespace clang::lifetimes

#endif // LLVM_CLANG_ANALYSIS_ANALYSES_LIFETIMEANNOTATIONS_H
