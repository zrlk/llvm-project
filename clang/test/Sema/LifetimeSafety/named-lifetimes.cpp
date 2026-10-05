// RUN: %clang_cc1 -fsyntax-only -Wlifetime-safety-named-lifetimes \
// RUN:   -verify=expected,undeclared %s
//
// An undeclared lifetime is separable from the rest of the group. Unlike an
// annotation that cannot mean anything, it still denotes something -- a fresh
// lifetime parameter, which is how Crubit reads it -- so it is offered as its
// own subgroup that can be declined while the other checks stay on.
//
// RUN: %clang_cc1 -fsyntax-only -Wlifetime-safety-named-lifetimes \
// RUN:   -Wno-lifetime-safety-undeclared-lifetime -verify=expected %s

// Well-formedness of Crubit-style named lifetime annotations.
//
// The checks run from the lifetime safety analysis, which only runs on
// function definitions, so every function here has a body.

#define $(l) [[clang::annotate_type("lifetime", #l)]]
#define LIFETIME_PARAMS(...) [[clang::annotate("lifetime_params", __VA_ARGS__)]]
#define $a $(a)
#define $b $(b)
#define $c $(c)
#define $static $(static)
#define $unknown $(unknown)

//===----------------------------------------------------------------------===//
// Accepted
//===----------------------------------------------------------------------===//

LIFETIME_PARAMS("a")
int& $a ok(int& $a x) { return x; }

// Writing fewer lifetimes than the type can carry leaves the inner levels
// unconstrained, which is not an error.
LIFETIME_PARAMS("a")
void partial(int** $a p) {}

// The distinguished lifetimes are not parameters and need no declaration.
int& only_static(int& $static x) { return x; }
int& only_unknown(int& $unknown x) { return x; }

// Annotations may live on the declaration alone.
LIFETIME_PARAMS("a") int& split(int& $a x);
int& split(int& x) { return x; }

int& unannotated(int& x) { return x; }

//===----------------------------------------------------------------------===//
// A lifetime must be declared
//===----------------------------------------------------------------------===//

// undeclared-warning@+1 {{lifetime 'b' is not declared by this function}}
int& undeclared(int& $b y) { return y; }

// A lifetime declared on any redeclaration is in scope for all of them.
LIFETIME_PARAMS("a") void declared_elsewhere(int& $a x);
void declared_elsewhere(int& $a x) {}

//===----------------------------------------------------------------------===//
// The type must be able to carry the lifetimes
//===----------------------------------------------------------------------===//

LIFETIME_PARAMS("a")
// expected-warning@+1 {{type 'int' takes no lifetime annotations, but 1 was written}}
void not_a_pointer(int $a x) {}

LIFETIME_PARAMS("a", "b", "c")
// expected-warning@+1 {{type 'int *' takes one lifetime annotation, but 3 were written}}
void too_many(int* $a $b $c p) {}

// A lifetime binds to the level it is written on, so a second one on the same
// level is not absorbed by the level below it. Crubit rejects this the same
// way: `RsTypeKind` gives a pointer at most one lifetime argument.
LIFETIME_PARAMS("a", "b")
// expected-warning@+1 {{type 'int **' takes one lifetime annotation, but 2 were written}}
void stacked(int** $a $b p) {}

// Spelled one per level, the same two lifetimes are fine.
LIFETIME_PARAMS("a", "b")
void per_level(int* $a * $b p) {}

// The diagnostic names the level that overflowed, not the whole type.
LIFETIME_PARAMS("a", "b")
// expected-warning@+1 {{type 'int *' takes one lifetime annotation, but 2 were written}}
void stacked_inner(int* $a $b * p) {}

// A class carries exactly the lifetimes it declares; nothing is inferred from
// its members.
struct LIFETIME_PARAMS("a") Ref { int* p; };
struct Owner { int* p; };

LIFETIME_PARAMS("a")
void takes_ref(Ref $a r) {}

LIFETIME_PARAMS("a", "b")
// expected-warning@+1 {{type 'Ref' takes one lifetime annotation, but 2 were written}}
void takes_ref_too_many(Ref $a $b r) {}

LIFETIME_PARAMS("a")
// expected-warning@+1 {{type 'Owner' takes no lifetime annotations, but 1 was written}}
void takes_owner(Owner $a o) {}

//===----------------------------------------------------------------------===//
// Placement
//===----------------------------------------------------------------------===//

// An annotation after the parameter list attaches to the function type, where
// nothing reads it.
LIFETIME_PARAMS("a")
// expected-warning@+1 {{lifetime annotation after the parameter list applies to the function type and is ignored}}
int& trailing(int& x) $a { return x; }

//===----------------------------------------------------------------------===//
// LIFETIME_PARAMS itself
//===----------------------------------------------------------------------===//

// expected-warning@+2 {{lifetime 'a' is declared more than once}}
// expected-note@+1 {{lifetime 'a' declared here}}
LIFETIME_PARAMS("a", "a")
void duplicate_param(int& $a x) {}

// expected-warning@+2 {{repeated LIFETIME_PARAMS annotation}}
// expected-note@+1 {{previous LIFETIME_PARAMS annotation is here}}
LIFETIME_PARAMS("a") LIFETIME_PARAMS("b")
void repeated_params(int& $a x) {}

//===----------------------------------------------------------------------===//
// Redeclarations must agree
//===----------------------------------------------------------------------===//

// expected-note@+1 {{previous declaration is here}}
LIFETIME_PARAMS("a") int& conflict(int& $a x, int& y);
// expected-warning@+1 {{lifetime annotations on this declaration differ from those on a previous declaration}}
LIFETIME_PARAMS("a") int& conflict(int& x, int& $a y) { return y; }

//===----------------------------------------------------------------------===//
// Arguments must be string literals
//===----------------------------------------------------------------------===//

// expected-warning@+1 {{lifetime annotation argument is not a string literal and is ignored}}
LIFETIME_PARAMS(42)
void non_string_param(int& x) {}

// expected-warning@+1 {{lifetime annotation argument is not a string literal and is ignored}}
void non_string_type(int& [[clang::annotate_type("lifetime", 42)]] x) {}

//===----------------------------------------------------------------------===//
// Templates are not checked
//
// The analysis only visits functions with a CFG, which an uninstantiated
// pattern does not have, and instantiations are skipped because they carry the
// pattern's annotations verbatim. Nothing below is diagnosed today; these cases
// are here so that a change in that behaviour shows up as a test failure.
//===----------------------------------------------------------------------===//

template <typename T>
void tmpl_undeclared(T& $a x) {}

template <int N>
void tmpl_dependent_arg(int& [[clang::annotate_type("lifetime", N)]] x) {}

void instantiate() {
  int i = 0;
  tmpl_undeclared<int>(i);
  tmpl_dependent_arg<3>(i);
}

