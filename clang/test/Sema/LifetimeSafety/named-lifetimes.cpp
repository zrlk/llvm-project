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
// The checks on functions run from the lifetime safety analysis, which only
// runs on function definitions, so every function here has a body. Classes
// are checked when their definition is complete.

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

// A class type takes all of its lifetimes or none: they bind positionally, so
// a partial list would silently leave the rest open. `$unknown` spells "don't
// care" for one of them. Aliases are held to the count of the class they name.
struct LIFETIME_PARAMS("a", "b") Two {};
using TwoAlias = Two;
LIFETIME_PARAMS("a")
// expected-warning@+1 {{type 'Two' takes 2 lifetime annotations, but 1 was written}}
void takes_two_partial(Two $a t) {}
LIFETIME_PARAMS("a")
// expected-warning@+1 {{type 'TwoAlias' (aka 'Two') takes 2 lifetime annotations, but 1 was written}}
void takes_alias_partial(TwoAlias $a t) {}
LIFETIME_PARAMS("a")
void takes_two_unknown(Two $a $unknown t) {}
void takes_two_none(Two t) {}

// `this` is reserved for the lifetime elision gives the implicit object.
// expected-warning@+1 {{'this' is a distinguished lifetime and cannot be introduced as a parameter}}
LIFETIME_PARAMS("this")
void reserved_this() {}

// A class's declared lifetime parameters are in scope inside its member
// functions, while undeclared names are still diagnosed.
struct LIFETIME_PARAMS("a") RefWithMethods {
  int* $a p;
  int* $a get_ok() { return p; }
  // undeclared-warning@+1 {{lifetime 'b' is not declared by this function}}
  int* $b get_undeclared() { return p; }

  // A member cannot reintroduce one of its class's lifetimes.
  // expected-warning@+1 {{lifetime 'a' is declared more than once}}
  LIFETIME_PARAMS("a") void redeclares(int* $a x) {}
  LIFETIME_PARAMS("b") void introduces_own(int* $b x) {}
};
// expected-note@-11 {{lifetime 'a' declared here}}

//===----------------------------------------------------------------------===//
// Classes and their fields are not checked yet
//
// The checks on a class -- its own LIFETIME_PARAMS, its fields' types, and its
// bases -- exist (`checkRecordNamedLifetimes`), but nothing calls them. The
// natural caller is `Sema::CheckCompletedCXXClass`, and this prototype makes no
// changes to Sema's core declaration handling. They cannot ride along with the
// analysis of member functions instead: a class need not have any, and one
// with several would be diagnosed once per member.
//
// Every class below is ill-formed, and none of them is diagnosed today. The
// comment on each says what a caller would report, so that wiring one up shows
// up here as a test failure.
//===----------------------------------------------------------------------===//

struct LIFETIME_PARAMS("a") FieldsOk {
  int* $a p;
  int* $static s;
  int* unannotated;
  Ref $a r;
};

// Would report: lifetime 'b' is not declared by this class.
struct LIFETIME_PARAMS("a") FieldUndeclared {
  int* $b p;
};
// Would report: lifetime 'a' is not declared by this class.
struct FieldInUnannotatedClass {
  int* $a p;
};

// Would report: 2 lifetimes written where the type takes one, on each field.
struct LIFETIME_PARAMS("a") FieldArity {
  Ref $a $a r;
  int* $a $a p;
};

// Would report: 'static' is a distinguished lifetime.
struct LIFETIME_PARAMS("static") ClassReserved {};

// Would report: lifetime 'a' is declared more than once.
struct LIFETIME_PARAMS("a", "a") ClassDuplicate {};

// Would report, once for the pattern: lifetime 'b' is not declared.
template <typename T>
struct LIFETIME_PARAMS("a") ClassTemplate {
  T* $b p;
};
ClassTemplate<int> instantiation1;
ClassTemplate<char> instantiation2;

// Crubit appends a base class's lifetimes to the derived class's own. That is
// not modelled, so fields inherited from ParamBase are untracked through
// DerivedPlain and DerivedParams. Would report each direct base that declares
// lifetimes; Indirect would be covered through DerivedPlain.
struct LIFETIME_PARAMS("a") ParamBase { int* $a p; };
struct PlainBase {};
struct DerivedPlain : PlainBase, ParamBase {};
struct LIFETIME_PARAMS("a") DerivedParams : ParamBase {};
struct Indirect : DerivedPlain {};
struct DerivedFromPlain : PlainBase {};

//===----------------------------------------------------------------------===//
// Lifetimes inside template arguments are ignored
//
// A class template specialization is keyed on its canonical arguments, so
// `TView<int* $a>` and `TView<int*>` are the same type, and its fields are
// instantiated without the annotation. Crubit appends template-argument
// lifetimes to the record's own; until that is modelled, the annotation is
// reported rather than silently dropped. Like every check on a function, this
// one only runs on definitions.
//===----------------------------------------------------------------------===//

template <class T> struct TView { T value; };
template <class T, class U> struct TPair { T first; U second; };

LIFETIME_PARAMS("a", "b")
TView<int* $a> tmpl_arg_return(int* $a x, int* $b y) { // expected-warning {{lifetime annotation inside a template argument is not yet tracked and is ignored}}
  return {x};
}

LIFETIME_PARAMS("a")
void tmpl_arg_param(TView<int* $a> v) {} // expected-warning {{lifetime annotation inside a template argument is not yet tracked and is ignored}}

// Every annotation is reported, at any depth.
LIFETIME_PARAMS("a", "b")
void tmpl_arg_nested(TPair<int* $a, TView<int* $b>> p) {} // expected-warning 2 {{lifetime annotation inside a template argument is not yet tracked and is ignored}}

// An annotated class used as a template argument is no different.
LIFETIME_PARAMS("a")
void tmpl_arg_record(TView<Ref $a> v) {} // expected-warning {{lifetime annotation inside a template argument is not yet tracked and is ignored}}

// Annotations outside the template arguments are unaffected.
LIFETIME_PARAMS("a")
void tmpl_arg_outside(TView<int*>& $a v) {}

// Fields are not checked (see above), so this is not diagnosed either.
struct LIFETIME_PARAMS("a") TmplArgField {
  TView<int* $a> v;
};

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

