// RUN: %clang_cc1 -fsyntax-only -Wlifetime-safety-named-lifetime-violation -verify %s

// Verification of Crubit-style named lifetime return contracts.
//
// A function whose return type is annotated with a named lifetime may only
// return a value borrowed from that same lifetime. There is no outlives
// relation between named lifetimes yet, so the acceptance set for `$a` is
// exactly `{$a}`.
//
// Every such rejection carries a note naming the outlives bound that would
// have allowed it. The bound has no syntax, so the note only ever explains a
// rejection -- it never causes anything to be accepted, which is why it costs
// no variance reasoning. It fires only for named-to-named mismatches; a
// `$static` return is a separate diagnostic and gets no note, since a bound is
// not the repair there.

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

LIFETIME_PARAMS("a", "b")
int& $a returns_the_right_one(int& $a x, int& $b y) { return x; }

LIFETIME_PARAMS("a")
int* $a single_lifetime(int* $a x) { return x; }

LIFETIME_PARAMS("a", "b")
int& $a every_path_agrees(int& $a x, int& $a y, bool c) {
  if (c) return x;
  return y;
}

//===----------------------------------------------------------------------===//
// The returned value must come from the declared lifetime
//===----------------------------------------------------------------------===//

LIFETIME_PARAMS("a", "b")
int& $a reference(int& $a x, int& $b y) {
  return y; // expected-warning {{returning a value borrowed from lifetime 'b', but the return type declares lifetime 'a'}} // expected-note {{this would be allowed if lifetime 'b' were declared to outlive lifetime 'a', which cannot currently be expressed}}
}

LIFETIME_PARAMS("a", "b")
int* $a pointer(int* $a x, int* $b y) {
  return y; // expected-warning {{returning a value borrowed from lifetime 'b', but the return type declares lifetime 'a'}} // expected-note {{this would be allowed if lifetime 'b' were declared to outlive lifetime 'a', which cannot currently be expressed}}
}

// Each offending return is reported separately.
LIFETIME_PARAMS("a", "b", "c")
int& $a every_bad_path(int& $b y, int& $c z, bool k) {
  if (k)
    return y; // expected-warning {{returning a value borrowed from lifetime 'b', but the return type declares lifetime 'a'}} // expected-note {{this would be allowed if lifetime 'b' were declared to outlive lifetime 'a', which cannot currently be expressed}}
  return z;   // expected-warning {{returning a value borrowed from lifetime 'c', but the return type declares lifetime 'a'}} // expected-note {{this would be allowed if lifetime 'c' were declared to outlive lifetime 'a', which cannot currently be expressed}}
}

struct S {
  LIFETIME_PARAMS("a", "b")
  int& $a method(int& $a x, int& $b y) {
    return y; // expected-warning {{returning a value borrowed from lifetime 'b', but the return type declares lifetime 'a'}} // expected-note {{this would be allowed if lifetime 'b' were declared to outlive lifetime 'a', which cannot currently be expressed}}
  }
};

//===----------------------------------------------------------------------===//
// Only the outermost lifetime of the return type is checked
//===----------------------------------------------------------------------===//

// Lifetimes at one declarator chunk read outermost-first, so `p` is
// `int** $a $b` and `q` is `int** $b $a`; the outer lifetimes disagree.
LIFETIME_PARAMS("a", "b")
int** $a $b outer_level(int** $a $b p, int** $b $a q) {
  return q; // expected-warning {{returning a value borrowed from lifetime 'b', but the return type declares lifetime 'a'}} // expected-note {{this would be allowed if lifetime 'b' were declared to outlive lifetime 'a', which cannot currently be expressed}}
}

//===----------------------------------------------------------------------===//
// The signature is shared across redeclarations
//===----------------------------------------------------------------------===//

LIFETIME_PARAMS("a", "b")
int& $a declared_then_defined(int& $a x, int& $b y);
int& declared_then_defined(int& x, int& y) {
  return y; // expected-warning {{returning a value borrowed from lifetime 'b', but the return type declares lifetime 'a'}} // expected-note {{this would be allowed if lifetime 'b' were declared to outlive lifetime 'a', which cannot currently be expressed}}
}

//===----------------------------------------------------------------------===//
// Cases the check deliberately stays quiet about
//===----------------------------------------------------------------------===//

// An unannotated return type imposes no contract.
LIFETIME_PARAMS("a", "b")
int& unconstrained_return(int& $a x, int& $b y) { return y; }

// `$unknown` is the opt-out.
LIFETIME_PARAMS("b")
int* $unknown unknown_return(int* $b y) { return y; }

// An unannotated parameter carries no named lifetime to compare against. The
// missing annotation is the subject of the lifetimebound suggestions instead.
LIFETIME_PARAMS("a")
int* $a unannotated_param(int* $a x, int* y) { return y; }

// `$static` satisfies every obligation, so returning one under `$a` is fine.
// The reverse is not, and is checked in `static-lifetimes.cpp`.
LIFETIME_PARAMS("a")
int* $a from_static(int* $static s) { return s; }

// Nothing at all is annotated.
int& untouched(int& x, int& y) { return y; }

//===----------------------------------------------------------------------===//
// Templates are checked once per specialization
//===----------------------------------------------------------------------===//

// The lifetime arguments are plain string literals, so they survive
// substitution unchanged. The pattern itself has no CFG, so the check runs on
// each instantiation and the diagnostic carries an instantiation backtrace.
template <typename T>
LIFETIME_PARAMS("a", "b")
T& $a dependent(T& $a x, T& $b y) {
  return y; // expected-warning 2 {{returning a value borrowed from lifetime 'b', but the return type declares lifetime 'a'}} // expected-note 2 {{this would be allowed if lifetime 'b' were declared to outlive lifetime 'a', which cannot currently be expressed}}
}

int& instantiate_int(int& x, int& y) {
  return dependent(x, y); // expected-note {{in instantiation of function template specialization 'dependent<int>' requested here}}
}

float& instantiate_float(float& x, float& y) {
  return dependent(x, y); // expected-note {{in instantiation of function template specialization 'dependent<float>' requested here}}
}

// A second use of an existing specialization does not re-report.
int& reuse_int(int& x, int& y) { return dependent(x, y); }

// An uninstantiated pattern is never analyzed.
template <typename T>
LIFETIME_PARAMS("a", "b")
T& $a never_instantiated(T& $a x, T& $b y) { return y; }
