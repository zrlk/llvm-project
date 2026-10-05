// RUN: %clang_cc1 -fsyntax-only -verify \
// RUN:   -Wlifetime-safety-annotation-verification %s

#define $(l) [[clang::annotate_type("lifetime", #l)]]
#define LIFETIME_PARAMS(...) [[clang::annotate("lifetime_params", __VA_ARGS__)]]
#define $a $(a)
#define LB [[clang::lifetimebound]]

// expected-no-diagnostics

//===----------------------------------------------------------------------===//
// A named lifetime and 'lifetimebound' can be written on the same position.
//
// Both issue a placeholder loan to the same origin: 'lifetimebound' relies on
// the parameter's own placeholder loan being visible in the escaped set, and
// the signature adds a loan for the named lifetime. Issuing a loan used to
// erase the origin's existing loans, so the named loan hid the one
// 'lifetimebound' verification looks for and the escape was reported as
// unverifiable. Named loans are now additive.
//===----------------------------------------------------------------------===//

LIFETIME_PARAMS("a")
int* $a param_named(int* $a p LB) { return p; }

// Baseline: the same function with no named lifetime was always accepted.
int* param_plain(int* p LB) { return p; }

struct S {
  int x;

  LIFETIME_PARAMS("a")
  int* $a this_named() $a LB;

  int* this_plain() LB;
};

int* S::this_named() { return &x; }
int* S::this_plain() { return &x; }
