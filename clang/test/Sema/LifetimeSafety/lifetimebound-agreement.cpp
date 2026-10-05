// RUN: %clang_cc1 -fsyntax-only -verify \
// RUN:   -Wlifetime-safety-lifetimebound-conflict \
// RUN:   -Wlifetime-safety-named-lifetime-suggestions %s

#define $(l) [[clang::annotate_type("lifetime", #l)]]
#define LIFETIME_PARAMS(...) [[clang::annotate("lifetime_params", __VA_ARGS__)]]
#define $a $(a)
#define $b $(b)
#define $static $(static)
#define $unknown $(unknown)
#define LB [[clang::lifetimebound]]

//===----------------------------------------------------------------------===//
// A signature and 'lifetimebound' can contradict each other.
//
// 'lifetimebound' asserts the result may borrow from the parameter; a signature
// that gives the parameter a different lifetime asserts it may not.
//===----------------------------------------------------------------------===//

LIFETIME_PARAMS("a", "b")
int* $a conflict(int* $a p LB,
                 int* $b q LB) { // expected-warning {{'lifetimebound' says the result may borrow from this parameter, but it declares lifetime 'b' while the return type declares lifetime 'a'}}
  // expected-note@-2 {{return type declares lifetime 'a' here}}
  return p;
}

// Only the parameters that disagree are reported.
LIFETIME_PARAMS("a", "b")
int* $a conflict_one_of_two(int* $b bad LB, // expected-warning {{but it declares lifetime 'b' while the return type declares lifetime 'a'}}
                            int* $a good LB) {
  // expected-note@-2 {{return type declares lifetime 'a' here}}
  return good;
}

//===----------------------------------------------------------------------===//
// A parameter that shares the return type's lifetime should also say so with
// 'lifetimebound', since consumers that do not read signatures -- including
// Clang's own -Wdangling -- cannot otherwise see the relationship.
//===----------------------------------------------------------------------===//

LIFETIME_PARAMS("a", "b")
int* $a missing(int* $a p, // expected-warning {{parameter shares lifetime 'a' with the return type but is not marked 'lifetimebound'}}
                int* $b q) {
  // expected-note@-2 {{return type declares lifetime 'a' here}}
  return p;
}

// Both diagnostics can fire on the same function, on different parameters.
LIFETIME_PARAMS("a", "b")
int* $a both(int* $a p, // expected-warning {{parameter shares lifetime 'a' with the return type but is not marked 'lifetimebound'}}
             int* $b q LB) { // expected-warning {{but it declares lifetime 'b' while the return type declares lifetime 'a'}}
  // expected-note@-2 2 {{return type declares lifetime 'a' here}}
  return p;
}

//===----------------------------------------------------------------------===//
// Consistent annotations are silent.
//===----------------------------------------------------------------------===//

LIFETIME_PARAMS("a", "b")
int* $a consistent(int* $a p LB, int* $b q) { return p; }

// A parameter with no lifetime of its own is unconstrained by the signature, so
// it is not asked to carry 'lifetimebound' either way.
LIFETIME_PARAMS("a")
int* $a unannotated_param(int* $a p LB, int* q LB) { return p; }

//===----------------------------------------------------------------------===//
// The distinguished lifetimes opt out.
//
// '$static' outlives everything, so borrowing from it is always sound, and
// '$unknown' is an explicit assertion that no lifetime applies.
//===----------------------------------------------------------------------===//

LIFETIME_PARAMS("a")
int* $a distinguished(int* $static s LB, int* $unknown u LB, int* $a p LB) {
  return p;
}

// A bare return type states no contract to compare against.
LIFETIME_PARAMS("a")
int* plain_return(int* $a p LB) { return p; }

// A distinguished one does, and it is a contract `lifetimebound` contradicts:
// neither borrows from anything the caller passes in. See
// `static-lifetimes.cpp` for the full treatment.
LIFETIME_PARAMS("a")
int* $static static_return(int* $a p LB) { // expected-warning {{'lifetimebound' says the result may borrow from this parameter, but the return type declares lifetime 'static', which does not borrow from the parameters}}
  // expected-note@-1 {{return type declares lifetime 'static' here}}
  return p;
}

LIFETIME_PARAMS("a")
int* $unknown unknown_return(int* $a p LB) { // expected-warning {{'lifetimebound' says the result may borrow from this parameter, but the return type declares lifetime 'unknown', which does not borrow from the parameters}}
  // expected-note@-1 {{return type declares lifetime 'unknown' here}}
  return p;
}

//===----------------------------------------------------------------------===//
// The signature may be spelled on a declaration and the attribute on the
// definition, or vice versa; both are found.
//===----------------------------------------------------------------------===//

LIFETIME_PARAMS("a", "b")
int* $a split(int* $b q LB);

int* split(int* q) { // expected-warning {{but it declares lifetime 'b' while the return type declares lifetime 'a'}}
  // expected-note@-3 {{return type declares lifetime 'a' here}}
  return q;
}
