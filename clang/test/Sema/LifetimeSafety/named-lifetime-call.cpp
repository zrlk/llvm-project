// RUN: %clang_cc1 -fsyntax-only -Wlifetime-safety -verify %s

// Call-site substitution for named lifetimes.
//
// When a callee's return type names a lifetime, the result borrows from
// exactly those arguments written with the same lifetime. This is strictly
// more precise than `[[clang::lifetimebound]]`, which can only say that the
// result may borrow from *some* annotated argument.
//
// The soundness of exploiting this at the caller rests on the callee actually
// honouring its contract, which is what -Wlifetime-safety-named-lifetime-
// violation checks.

#define $(l) [[clang::annotate_type("lifetime", #l)]]
#define LIFETIME_PARAMS(...) [[clang::annotate("lifetime_params", __VA_ARGS__)]]
#define $a $(a)
#define $b $(b)
#define $unknown $(unknown)
#define LB [[clang::lifetimebound]]

// Marks a use for -Wlifetime-safety. Returning `r` instead would be reported
// as a return of stack memory, which carries no alias-chain note.
void use(int);

LIFETIME_PARAMS("a", "b")
int* $a pick(int* $a x, int* $b y);

//===----------------------------------------------------------------------===//
// The precision win
//===----------------------------------------------------------------------===//

// The result cannot borrow from `y`, so `local` dying is harmless. Under
// `lifetimebound` this would warn; see `lifetimebound_baseline` below for the
// same shape spelled the old way.
void unrelated_arg_dies(int* p) {
  int* r;
  {
    int local = 0;
    r = pick(p, &local);
  }
  use(*r);
}

// Same call, same shape, `lifetimebound` instead of a signature: the union of
// both parameters is assumed, so this warns.
int* both(int* x LB, int* y LB);
void lifetimebound_baseline(int* p) {
  int* r;
  {
    int local = 0;
    r = both(p, &local); // expected-warning {{local variable 'local' does not live long enough}}
                         // expected-note@-1 {{result of call to 'both' aliases the storage of local variable 'local' because parameter 'y' is marked as lifetimebound}}
  }
  use(*r); // expected-note {{later used here}}
} // expected-note@-2 {{local variable 'local' is destroyed here}}

//===----------------------------------------------------------------------===//
// Detection still works through the matching lifetime
//===----------------------------------------------------------------------===//

void matching_arg_dies(int* q) {
  int* r;
  {
    int local = 0;
    r = pick(&local, q); // expected-warning {{local variable 'local' does not live long enough}}
                         // expected-note@-1 {{result of call to 'pick' aliases the storage of local variable 'local'}}
  }
  use(*r); // expected-note {{later used here}}
} // expected-note@-2 {{local variable 'local' is destroyed here}}

//===----------------------------------------------------------------------===//
// Several arguments may share one lifetime
//===----------------------------------------------------------------------===//

LIFETIME_PARAMS("a")
int* $a join(int* $a x, int* $a y);

void shared_lifetime_first(int* p) {
  int* r;
  {
    int local = 0;
    r = join(&local, p); // expected-warning {{local variable 'local' does not live long enough}}
                         // expected-note@-1 {{result of call to 'join' aliases the storage of local variable 'local'}}
  }
  use(*r); // expected-note {{later used here}}
} // expected-note@-2 {{local variable 'local' is destroyed here}}

void shared_lifetime_second(int* p) {
  int* r;
  {
    int local = 0;
    r = join(p, &local); // expected-warning {{local variable 'local' does not live long enough}}
                         // expected-note@-1 {{result of call to 'join' aliases the storage of local variable 'local'}}
  }
  use(*r); // expected-note {{later used here}}
} // expected-note@-2 {{local variable 'local' is destroyed here}}

//===----------------------------------------------------------------------===//
// Member calls: the implicit object argument shifts parameter indices
//===----------------------------------------------------------------------===//

struct S {
  LIFETIME_PARAMS("a", "b")
  int* $a pick(int* $a x, int* $b y);
};

void method_unrelated_dies(S s, int* p) {
  int* r;
  {
    int local = 0;
    r = s.pick(p, &local);
  }
  use(*r);
}

void method_matching_dies(S s, int* p) {
  int* r;
  {
    int local = 0;
    r = s.pick(&local, p); // expected-warning {{local variable 'local' does not live long enough}}
                           // expected-note@-1 {{result of call to 'pick' aliases the storage of local variable 'local'}}
  }
  use(*r); // expected-note {{later used here}}
} // expected-note@-2 {{local variable 'local' is destroyed here}}

//===----------------------------------------------------------------------===//
// When the signature does not govern the result
//===----------------------------------------------------------------------===//

// The return type names no lifetime, so the signature says nothing about what
// the call yields and `lifetimebound` is still honoured.
LIFETIME_PARAMS("a", "b")
int* bare_return(int* $a x LB, int* $b y LB);

void falls_back_to_lifetimebound(int* p) {
  int* r;
  {
    int local = 0;
    r = bare_return(p, &local); // expected-warning {{local variable 'local' does not live long enough}}
                                // expected-note@-1 {{result of call to 'bare_return' aliases the storage of local variable 'local' because parameter 'y' is marked as lifetimebound}}
  }
  use(*r); // expected-note {{later used here}}
} // expected-note@-2 {{local variable 'local' is destroyed here}}

//===----------------------------------------------------------------------===//
// Every level flows independently
//===----------------------------------------------------------------------===//

// Matching by name makes differing list lengths a non-issue, so inner origins
// can be flowed too. The `lifetimebound` path deliberately does not do this
// (see the FIXME in FactsGenerator::handleFunctionCall) because it has no way
// to line the levels up.
//
// `q` reverses the two lifetimes relative to `p`, so its outer level feeds the
// result's *inner* level.
//
// A lifetime binds to the level it is written on, so the outer level is the
// one named after the last `*`: `int* $b * $a` is 'a' outside, 'b' inside.
LIFETIME_PARAMS("a", "b")
int* $b * $a get(int* $b * $a p, int* $a * $b q);

void outer_level(int** q) {
  int** r;
  {
    int* l = nullptr;
    r = get(&l, q); // expected-warning {{local variable 'l' does not live long enough}}
                    // expected-note@-1 {{result of call to 'get' aliases the storage of local variable 'l'}}
  } // expected-note {{local variable 'l' is destroyed here}}
  use(**r); // expected-note {{later used here}}
}

void inner_level(int** p) {
  int** r;
  {
    int* l = nullptr;
    r = get(p, &l); // expected-warning {{local variable 'l' does not live long enough}}
                    // expected-note@-1 {{result of call to 'get' aliases the storage of local variable 'l'}}
  } // expected-note {{local variable 'l' is destroyed here}}
  use(**r); // expected-note {{later used here}}
}

// `$unknown` opts out entirely: nothing flows.

LIFETIME_PARAMS("a")
int* $unknown opaque(int* $a x);

void unknown_return_flows_nothing() {
  int* r;
  {
    int local = 0;
    r = opaque(&local);
  }
  use(*r);
}

// A lifetime named on the return but on no parameter borrows from nothing.
LIFETIME_PARAMS("a", "b")
int* $a fresh(int* $b y);

void fresh_lifetime_flows_nothing() {
  int* r;
  {
    int local = 0;
    r = fresh(&local);
  }
  use(*r);
}
