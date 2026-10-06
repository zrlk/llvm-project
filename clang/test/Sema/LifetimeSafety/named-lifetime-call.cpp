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

//===----------------------------------------------------------------------===//
// Structs with LIFETIME_PARAMS
//===----------------------------------------------------------------------===//

#define $2(l1, l2) [[clang::annotate_type("lifetime", #l1, #l2)]]

struct LIFETIME_PARAMS("a") SV {};
using SVA = SV;
struct LIFETIME_PARAMS("a", "b") Pair {};

void use_sv(SV);

LIFETIME_PARAMS("a")
SV $a make_sv(int* $a p);

LIFETIME_PARAMS("a", "b")
SV $a pick_sv(SV $a x, SV $b y);

LIFETIME_PARAMS("a", "b")
Pair $2(a, b) make_pair(int* $a x, int* $b y);

LIFETIME_PARAMS("a", "b")
int* $a pair_first(Pair $2(a, b) p);

LIFETIME_PARAMS("a", "b")
int* $b pair_second(Pair $2(a, b) p);

void sv_unrelated_dies(SV keep) {
  SV r;
  {
    int local = 0;
    r = pick_sv(keep, make_sv(&local));
  }
  use_sv(r);
}

void sv_matching_dies(SV other) {
  SV r;
  {
    int local = 0;
    r = pick_sv(make_sv(&local), other); // expected-warning {{local variable 'local' does not live long enough}}
                                         // expected-note@-1 {{result of call to 'pick_sv' aliases the storage of local variable 'local'}}
                                         // expected-note@-2 {{result of call to 'make_sv' aliases the storage of local variable 'local'}}
  } // expected-note {{local variable 'local' is destroyed here}}
  use_sv(r); // expected-note {{later used here}}
}

void pair_slots_flow_independently(int* keep) {
  int* r1;
  {
    int local = 0;
    Pair p = make_pair(keep, &local);
    r1 = pair_first(p);
  }
  use(*r1);

  int* r2;
  {
    int local = 0;
    Pair p = make_pair(keep, &local); // expected-warning {{local variable 'local' does not live long enough}}
                                      // expected-note@-1 {{result of call to 'make_pair' aliases the storage of local variable 'local'}}
    r2 = pair_second(p); // expected-note {{local variable 'p' aliases the storage of local variable 'local'}}
                         // expected-note@-1 {{result of call to 'pair_second' aliases the storage of local variable 'local'}}
  } // expected-note {{local variable 'local' is destroyed here}}
  use(*r2); // expected-note {{later used here}}
}

struct LIFETIME_PARAMS("a", "b") PairWithFields {
  int* $a first;
  int* $b second;

  int* $a get_first() { return first; }
  int* $b get_second() { return second; }
};

LIFETIME_PARAMS("a", "b")
PairWithFields $2(a, b) make_pair_with_fields(int* $a x, int* $b y);

void pair_fields_and_methods(int* keep) {
  int* r1;
  {
    int local = 0;
    PairWithFields p = make_pair_with_fields(keep, &local);
    r1 = p.first;
  }
  use(*r1);

  int* r2;
  {
    int local = 0;
    PairWithFields p = make_pair_with_fields(keep, &local); // expected-warning {{local variable 'local' does not live long enough}}
                                                            // expected-note@-1 {{result of call to 'make_pair_with_fields' aliases the storage of local variable 'local'}}
    r2 = p.second;
  } // expected-note {{local variable 'local' is destroyed here}}
  use(*r2); // expected-note {{later used here}}

  int* m1;
  {
    int local = 0;
    PairWithFields p = make_pair_with_fields(keep, &local);
    m1 = p.get_first();
  }
  use(*m1);

  int* m2;
  {
    int local = 0;
    PairWithFields p = make_pair_with_fields(keep, &local); // expected-warning {{local variable 'local' does not live long enough}}
                                                            // expected-note@-1 {{result of call to 'make_pair_with_fields' aliases the storage of local variable 'local'}}
    m2 = p.get_second(); // expected-note {{result of call to 'get_second' aliases the storage of local variable 'local'}}
  } // expected-note {{local variable 'local' is destroyed here}}
  use(*m2); // expected-note {{later used here}}
}

struct LIFETIME_PARAMS("a", "b") CtorPair {
  int* $a first;
  int* $b second;
  CtorPair(int* $a f, int* $b s) : first(f), second(s) {}
};

void pair_ctor_and_agg_init(int* keep) {
  int* c1;
  {
    int local = 0;
    CtorPair p(keep, &local);
    c1 = p.first;
  }
  use(*c1);

  int* c2;
  {
    int local = 0;
    CtorPair p(keep, &local); // expected-warning {{local variable 'local' does not live long enough}}
    c2 = p.second;
  } // expected-note {{local variable 'local' is destroyed here}}
  use(*c2); // expected-note {{later used here}}

  int* a1;
  {
    int local = 0;
    PairWithFields p{keep, &local};
    a1 = p.first;
  }
  use(*a1);

  int* a2;
  {
    int local = 0;
    PairWithFields p{keep, &local}; // expected-warning {{local variable 'local' does not live long enough}}
    a2 = p.second;
  } // expected-note {{local variable 'local' is destroyed here}}
  use(*a2); // expected-note {{later used here}}
}

//===----------------------------------------------------------------------===//
// Which steps the alias notes name
//===----------------------------------------------------------------------===//
//
// The notes come from the shared use-after-scope machinery, which names a step
// only when it is an expression of its own on the path the loan took. A use of
// a variable shares that variable's origins, so the variable is named when its
// value is copied out -- as a by-value argument, above, gets
// "local variable 'p' aliases ..." -- but not when it is accessed in place:
// `p.second` above, and `p.get_second()`, reach the loan without naming `p`.
// This is the same rule the analysis applies to unannotated code, where a call
// to a non-const accessor on a gsl::Pointer variable does not name the
// variable either, and a call to a const one does, through the qualification
// conversion of the object argument.

struct LIFETIME_PARAMS("a") Box {
  int* $a p;
  int* $a get() { return p; }
  int* $a get_const() const { return p; }
};

LIFETIME_PARAMS("a")
Box $a make_box(int* $a p);

void notes_follow_copies() {
  int* r1;
  {
    int local = 0;
    Box b = make_box(&local); // expected-warning {{local variable 'local' does not live long enough}}
                              // expected-note@-1 {{result of call to 'make_box' aliases the storage of local variable 'local'}}
    r1 = b.get(); // expected-note {{result of call to 'get' aliases the storage of local variable 'local'}}
  } // expected-note {{local variable 'local' is destroyed here}}
  use(*r1); // expected-note {{later used here}}

  int* r2;
  {
    int local = 0;
    Box b = make_box(&local); // expected-warning {{local variable 'local' does not live long enough}}
                              // expected-note@-1 {{result of call to 'make_box' aliases the storage of local variable 'local'}}
    r2 = b.get_const(); // expected-note {{local variable 'b' aliases the storage of local variable 'local'}}
                        // expected-note@-1 {{result of call to 'get_const' aliases the storage of local variable 'local'}}
  } // expected-note {{local variable 'local' is destroyed here}}
  use(*r2); // expected-note {{later used here}}
}

//===----------------------------------------------------------------------===//
// Class templates
//===----------------------------------------------------------------------===//
//
// A specialization of a class template carries the pattern's LIFETIME_PARAMS
// and field annotations, so it is modelled like any other annotated class.

template <typename T>
struct LIFETIME_PARAMS("a") TBox {
  T* $a p;
  T* $a get() { return p; }
};

void template_box(int* keep) {
  int* r1;
  {
    int local = 0;
    TBox<int> b{&local}; // expected-warning {{local variable 'local' does not live long enough}}
    r1 = b.get(); // expected-note {{result of call to 'get' aliases the storage of local variable 'local'}}
  } // expected-note {{local variable 'local' is destroyed here}}
  use(*r1); // expected-note {{later used here}}

  int* r2;
  {
    int local = 0;
    TBox<int> b{keep};
    r2 = b.get();
    (void)local;
  }
  use(*r2);
}
