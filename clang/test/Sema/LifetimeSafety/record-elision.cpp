// RUN: %clang_cc1 -fsyntax-only -Wlifetime-safety \
// RUN:   -Wlifetime-safety-named-lifetime-violation -verify=viol %s
// RUN: %clang_cc1 -fsyntax-only \
// RUN:   -Wlifetime-safety-named-lifetime-suggestions -verify=suggest %s

// Lifetime elision for members of a class with LIFETIME_PARAMS.
//
// A member function's return lifetime that is not written takes the lifetime
// of `this`, as in Crubit. That is sound -- an object cannot outlive its own
// lifetime parameters, so every class lifetime outlives `this` -- but strict
// for view types, whose accessors return something that would live as long as
// a class lifetime. Such accessors are pointed out by
// -Wlifetime-safety-named-lifetime-suggestions.
//
// Classes without LIFETIME_PARAMS are unaffected, as are members that use
// `lifetimebound`, whose result the attribute already describes.

#define $(l) [[clang::annotate_type("lifetime", #l)]]
#define LIFETIME_PARAMS(...) [[clang::annotate("lifetime_params", __VA_ARGS__)]]
#define $a $(a)
#define $b $(b)

struct LIFETIME_PARAMS("a") View {
  int* $a p;
  int n;

  // Returning a class lifetime under the elided `this` lifetime is accepted,
  // but annotating it would let callers keep the result longer.
  int* get() { return p; } // suggest-warning {{return type of 'get' defaults to the lifetime of the object, but everything it returns is borrowed from lifetime 'a'; annotate the return type with lifetime 'a' to let callers rely on it}}

  // Borrowing from the object itself: the elided lifetime is the right one.
  int* own() { return &n; }
  int* either(bool c) { return c ? p : &n; }
  int* via_other_member() { return get(); }

  int* $a get_a() { return p; }

  // `lifetimebound` is left in charge.
  int* pick(int* x [[clang::lifetimebound]]) { return x; }
};

// The result of an elided accessor borrows from the object, so returning it
// from a by-value parameter dangles even though the field would not.
LIFETIME_PARAMS("a")
// suggest-note@+2 {{return type declares lifetime 'a' here}}
// suggest-warning@+1 {{parameter shares lifetime 'a' with the return type but is not marked 'lifetimebound'}}
int* $a through_elided(View $a v) {
  return v.get(); // viol-warning {{stack memory associated with parameter 'v' is returned}} viol-note {{returned here}}
}

// The annotated accessor says what it means, and the caller can rely on it.
LIFETIME_PARAMS("a")
// suggest-note@+2 {{return type declares lifetime 'a' here}}
// suggest-warning@+1 {{parameter shares lifetime 'a' with the return type but is not marked 'lifetimebound'}}
int* $a through_annotated(View $a v) { return v.get_a(); }

// The implied bound only relates class lifetimes to `this`; it does not make
// unrelated lifetimes acceptable.
struct LIFETIME_PARAMS("a") Mismatch {
  LIFETIME_PARAMS("b")
  int* other(int* $b x) {
    return x; // viol-warning {{returning a value borrowed from lifetime 'b', but the return type declares lifetime 'this'}} viol-note {{this would be allowed if lifetime 'b' were declared to outlive lifetime 'this', which cannot currently be expressed}}
  }
};

// Without LIFETIME_PARAMS nothing changes: an unannotated accessor still has
// no contract, and its callers fall back to `lifetimebound`.
struct Plain {
  int n;
  int* own() { return &n; }
};
int* plain_caller(Plain& s) { return s.own(); }

//===----------------------------------------------------------------------===//
// The caller's half of the implied bound (D22). A result named with the
// lifetime of `this` may borrow from any class lifetime of the object, so at
// the call it borrows from what the object was built from as well as from the
// object itself. Without this, reassigning the object to borrow a shorter-lived
// local and reading through the accessor's result dangles unnoticed.
//===----------------------------------------------------------------------===//

void use(int);

struct LIFETIME_PARAMS("a") Holder {
  int* $a p;
  int n;
  Holder(int* $a q) : p(q) {} // suggest-warning {{parameter shares lifetime 'a' with the return type but is not marked 'lifetimebound'}}
  int* get() { return p; }                           // suggest-warning {{return type of 'get' defaults to the lifetime of the object, but everything it returns is borrowed from lifetime 'a'; annotate the return type with lifetime 'a' to let callers rely on it}}
  int* decl();                                       // declared only
  int* either(bool c) { return c ? p : &n; }         // suggestion blocked
  LIFETIME_PARAMS("t") int* $(t) named() $(t); // suggest-note {{return type declares lifetime 't' here}}
  int* own() { return &n; }
};
int* Holder::named() { return p; } // suggest-warning {{the implicit object parameter shares lifetime 't' with the return type but is not marked 'lifetimebound'}}

void elided_caller() {
  int y = 0;
  Holder h(&y);
  int* r;
  {
    int x = 1;
    h = Holder(&x); // viol-warning {{local variable 'x' does not live long enough}}
    r = h.get();    // viol-note {{result of call to 'get' aliases the storage of local variable 'x'}}
  } // viol-note {{destroyed here}}
  use(*r); // viol-note {{later used here}}
}

// Only the declaration is visible, so there is no suggestion to heed.
void declared_only_caller() {
  int y = 0;
  Holder h(&y);
  int* r;
  {
    int x = 1;
    h = Holder(&x); // viol-warning {{local variable 'x' does not live long enough}}
    r = h.decl();   // viol-note {{result of call to 'decl' aliases the storage of local variable 'x'}}
  } // viol-note {{destroyed here}}
  use(*r); // viol-note {{later used here}}
}

// FIXME: assigning through a pointer does not reach the pointee's origins, so
// this is missed even with `int* $a` on the result, and for a plain `hp->p`.
void through_pointer_caller(Holder* hp) {
  int* r;
  {
    int x = 1;
    *hp = Holder(&x);
    r = hp->decl();
  }
  use(*r);
}

// Borrowing from both, so the named-return suggestion is withheld.
void mixed_caller() {
  int y = 0;
  Holder h(&y);
  int* r;
  {
    int x = 1;
    h = Holder(&x);     // viol-warning {{local variable 'x' does not live long enough}}
    r = h.either(true); // viol-note {{result of call to 'either' aliases the storage of local variable 'x'}}
  } // viol-note {{destroyed here}}
  use(*r); // viol-note {{later used here}}
}

// The lifetime of `this` written out rather than elided: the same bound.
void named_this_caller() {
  int y = 0;
  Holder h(&y);
  int* r;
  {
    int x = 1;
    h = Holder(&x); // viol-warning {{local variable 'x' does not live long enough}}
    r = h.named();  // viol-note {{result of call to 'named' aliases the storage of local variable 'x'}}
  } // viol-note {{destroyed here}}
  use(*r); // viol-note {{later used here}}
}

// The signature cannot tell `own` from `get`, so the caller treats both alike;
// Rust rejects the same program. Annotating `int* $a get()` is what lets a
// caller keep a result longer than the object.
void own_caller() {
  int y = 0;
  Holder h(&y);
  int* r;
  {
    int x = 1;
    h = Holder(&x); // viol-warning {{local variable 'x' does not live long enough}}
    r = h.own();    // viol-note {{result of call to 'own' aliases the storage of local variable 'x'}}
  } // viol-note {{destroyed here}}
  use(*r); // viol-note {{later used here}}
}

// With the class lifetime outliving the use, nothing is reported.
void long_lived_caller() {
  int y = 0;
  Holder h(&y);
  int* r = h.get();
  use(*r);
}
