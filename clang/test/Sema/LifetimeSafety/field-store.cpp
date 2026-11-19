// RUN: %clang_cc1 -fsyntax-only -Wlifetime-safety \
// RUN:   -Wlifetime-safety-named-lifetime-violation -verify %s

// Stores into a field of a record with lifetime parameters, and stores
// through a dereference.
//
// A record with LIFETIME_PARAMS carries one origin per parameter. Reading a
// field substitutes the parameter's origin into the field's annotated levels;
// storing into a field adds the stored value to the parameter's origin, so a
// later read of the field, or of the whole object, sees it. The store does not
// kill the parameter's origin: other fields may name the same parameter.

#define $(l) [[clang::annotate_type("lifetime", #l)]]
#define LIFETIME_PARAMS(...) [[clang::annotate("lifetime_params", __VA_ARGS__)]]

struct LIFETIME_PARAMS("a") Wrapper {
  explicit Wrapper(int &x [[clang::lifetimebound]]) : p(&x) {}
  int get() const { return *p; }
  int *$(a) p;
};

struct LIFETIME_PARAMS("a") Holder {
  Wrapper $(a) w;
};

int FieldDangle(int &x) {
  Holder h{Wrapper(x)};
  {
    int v = 1;
    h.w = Wrapper(v); // expected-warning {{local variable 'v' does not live long enough}}
  }                   // expected-note {{destroyed here}}
  return h.w.get();   // expected-note {{later used here}}
}

int WholeObjectDangle(int &x) {
  Holder h{Wrapper(x)};
  {
    int v = 1;
    h.w = Wrapper(v); // expected-warning {{local variable 'v' does not live long enough}}
  }                   // expected-note {{destroyed here}}
  Holder copy = h;    // expected-note {{local variable 'h' aliases the storage of local variable 'v'}}
  return copy.w.get(); // expected-note {{later used here}}
}

int ThroughPointerDangle(int &x) {
  Holder h{Wrapper(x)};
  Holder *q = &h;
  {
    int v = 1;
    q->w = Wrapper(v); // expected-warning {{local variable 'v' does not live long enough}}
  }                    // expected-note {{destroyed here}}
  return q->w.get();   // expected-note {{later used here}}
}

LIFETIME_PARAMS("x", "y")
Holder $(x) Overwrite(int &$(x) x, int &$(y) y) {
  Holder h{Wrapper(x)};
  h.w = Wrapper(y);
  return h; // expected-warning {{returning a value borrowed from lifetime 'y', but the return type declares lifetime 'x'}}
  // expected-note@-1 {{this would be allowed if lifetime 'y' were declared to outlive lifetime 'x', which cannot currently be expressed}}
}

LIFETIME_PARAMS("x", "y")
Wrapper $(x) FieldOverwriteRead(int &$(x) x, int &$(y) y) {
  Holder h{Wrapper(x)};
  h.w = Wrapper(y);
  return h.w; // expected-warning {{returning a value borrowed from lifetime 'y', but the return type declares lifetime 'x'}}
  // expected-note@-1 {{this would be allowed if lifetime 'y' were declared to outlive lifetime 'x', which cannot currently be expressed}}
}

// The stored value only adds to the parameter's origin.
LIFETIME_PARAMS("x")
Wrapper $(x) FieldStoreSameLifetime(int &$(x) x, int &$(x) x2) {
  Holder h{Wrapper(x)};
  h.w = Wrapper(x2);
  return h.w;
}

// A user-provided copy assignment of a record with lifetime parameters takes
// the source's parameters, as its type says.
struct LIFETIME_PARAMS("a") UserAssign {
  explicit UserAssign(int &x [[clang::lifetimebound]]) : p(&x) {}
  UserAssign &operator=(const UserAssign &o) {
    p = o.p;
    return *this;
  }
  int *$(a) p;
};

int UserAssignDangle(int &x) {
  UserAssign u(x);
  {
    int v = 1;
    u = UserAssign(v); // expected-warning {{local variable 'v' does not live long enough}}
  }                    // expected-note {{destroyed here}}
  return *u.p;         // expected-note {{later used here}}
}

// A store through `*pp` lands in the pointee's origins.
int DerefStoreDangle(int &x) {
  int *p = &x;
  int **pp = &p;
  {
    int v = 1;
    *pp = &v; // expected-warning {{local variable 'v' does not live long enough}}
  }           // expected-note {{destroyed here}}
  return **pp; // expected-note {{later used here}}
}
