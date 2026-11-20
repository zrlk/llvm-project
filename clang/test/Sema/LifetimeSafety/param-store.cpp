// RUN: %clang_cc1 -fsyntax-only -Wlifetime-safety \
// RUN:   -Wlifetime-safety-named-lifetime-violation -verify %s

// Stores through pointer and reference parameters, checked in the callee.
//
// What a function stores into what a parameter refers to (`*p = v`, `r = v`,
// or a field of either) is seen by the caller once the function returns. At
// the exit, each level of the stored value must satisfy the lifetime that the
// parameter's type declares at the matching level below it: a level with no
// lifetime written accepts no named loan, a `$static` level only storage that
// never expires. Only the stores are checked, not what the caller passed in,
// and only what is still there at the exit. A stored borrow of a local
// dangles in the caller.

#define $(l) [[clang::annotate_type("lifetime", #l)]]
#define $static $(static)
#define $unknown $(unknown)
#define LIFETIME_PARAMS(...) [[clang::annotate("lifetime_params", __VA_ARGS__)]]

LIFETIME_PARAMS("a")
void GetOk(int *$(a) in, int *$(a) *out) { *out = in; }

LIFETIME_PARAMS("a", "b")
void GetWrongNamed(int *$(a) in, int *$(b) *out) { // expected-note {{parameter 'out' declared here}}
  *out = in; // expected-warning {{storing a value borrowed from lifetime 'a' into what parameter 'out' refers to, whose type declares lifetime 'b' there}}
  // expected-note@-1 {{this would be allowed if lifetime 'a' were declared to outlive lifetime 'b', which cannot currently be expressed}}
}

// A level with nothing written on it accepts no named loan.
LIFETIME_PARAMS("a")
void GetElided(int *$(a) in, int **out) { // expected-note {{parameter 'out' declared here}}
  *out = in; // expected-warning {{storing a value borrowed from lifetime 'a' into what parameter 'out' refers to, whose type declares no lifetime there}}
}

// Every level of the stored value is checked: the levels below a pointer that
// can be written must agree.
LIFETIME_PARAMS("a")
void DeepStoreElided(int **$(a) *m, int *$(a) *$(a) n) { // expected-note {{parameter 'm' declared here}}
  *m = n; // expected-warning {{storing a value borrowed from lifetime 'a' at level 2 below parameter 'm', whose type declares no lifetime there}}
}

LIFETIME_PARAMS("a", "b")
void DeepStoreNamed(int *$(b) *$(a) *m, int *$(a) *$(a) n) { // expected-note {{parameter 'm' declared here}}
  *m = n; // expected-warning {{storing a value borrowed from lifetime 'a' at level 2 below parameter 'm', whose type declares lifetime 'b' there}}
}

LIFETIME_PARAMS("a")
void DeepStoreOk(int *$(a) *$(a) *m, int *$(a) *$(a) n) { *m = n; }

LIFETIME_PARAMS("a", "b")
void RefStore(int *$(a) in, int *$(b) &out) { // expected-note {{parameter 'out' declared here}}
  out = in; // expected-warning {{storing a value borrowed from lifetime 'a' into what parameter 'out' refers to, whose type declares lifetime 'b' there}}
  // expected-note@-1 {{this would be allowed if lifetime 'a' were declared to outlive lifetime 'b', which cannot currently be expressed}}
}

// Only what the parameter holds at the exit is checked.
LIFETIME_PARAMS("a", "b")
void Overwritten(int *$(a) in, int *$(b) in2, int *$(b) *out) {
  *out = in;
  *out = in2;
}

// A parameter's own pointer, stored with no annotation involved, is not a
// violation of anything written.
void NoAnnotations(int *in, int **out) { *out = in; }

// Storing the parameter itself is not a store through it.
LIFETIME_PARAMS("a", "b")
void ReassignParam(int *$(a) *p, int *$(b) *q) { p = q; }

LIFETIME_PARAMS("a")
void StaticSink(int *$(a) in, int *$static *out) { // expected-note {{parameter 'out' declared here}}
  *out = in; // expected-warning {{storing a value borrowed from this function's caller into what parameter 'out' refers to, whose type declares lifetime 'static' there}}
}

int global;
void StaticSinkGlobal(int *$static *out) { *out = &global; }
void StaticSinkStaticParam(int *$static in, int *$static *out) { *out = in; }

LIFETIME_PARAMS("a")
void UnknownSink(int *$(a) in, int *$unknown *out) { *out = in; }

// A borrow of a local stored through a parameter dangles in the caller.
void Leak(int **out) {
  int x = 1;
  *out = &x; // expected-warning {{local variable 'x' does not live long enough}}
} // expected-note {{destroyed here}} expected-note {{later used here}}

void LeakRef(int *&out) {
  int x = 1;
  out = &x; // expected-warning {{local variable 'x' does not live long enough}}
} // expected-note {{destroyed here}} expected-note {{later used here}}

void LeakOverwritten(int **out) {
  int x = 1;
  *out = &x;
  *out = nullptr;
}

// A store in a loop body is seen too, though the body follows the exit in
// the order the facts are generated in.
void LeakInLoop(int **out, int n) {
  for (int i = 0; i < n; ++i) {
    int x = i;
    *out = &x; // expected-warning {{local variable 'x' does not live long enough}}
  } // expected-note {{destroyed here}}
} // expected-note {{later used here}}

// Fields of a record with lifetime parameters, through a reference or a
// pointer parameter.
struct LIFETIME_PARAMS("a") Wrapper {
  explicit Wrapper(int &x [[clang::lifetimebound]]) : p(&x) {}
  int get() const { return *p; }
  int *$(a) p;
};

struct LIFETIME_PARAMS("a") Holder {
  Wrapper $(a) w;
};

LIFETIME_PARAMS("a", "b", "c")
void SetBad(Holder $(a) &$(c) h, int &$(b) y) { // expected-note {{parameter 'h' declared here}}
  h.w = Wrapper(y); // expected-warning {{storing a value borrowed from lifetime 'b' into what parameter 'h' refers to, whose type declares lifetime 'a' there}}
  // expected-note@-1 {{this would be allowed if lifetime 'b' were declared to outlive lifetime 'a', which cannot currently be expressed}}
}

LIFETIME_PARAMS("a", "c")
void SetOk(Holder $(a) &$(c) h, int &$(a) y) { h.w = Wrapper(y); }

LIFETIME_PARAMS("a", "b")
void SetBadPtr(Holder $(a) *h, int &$(b) y) { // expected-note {{parameter 'h' declared here}}
  h->w = Wrapper(y); // expected-warning {{storing a value borrowed from lifetime 'b' into what parameter 'h' refers to, whose type declares lifetime 'a' there}}
  // expected-note@-1 {{this would be allowed if lifetime 'b' were declared to outlive lifetime 'a', which cannot currently be expressed}}
}

LIFETIME_PARAMS("a", "b")
void AssignBad(Holder $(a) &h, Holder $(b) &other) { // expected-note {{parameter 'h' declared here}}
  h = other; // expected-warning {{storing a value borrowed from lifetime 'b' into what parameter 'h' refers to, whose type declares lifetime 'a' there}}
  // expected-note@-1 {{this would be allowed if lifetime 'b' were declared to outlive lifetime 'a', which cannot currently be expressed}}
}

void SetLeak(Holder &h) {
  int v = 1;
  h.w = Wrapper(v); // expected-warning {{local variable 'v' does not live long enough}}
} // expected-note {{destroyed here}} expected-note {{later used here}}
