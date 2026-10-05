// RUN: %clang_cc1 -fsyntax-only -Wlifetime-safety-named-lifetime-violation -verify=viol %s
// RUN: %clang_cc1 -fsyntax-only -Wlifetime-safety-named-lifetimes -verify=named %s
// RUN: %clang_cc1 -fsyntax-only -Wlifetime-safety-lifetimebound-conflict -verify=conflict %s
// RUN: %clang_cc1 -fsyntax-only -Wlifetime-safety -verify=dangling %s

// The distinguished lifetimes `$static` and `$unknown`.
//
// `$static` names storage that never expires. Unlike a named lifetime, which
// the caller instantiates with whatever it has, it is a fixed demand: it
// satisfies every obligation and imposes one when written into.
//
// `$unknown` is the opposite: an assertion that no lifetime applies. It
// suppresses both the diagnostics and the obligations a loan passing through
// it would otherwise carry. Crubit pre-seeds exactly these two names as
// builtin lifetime bindings, in
// `rs_bindings_from_cc/generate_bindings/lifetime_defaults_transform.rs`.

#define $(l) [[clang::annotate_type("lifetime", #l)]]
#define LIFETIME_PARAMS(...) [[clang::annotate("lifetime_params", __VA_ARGS__)]]
#define $a $(a)
#define $static $(static)
#define $unknown $(unknown)
#define LB [[clang::lifetimebound]]

int g;

//===----------------------------------------------------------------------===//
// Neither name may be introduced as a parameter
//===----------------------------------------------------------------------===//

LIFETIME_PARAMS("static") // named-warning {{'static' is a distinguished lifetime and cannot be introduced as a parameter}}
int* declares_static(int* p) { return p; }

LIFETIME_PARAMS("unknown") // named-warning {{'unknown' is a distinguished lifetime and cannot be introduced as a parameter}}
int* declares_unknown(int* p) { return p; }

// Conversely, using them needs no declaration: they are always in scope.
int* $static uses_static_undeclared() { return &g; }
int* $unknown uses_unknown_undeclared(int* p) { return p; }

//===----------------------------------------------------------------------===//
// A `$static` return accepts only storage that never expires
//===----------------------------------------------------------------------===//

int* $static from_global() { return &g; }

int* $static from_function_static() { static int x; return &x; }

int* $static from_static_param(int* $static p) { return p; }

// `$unknown` is an opt-out, so a value flowing out of one is not challenged.
int* $static from_unknown_param(int* $unknown p) { return p; }

// The unsound direction: `$a` is whatever the caller supplied, which is not
// forever.
LIFETIME_PARAMS("a")
int* $static from_named_param(int* $a p) {
  return p; // viol-warning {{returning a value borrowed from this function's caller, but the return type declares lifetime 'static'}}
}

// An unannotated parameter promises nothing either.
int* $static from_plain_param(int* p) {
  return p; // viol-warning {{returning a value borrowed from this function's caller, but the return type declares lifetime 'static'}}
}

struct S {
  int x;
  // The implicit object parameter is the position after the parameter list.
  int* $static from_this() { return &x; } // viol-warning {{returning a value borrowed from this function's caller, but the return type declares lifetime 'static'}}
  int* $static from_static_this() $static { return &x; }
};

// A return that borrows from nothing at all is fine.
int* $static from_nothing() { return nullptr; }

//===----------------------------------------------------------------------===//
// A `$static` parameter demands the same of its argument
//===----------------------------------------------------------------------===//

void sink(int* $static p); // viol-note 4 {{parameter declares lifetime 'static' here}}

void pass_global() { sink(&g); }
void pass_function_static() { static int x; sink(&x); }
void pass_new() { sink(new int(1)); }
void pass_nothing() { sink(nullptr); }

void pass_local() {
  int x = 0;
  sink(&x); // viol-warning {{argument is not known to live forever, but parameter 'p' declares lifetime 'static'}}
}

void forward_static(int* $static p) { sink(p); }
void forward_unknown(int* $unknown p) { sink(p); }

LIFETIME_PARAMS("a")
void forward_named(int* $a p) {
  sink(p); // viol-warning {{argument is not known to live forever, but parameter 'p' declares lifetime 'static'}}
}

void forward_plain(int* p) {
  sink(p); // viol-warning {{argument is not known to live forever, but parameter 'p' declares lifetime 'static'}}
}

// Only one report per argument, however many expiring loans reach it.
void pass_either(bool c) {
  int x = 0, y = 0;
  int* p = c ? &x : &y;
  sink(p); // viol-warning {{argument is not known to live forever, but parameter 'p' declares lifetime 'static'}}
}

//===----------------------------------------------------------------------===//
// `$unknown` suppresses what would otherwise be reported
//===----------------------------------------------------------------------===//

// Without the opt-out this call would be governed by `lifetimebound` and the
// result would be reported as dangling. The signature says no lifetime applies
// to the result, so it holds no loans and there is nothing to report.
LIFETIME_PARAMS("a")
int* $unknown opaque(int* $a p LB);

// Marks a use for -Wlifetime-safety. `(void)*p` is not one: a discarded-value
// expression reads nothing.
void use(int);

void use_after_scope_opaque() {
  int* p = nullptr;
  {
    int x = 0;
    p = opaque(&x);
  }
  use(*p);
}

// The same shape with an ordinary lifetime is reported, which is what makes
// the case above a suppression rather than a gap in the analysis.
LIFETIME_PARAMS("a")
int* $a transparent(int* $a p LB);

void use_after_scope_transparent() {
  int* p = nullptr;
  {
    int x = 0;
    // dangling-warning@+1 {{local variable 'x' does not live long enough}}
    p = transparent(&x); // dangling-note {{result of call to 'transparent' aliases the storage of local variable 'x' because parameter 'p' is marked as lifetimebound}}
  } // dangling-note {{local variable 'x' is destroyed here}}
  use(*p); // dangling-note {{later used here}}
}

//===----------------------------------------------------------------------===//
// `lifetimebound` cannot agree with a distinguished return
//===----------------------------------------------------------------------===//

// `lifetimebound` asserts the result may borrow from the parameter; neither
// distinguished lifetime does. The signature is what the analysis follows, so
// the attribute would simply be ignored.
int* $static bound_static(int* p LB) { // conflict-warning {{'lifetimebound' says the result may borrow from this parameter, but the return type declares lifetime 'static', which does not borrow from the parameters}}
  // conflict-note@-1 {{return type declares lifetime 'static' here}}
  return &g;
}

int* $unknown bound_unknown(int* p LB) { // conflict-warning {{'lifetimebound' says the result may borrow from this parameter, but the return type declares lifetime 'unknown', which does not borrow from the parameters}}
  // conflict-note@-1 {{return type declares lifetime 'unknown' here}}
  return p;
}

struct T {
  int x;
  int* $static bound_this() LB { // conflict-warning {{'lifetimebound' says the result may borrow from the implicit object parameter, but the return type declares lifetime 'static', which does not borrow from the parameters}}
    // conflict-note@-1 {{return type declares lifetime 'static' here}}
    return &g;
  }
};

// A `$static` return with no `lifetimebound` anywhere is unremarkable.
int* $static unbound(int* p) { return &g; }
