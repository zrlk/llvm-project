// A lifetime written after the parameter list of an instance method names the
// lifetime of the implicit object parameter. This matches Crubit, which
// collects trailing lifetimes off the function type and assigns them to `this`.
//
// The three RUN lines below exercise disjoint diagnostic groups, so each one
// sees only the diagnostics it is responsible for.

// RUN: %clang_cc1 -fsyntax-only -verify=wf \
// RUN:   -Wlifetime-safety-named-lifetimes %s
// RUN: %clang_cc1 -fsyntax-only -verify=agree \
// RUN:   -Wlifetime-safety-lifetimebound-conflict \
// RUN:   -Wlifetime-safety-named-lifetime-suggestions %s
// RUN: %clang_cc1 -fsyntax-only -verify=flow \
// RUN:   -Wlifetime-safety -Wlifetime-safety-named-lifetime-violation %s

#define $(l) [[clang::annotate_type("lifetime", #l)]]
#define LIFETIME_PARAMS(...) [[clang::annotate("lifetime_params", __VA_ARGS__)]]
#define $a $(a)
#define $b $(b)
#define LB [[clang::lifetimebound]]

struct S {
  int x;

  // The ordinary case: the result borrows from the object, so both name 'a'.
  LIFETIME_PARAMS("a")
  int* $a get() $a; // agree-note {{return type declares lifetime 'a' here}}

  // The object is 'b' while the result is 'a', which asserts that the result
  // does not borrow from the object.
  LIFETIME_PARAMS("a", "b")
  int* $a mismatch() $b;

  // ... and 'lifetimebound' asserts the opposite, so the two contradict.
  LIFETIME_PARAMS("a", "b")
  int* $a conflict() $b LB; // agree-note {{return type declares lifetime 'a' here}}

  // `this` has type 'S *', which carries exactly one lifetime.
  LIFETIME_PARAMS("a", "b")
  int* $a too_many() $a $b; // wf-warning {{type 'S *' takes one lifetime annotation, but 2 were written}} agree-note {{return type declares lifetime 'a' here}}
};

int* S::get() { return &x; } // agree-warning {{the implicit object parameter shares lifetime 'a' with the return type but is not marked 'lifetimebound'}}
int* S::mismatch() { return &x; } // flow-warning {{returning a value borrowed from lifetime 'b', but the return type declares lifetime 'a'}} flow-note {{this would be allowed if lifetime 'b' were declared to outlive lifetime 'a', which cannot currently be expressed}}
int* S::conflict() { return &x; } // agree-warning {{'lifetimebound' says the result may borrow from the implicit object parameter, but it declares lifetime 'b' while the return type declares lifetime 'a'}} flow-warning {{returning a value borrowed from lifetime 'b', but the return type declares lifetime 'a'}} flow-note {{this would be allowed if lifetime 'b' were declared to outlive lifetime 'a', which cannot currently be expressed}}
int* S::too_many() { return &x; } // agree-warning {{the implicit object parameter shares lifetime 'a' with the return type but is not marked 'lifetimebound'}}

//===----------------------------------------------------------------------===//
// Without an implicit object parameter there is nothing for a trailing
// lifetime to name, so it remains misplaced.
//===----------------------------------------------------------------------===//

static int g;

LIFETIME_PARAMS("a")
int* free_trailing() $a { return &g; } // wf-warning {{lifetime annotation after the parameter list applies to the function type and is ignored; write it on the return type instead}}

struct T {
  LIFETIME_PARAMS("a")
  static int* static_trailing() $a; // wf-warning {{lifetime annotation after the parameter list applies to the function type and is ignored; write it on the return type instead}}
};

int* T::static_trailing() { return &g; }

//===----------------------------------------------------------------------===//
// The lifetime of the object flows to the result at the call site.
//===----------------------------------------------------------------------===//

// Marks a use for -Wlifetime-safety. Returning `r` instead would be reported
// as a return of stack memory, which carries no alias-chain note.
void use(int);

void call_site(S* p) {
  int* r = p->get();
  {
    S local;
    r = local.get(); // flow-warning {{local variable 'local' does not live long enough}} flow-note {{result of call to 'get' aliases the storage of local variable 'local'}}
  } // flow-note {{local variable 'local' is destroyed here}}
  use(*r); // flow-note {{later used here}}
}

// The object's lifetime is only borrowed when the signature says so.
void no_flow_from_object(S* p) {
  int* r = p->mismatch();
  {
    S local;
    r = local.mismatch();
  }
  use(*r);
}
