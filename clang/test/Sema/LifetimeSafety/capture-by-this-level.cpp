// RUN: %clang_cc1 -fsyntax-only -Wlifetime-safety -Wlifetime-safety-suggestions -verify %s

// A borrow captured via [[clang::lifetime_capture_by_this]] is held by the
// object `*this`, not by the `this` pointer value.

struct S {
  int member = 0;
  const int *p = nullptr;
  void store(const int &x [[clang::lifetime_capture_by_this]]);
  int read() const;

  // The address of a member borrows `*this` only; the captured parameter does
  // not flow into the result, so `x` needs no [[clang::lifetimebound]].
  int *member_addr(const int &x [[clang::lifetime_capture_by_this]])
      [[clang::lifetimebound]] {
    store(x);
    return &member;
  }

  // The captured local dangles from the object at the method's exit. Reading
  // `member` loads through the `this` pointer, which holds no capture, so it
  // is not the use.
  int captures_then_reads_member() {
    {
      int local = 1;
      store(local); // expected-warning {{local variable 'local' does not live long enough}}
    }               // expected-note {{local variable 'local' is destroyed here}}
    return member;
  } // expected-note {{later used here}}
};
