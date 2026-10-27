// RUN: %clang_cc1 -fsyntax-only -Wlifetime-safety \
// RUN:   -Wlifetime-safety-experimental-field-origin-escape \
// RUN:   -Wlifetime-safety-named-lifetime-violation -verify=viol %s
// RUN: %clang_cc1 -fsyntax-only \
// RUN:   -Wlifetime-safety-experimental-field-origin-escape \
// RUN:   -Wlifetime-safety-named-lifetime-suggestions -verify=suggest %s

// The field-origin-escape warning and named lifetimes on fields.
//
// Trunk's warning points out a member function whose result depends on what a
// field refers to rather than on `*this`, a contract `lifetimebound` cannot
// express. A lifetime written on the field's type expresses exactly that
// contract, so where the field names one, the named rules are in charge: a
// return annotated with the field's lifetime is verified, and an elided return
// gets the named-return suggestion. The trunk warning stays for fields that
// name nothing.

#define $(l) [[clang::annotate_type("lifetime", #l)]]
#define LIFETIME_PARAMS(...) [[clang::annotate("lifetime_params", __VA_ARGS__)]]
#define $a $(a)

struct Plain {
  int* p; // viol-note {{if field 'p' is owned by the class, mark the method [[clang::lifetimebound]]}} \
          // suggest-note {{if field 'p' is owned by the class, mark the method [[clang::lifetimebound]]}}
  int* get() const { return p; } // viol-warning {{return value depends on the object referenced by field 'p', not on '*this'}} \
                                 // suggest-warning {{return value depends on the object referenced by field 'p', not on '*this'}} \
                                 // viol-note {{returned here}} suggest-note {{returned here}}
};

struct LIFETIME_PARAMS("a") NamedOnly {
  int* $a p;
  // The suggestion also holds with the experimental group enabled.
  int* get() const { return p; } // suggest-warning {{return type of 'get' defaults to the lifetime of the object, but everything it returns is borrowed from lifetime 'a'; annotate the return type with lifetime 'a' to let callers rely on it}}
};

struct LIFETIME_PARAMS("a") Named {
  int* $a p;
  int* q; // viol-note {{if field 'q' is owned by the class, mark the method [[clang::lifetimebound]]}} \
          // suggest-note {{if field 'q' is owned by the class, mark the method [[clang::lifetimebound]]}}

  // The field's lifetime, verified by the named rules: no trunk warning.
  int* $a get_a() const { return p; }

  // Elided return: the named-return suggestion, not the trunk warning. The
  // field's `$this.p` placeholder does not block it.
  int* get() const { return p; } // suggest-warning {{return type of 'get' defaults to the lifetime of the object, but everything it returns is borrowed from lifetime 'a'; annotate the return type with lifetime 'a' to let callers rely on it}}

  // A field of the same class that names nothing keeps the trunk warning, and
  // an elided return reaching it gets no named suggestion.
  int* get_q() const { return q; } // viol-warning {{return value depends on the object referenced by field 'q', not on '*this'}} \
                                   // suggest-warning {{return value depends on the object referenced by field 'q', not on '*this'}} \
                                   // viol-note {{returned here}} suggest-note {{returned here}}
};
