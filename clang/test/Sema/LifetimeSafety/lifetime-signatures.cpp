// RUN: %clang_cc1 -mllvm -debug-only=LifetimeSignatures -Wlifetime-safety %s 2>&1 | FileCheck %s
// REQUIRES: asserts

// Tests that Crubit-style named lifetime annotations are read off the AST and
// elaborated into a lifetime signature. These annotations do not yet influence
// the analysis; this only checks what is parsed.

#define $(l) [[clang::annotate_type("lifetime", #l)]]
#define LIFETIME_PARAMS(...) [[clang::annotate("lifetime_params", __VA_ARGS__)]]
#define $a $(a)
#define $b $(b)
#define $static $(static)
#define $unknown $(unknown)

int global;

// CHECK-LABEL: Lifetime signature for basic:
// CHECK-NEXT:   declared: $a
// CHECK-NEXT:   function-type: <none>
// CHECK-NEXT:   return: $a
// CHECK-NEXT:   param 0 ('x'): $a
// CHECK-NEXT:   param 1 ('y'): $b
LIFETIME_PARAMS("a")
int& $a basic(int& $a x, int& $b y) { return x; }

// Per-level placement: the outer `*` carries $a, the inner `*` carries $b.
// CHECK-LABEL: Lifetime signature for per_level:
// CHECK-NEXT:   declared: <none>
// CHECK-NEXT:   function-type: <none>
// CHECK-NEXT:   return: <none>
// CHECK-NEXT:   param 0 ('p'): $a, $b
void per_level(int* $b * $a p) { (void)p; }

// The distinguished lifetime names are recognized.
// CHECK-LABEL: Lifetime signature for distinguished:
// CHECK-NEXT:   declared: <none>
// CHECK-NEXT:   function-type: <none>
// CHECK-NEXT:   return: <none>
// CHECK-NEXT:   param 0 ('s'): $static
// CHECK-NEXT:   param 1 ('u'): $unknown
void distinguished(int& $static s, int& $unknown u) { (void)s; (void)u; }

// An annotation after the parameter list appertains to the function type, not
// to the return value, and is reported separately.
// CHECK-LABEL: Lifetime signature for trailing:
// CHECK-NEXT:   declared: <none>
// CHECK-NEXT:   function-type: $a
// CHECK-NEXT:   return: <none>
int& trailing() $a { return global; }

// Annotations on types do not merge across redeclarations, so the signature
// must be recovered from the declaration that spelled them.
int& $a split_decl(int& $a x);
// CHECK-LABEL: Lifetime signature for split_decl:
// CHECK-NEXT:   declared: <none>
// CHECK-NEXT:   function-type: <none>
// CHECK-NEXT:   return: $a
// CHECK-NEXT:   param 0 ('x'): $a
int& split_decl(int& x) { return x; }

// A view-like class type carries a lifetime slot of its own once annotated.
struct LIFETIME_PARAMS("a") Ref {
  int& $a r;
};

// CHECK-LABEL: Lifetime signature for takes_ref:
// CHECK-NEXT:   declared: <none>
// CHECK-NEXT:   function-type: <none>
// CHECK-NEXT:   return: <none>
// CHECK-NEXT:   param 0 ('r'): $a
void takes_ref(Ref $a r) { (void)r; }

// Methods: the implicit object parameter is not an explicit parameter.
struct S {
  // CHECK-LABEL: Lifetime signature for S::method:
  // CHECK-NEXT:   declared: <none>
  // CHECK-NEXT:   function-type: <none>
  // CHECK-NEXT:   return: $a
  // CHECK-NEXT:   param 0 ('x'): $a
  int& $a method(int& $a x) { return x; }
};

// Unannotated functions produce no output at all.
// CHECK-NOT: Lifetime signature for unannotated
int& unannotated(int& x) { return x; }
