// RUN: %clang_cc1 -mllvm -debug-only=LifetimeSignatures -fsyntax-only \
// RUN:   -Wlifetime-safety-named-lifetimes %s 2>&1 | FileCheck %s
// REQUIRES: asserts

// A lifetime binds to the level of the type it is written on. Levels are
// annotated independently, so an unannotated level still occupies its slot and
// the levels after it stay put.
//
// This matches Crubit, which attaches lifetimes per node of its type tree
// rather than to a flat list: rs_bindings_from_cc/importer.cc collects the
// annotations at each level as it recurses into pointees, and a pointer node
// accepts at most one.

#define $(l) [[clang::annotate_type("lifetime", #l)]]
#define LIFETIME_PARAMS(...) [[clang::annotate("lifetime_params", __VA_ARGS__)]]
#define $a $(a)
#define $b $(b)

struct LIFETIME_PARAMS("v") SV { const char* p; };

//===----------------------------------------------------------------------===//
// The outer level is the one written after the last `*`.
//===----------------------------------------------------------------------===//

// CHECK-LABEL: Lifetime signature for outer_only:
// CHECK: param 0 ('p'): $a
LIFETIME_PARAMS("a", "b")
void outer_only(int** $a p) {}

//===----------------------------------------------------------------------===//
// Annotating only an inner level leaves a hole in front of it. Collapsing the
// hole would silently turn this into `outer_only`, which says the opposite.
//===----------------------------------------------------------------------===//

// CHECK-LABEL: Lifetime signature for inner_only:
// CHECK: param 0 ('p'): <elided>, $a
LIFETIME_PARAMS("a", "b")
void inner_only(int* $a * p) {}

//===----------------------------------------------------------------------===//
// Both levels written.
//===----------------------------------------------------------------------===//

// CHECK-LABEL: Lifetime signature for both_levels:
// CHECK: param 0 ('p'): $a, $b
LIFETIME_PARAMS("a", "b")
void both_levels(int* $b * $a p) {}

//===----------------------------------------------------------------------===//
// Stacking both on one level is ill-formed -- a pointer level has room for one
// -- and is diagnosed separately. The excess is dropped rather than allowed to
// slide down onto the level below, which would give this the meaning of
// `both_levels`.
//===----------------------------------------------------------------------===//

// CHECK-LABEL: Lifetime signature for stacked:
// CHECK: param 0 ('p'): $a
LIFETIME_PARAMS("a", "b")
void stacked(int** $a $b p) {}

//===----------------------------------------------------------------------===//
// A record contributes the lifetimes its definition declares, at its own
// level. Annotating the pointee rather than the pointer is how an
// out-parameter says "the view written here has lifetime 'a'".
//===----------------------------------------------------------------------===//

// CHECK-LABEL: Lifetime signature for view_out_param:
// CHECK: param 0 ('out'): <elided>, $a
LIFETIME_PARAMS("a", "b")
void view_out_param(SV $a * out) {}

// CHECK-LABEL: Lifetime signature for pointer_to_view:
// CHECK: param 0 ('out'): $a
LIFETIME_PARAMS("a", "b")
void pointer_to_view(SV* $a out) {}

//===----------------------------------------------------------------------===//
// Trailing holes carry no information and are dropped, so a type with nothing
// written on it elaborates to an empty list rather than a run of holes.
//===----------------------------------------------------------------------===//

// CHECK-LABEL: Lifetime signature for unannotated:
// CHECK: param 0 ('p'): <none>
LIFETIME_PARAMS("a")
void unannotated(int** p) {}

//===----------------------------------------------------------------------===//
// The return type is elaborated the same way. An elided outermost slot states
// no contract, so nothing is enforced against the body.
//===----------------------------------------------------------------------===//

// CHECK-LABEL: Lifetime signature for inner_return:
// CHECK: return: <elided>, $a
LIFETIME_PARAMS("a")
int* $a * inner_return(int* $a * p) { return p; }
