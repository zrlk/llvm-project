// RUN: %clang_cc1 -fsyntax-only -Wlifetime-safety \
// RUN:   -Wlifetime-safety-named-lifetimes \
// RUN:   -Wlifetime-safety-named-lifetime-violation \
// RUN:   -Wlifetime-safety-named-lifetime-suggestions -verify %s

// A container template mirroring the std::vector API, annotated as
// descriptively as the named-lifetime scheme allows. It serves two purposes:
//
//  * a regression test for what the scheme already models on a realistic
//    container: element lifetimes entering through constructors, references
//    and iterators borrowing from the container, and element lifetimes read
//    back out through accessors and iterators;
//  * a catalogue of what the scheme cannot express yet. Every such place is
//    marked `INEXPRESSIBLE:` (the annotation language has no way to say it)
//    or `NOT MODELLED:` (it can be written, but the analysis ignores it), with
//    a pointer to the design document that discusses it.
//
// Lifetime names used throughout:
//   'e'  the lifetime of the borrows *held by the elements* (Rust: the 'a in
//        Vec<&'a str>). A class lifetime parameter of Vector.
//   'c'  the lifetime of a borrow *of the container itself*, as carried by
//        iterators. A class lifetime parameter of the iterator types, and a
//        member lifetime parameter of the members that produce iterators.
//   unwritten outer reference levels on member results default to the
//   lifetime of `this` (see record-elision.cpp).
//
// Design documents (Google-internal): named_lifetimes_proposal.md (§0 "Where
// exactly the model falls short"), lifetime_bounds.md,
// template_arg_lifetimes_plan.md.

#define $(l) [[clang::annotate_type("lifetime", #l)]]
#define $2(l1, l2) [[clang::annotate_type("lifetime", #l1, #l2)]]
#define LIFETIME_PARAMS(...) [[clang::annotate("lifetime_params", __VA_ARGS__)]]
#define $a $(a)
#define $b $(b)
#define $c $(c)
#define $e $(e)
#define $f $(f)

using size_t = decltype(sizeof(0));
void use(int);

// A view with one lifetime: the element type the examples mostly use.
struct LIFETIME_PARAMS("a") SV {
  const int* $a p;
};

// A record with two lifetimes, to show what happens when T does not have
// exactly one lifetime slot.
struct LIFETIME_PARAMS("a", "b") Pair {
  const int* $a x;
  const int* $b y;
};

//===----------------------------------------------------------------------===//
// The container
//===----------------------------------------------------------------------===//

// INEXPRESSIBLE: "whatever lifetimes T has". The element lifetime is written as
// `T $e`, which reads correctly only when T has exactly one lifetime slot
// (`SV`, `const int*`). For a T with no slots (`int`) the annotation is
// meaningless, and for a T with two (`Pair`) it is wrong; neither is
// diagnosed (see "Instantiations" below). Rust writes `Vec<T>` with T opaque
// and puts the lifetime inside T; the equivalent here needs lifetimes to
// survive in template arguments (`Vector<SV $a>`), which they do not. See
// template_arg_lifetimes_plan.md.
//
// INEXPRESSIBLE: the allocator. A stateful allocator is a borrow the vector
// holds, i.e. a second class lifetime whose relation to 'e is unconstrained.
// Omitted here.
template <class T>
class LIFETIME_PARAMS("e") Vector {
  // INEXPRESSIBLE: ownership. `data_` points to storage owned by *this, which
  // would naturally be spelled `T $e* $(this) data_`. There is no lifetime for
  // "owned by the enclosing object", so the pointer level is left unannotated.
  // Consequently the inline bodies below, which return references into
  // `data_`, are accepted vacuously (the pointer carries no loans), not
  // because the checker has verified that they borrow from *this.
  T $e* data_;
  size_t size_ = 0;
  size_t cap_ = 0;

public:
  using value_type = T;
  using size_type = size_t;
  // INEXPRESSIBLE (as a typedef): `reference` would be `T $e&` with the
  // reference level borrowing from the object it was obtained from; a typedef
  // has no object. Members spell the type out instead.

  //--- Iterators -------------------------------------------------------------

  // An iterator borrows the container ('c) and yields elements whose borrows
  // live for 'e. Dereferencing yields a reference into the container, so the
  // reference level is 'c, not the lifetime of the iterator object: an
  // element reference stays valid after the iterator is gone.
  //
  // INEXPRESSIBLE: 'e outlives 'c (a container cannot outlive the borrows it
  // holds). This is an implied bound from well-formedness; it is encoded for
  // class lifetimes versus `this`, but not between two class lifetimes. See
  // lifetime_bounds.md §3.2 ("Return an element of a borrowed container").
  class LIFETIME_PARAMS("c", "e") iterator {
    T $e* $c p_;

  public:
    T $e& $c operator*() const { return *p_; }
    T $e* $c operator->() const { return p_; }
    // The result is *this; the elided lifetime of `this` is right.
    iterator& operator++() {
      ++p_;
      return *this;
    }
    // Comparing iterators into different containers is undefined behaviour.
    // INEXPRESSIBLE: "points into the same object", which is provenance, not
    // a lifetime. Writing `iterator $2(c, e) other` only requires the two
    // borrows to share a lifetime.
    bool operator!=(const iterator& other) const;
  };

  class LIFETIME_PARAMS("c", "e") const_iterator {
    const T $e* $c p_;

  public:
    // NOT MODELLED: `iterator` converts to `const_iterator`, and the
    // conversion should carry both lifetimes across. A converting constructor
    // with a written signature would do it, but the parameter would have to
    // name the nested type of the same specialization; omitted.
    const T $e& $c operator*() const { return *p_; }
    const_iterator& operator++() {
      ++p_;
      return *this;
    }
  };

  //--- Construction and assignment -------------------------------------------

  Vector();
  // The value's borrows become the elements' borrows.
  Vector(size_t n, const T $e& value);
  // INEXPRESSIBLE: a range constructor. `template <class It> Vector(It, It)`
  // copies elements whose borrows live for "whatever lifetimes It's
  // value_type has"; tying that to 'e is a bound on a type parameter (Rust:
  // `I: Iterator<Item = T>, T: 'e`). See lifetime_bounds.md §4 item 1 and §7.
  //
  // INEXPRESSIBLE: `Vector(std::initializer_list<T $e>)`, for the same reason
  // as `Vector<SV $a>`: lifetimes inside template arguments are dropped.
  //
  // Copies and moves keep the element lifetime. Under the injected class name
  // `Vector $e` means "this specialization, with element lifetime 'e".
  Vector(const Vector $e& other);
  Vector(Vector $e&& other);

  // NOT MODELLED: copy-assigning from a vector whose elements live *longer*
  // than 'e is sound, but the acceptance relation for abstract lifetimes is
  // exact (no covariance), so a caller with two names must rename them. See
  // lifetime_bounds.md §3.3.
  Vector $e& operator=(const Vector $e& other);
  Vector $e& operator=(Vector $e&& other);
  void assign(size_t n, const T $e& value);

  //--- Element access --------------------------------------------------------

  // The reference level borrows from *this (elided); the element level is 'e.
  T $e& operator[](size_t i) { return data_[i]; }
  const T $e& operator[](size_t i) const { return data_[i]; }
  T $e& at(size_t i);
  const T $e& at(size_t i) const;
  T $e& front() { return data_[0]; }
  const T $e& front() const { return data_[0]; }
  T $e& back() { return data_[size_ - 1]; }
  T $e* data() { return data_; }
  const T $e* data() const { return data_; }

  //--- Iterators -------------------------------------------------------------

  // The iterator's container borrow is the borrow of *this: 'c is a member
  // lifetime parameter that names `this` (trailing `$c`).
  LIFETIME_PARAMS("c") iterator $2(c, e) begin() $c;
  LIFETIME_PARAMS("c") iterator $2(c, e) end() $c;
  LIFETIME_PARAMS("c") const_iterator $2(c, e) begin() const $c;
  LIFETIME_PARAMS("c") const_iterator $2(c, e) end() const $c;
  LIFETIME_PARAMS("c") const_iterator $2(c, e) cbegin() const $c;
  LIFETIME_PARAMS("c") const_iterator $2(c, e) cend() const $c;

  //--- Capacity --------------------------------------------------------------

  bool empty() const { return size_ == 0; }
  size_t size() const { return size_; }
  size_t capacity() const { return cap_; }
  // INEXPRESSIBLE: invalidation. `reserve`, `shrink_to_fit`, `clear`,
  // `push_back`, `insert`, `erase`, `resize` and assignment invalidate
  // references and iterators into *this. Rust gets this from `&mut self`
  // excluding outstanding shared borrows; there is no annotation for "ends
  // every borrow of this object". The engine's invalidation check recognises
  // std containers by name only, so it does not apply to this class (see
  // `invalidation_not_modelled` below).
  void reserve(size_t n);
  void shrink_to_fit();

  //--- Modifiers -------------------------------------------------------------

  void clear();

  // NOT MODELLED: storing into *this. The value's borrows should flow into the
  // container's 'e slot, but call-site substitution only flows arguments into
  // the result, and a void member has none. Gap 2 in named_lifetimes_proposal.md
  // §0. The bodies of such members cannot be checked either (Gap 3).
  void push_back(const T $e& value);
  void push_back(T $e&& value);

  // INEXPRESSIBLE: `template <class... Args> T& emplace_back(Args&&... args)`.
  // The element is constructed from arbitrary arguments; which of their
  // borrows end up in the element is decided by T's constructor, and a pack
  // has no per-element lifetime syntax.

  void pop_back();
  void resize(size_t n);
  void resize(size_t n, const T $e& value);

  // `pos` must be an iterator into *this, and the result is one.
  // INEXPRESSIBLE: "into *this" (provenance); `$2(c, e)` only says that `pos`
  // borrows something for 'c, the same lifetime as `this` here.
  LIFETIME_PARAMS("c")
  iterator $2(c, e) insert(const_iterator $2(c, e) pos, const T $e& value) $c;
  LIFETIME_PARAMS("c")
  iterator $2(c, e) erase(const_iterator $2(c, e) pos) $c;
  LIFETIME_PARAMS("c")
  iterator $2(c, e) erase(const_iterator $2(c, e) first,
                          const_iterator $2(c, e) last) $c;

  // Both vectors are written through, so both element lifetimes are pinned
  // (invariant); swapping requires them to be equal, which one name says
  // exactly. Rust's `mem::swap` has the same signature.
  void swap(Vector $e& other);

  // Splicing elements out of another vector into this one: the source's
  // elements must outlive 'e.
  // INEXPRESSIBLE: an outlives bound `f: e`. Both vectors are written through
  // (the source is emptied), so renaming 'f to 'e would force callers'
  // element lifetimes to be equal. This is the one shape that genuinely
  // requires declared bounds; lifetime_bounds.md §3.2, first row.
  LIFETIME_PARAMS("f") void append_from(Vector<T> $f& source);
};

// Non-member swap: the same invariance argument as the member.
template <class T>
LIFETIME_PARAMS("e") void swap(Vector<T> $e& x, Vector<T> $e& y);

// Comparison reads both sides and keeps nothing, so the two element lifetimes
// are unrelated.
template <class T>
LIFETIME_PARAMS("e", "f")
bool operator==(const Vector<T> $e& x, const Vector<T> $f& y);

//===----------------------------------------------------------------------===//
// What the annotations already buy at call sites
//===----------------------------------------------------------------------===//

// The element lifetime enters through the constructor and comes back out of
// `front`, so a copy of an element is known to borrow the dead buffer.
void element_from_constructor() {
  SV r;
  {
    int buf = 0;
    Vector<SV> v(3, SV{&buf}); // expected-warning {{local variable 'buf' does not live long enough}}
    r = v.front(); // expected-note {{result of call to 'front' aliases the storage of local variable 'buf'}}
  } // expected-note {{local variable 'buf' is destroyed here}}
  use(*r.p); // expected-note {{later used here}}
}

// A reference to an element borrows the vector itself.
void element_reference_outlives_vector() {
  SV* r;
  {
    Vector<SV> v;
    r = &v[0]; // expected-warning {{local variable 'v' does not live long enough}} expected-note {{result of call to 'operator[]' aliases the storage of local variable 'v'}}
  } // expected-note {{local variable 'v' is destroyed here}}
  use(*r->p); // expected-note {{later used here}}
}

// An element reference obtained through an iterator borrows the vector ('c),
// not the iterator: the iterator going out of scope is not reported, the
// vector going out of scope is.
void iterator_reference_outlives_vector() {
  SV* r;
  {
    Vector<SV> v;
    Vector<SV>::iterator it = v.begin(); // expected-warning {{local variable 'v' does not live long enough}} expected-note {{result of call to 'begin' aliases the storage of local variable 'v'}}
    r = &*it; // expected-note {{local variable 'it' aliases the storage of local variable 'v'}} expected-note {{result of call to 'operator*' aliases the storage of local variable 'v'}}
  } // expected-note {{local variable 'v' is destroyed here}}
  use(*r->p); // expected-note {{later used here}}
}

void iterator_reference_outlives_iterator() {
  Vector<SV> v;
  SV* r;
  {
    Vector<SV>::iterator it = v.begin();
    r = &*it;
  }
  use(*r->p);
}

// The element lifetime also survives a trip through an iterator.
void element_through_iterator() {
  SV r;
  {
    int buf = 0;
    Vector<SV> v(1, SV{&buf}); // expected-warning {{local variable 'buf' does not live long enough}}
    Vector<SV>::iterator it = v.begin(); // expected-note {{result of call to 'begin' aliases the storage of local variable 'buf'}}
    r = *it; // expected-note {{local variable 'it' aliases the storage of local variable 'buf'}} expected-note {{result of call to 'operator*' aliases the storage of local variable 'buf'}}
  } // expected-note {{local variable 'buf' is destroyed here}}
  use(*r.p); // expected-note {{later used here}}
}

//===----------------------------------------------------------------------===//
// Function bodies that use the container
//===----------------------------------------------------------------------===//

LIFETIME_PARAMS("e")
SV $e first(Vector<SV> $e& v) { return v.front(); }

LIFETIME_PARAMS("e", "f")
SV $f first_wrong(Vector<SV> $e& v) {
  return v.front(); // expected-warning {{returning a value borrowed from lifetime 'e', but the return type declares lifetime 'f'}} expected-note {{this would be allowed if lifetime 'e' were declared to outlive lifetime 'f', which cannot currently be expressed}}
}

// Storing a value with the container's own element lifetime: fine.
LIFETIME_PARAMS("e")
void store_same(Vector<SV> $e& v, SV $e s) { v.push_back(s); }

// Storing a value with an unrelated lifetime is unsound and should be
// rejected (Rust rejects the analogous `fn f<'e, 'f>(v: &mut Vec<&'e i32>,
// s: &'f i32)`). Once it is, accepting it again needs either renaming 'f to
// 'e or an outlives bound `f: e`.
// NOT MODELLED: the store through `v` is invisible (Gaps 2 and 3).
LIFETIME_PARAMS("e", "f")
void store_unrelated(Vector<SV> $e& v, SV $f s) { v.push_back(s); }

//===----------------------------------------------------------------------===//
// Gaps, pinned at their current behaviour
//===----------------------------------------------------------------------===//

// NOT MODELLED: the pushed element's borrow never reaches `v`, so the dangling
// element read back by `front` is not reported. Gap 2.
void push_back_not_modelled() {
  SV r;
  Vector<SV> v;
  {
    int buf = 0;
    v.push_back(SV{&buf});
    r = v.front();
  }
  use(*r.p);
}

// INEXPRESSIBLE: `clear` ends every borrow of `v`, so `r` dangles. The same
// code with std::vector is reported by -Wlifetime-safety-invalidation, which
// matches std containers by name.
void invalidation_not_modelled() {
  Vector<SV> v(1, SV{nullptr});
  SV& r = v.front();
  v.clear();
  use(*r.p);
}

//===----------------------------------------------------------------------===//
// Instantiations: `T $e` with T having other than one lifetime slot
//===----------------------------------------------------------------------===//

// A pointer element has exactly one slot, and `T $e` names it.
void pointer_elements() {
  const int* r;
  {
    int a = 0;
    Vector<const int*> v(1, &a); // expected-warning {{local variable 'a' does not live long enough}}
    r = v.front(); // expected-note {{result of call to 'front' aliases the storage of local variable 'a'}}
  } // expected-note {{local variable 'a' is destroyed here}}
  use(*r); // expected-note {{later used here}}
}

// `int` has no slots; `int $e` is meaningless and silently ignored.
// FIXME: arguably a well-formedness error in the instantiation, but the
// signature check does not run on instantiated members.
int int_elements(Vector<int>& v) { return v.front() + v[0]; }

// `Pair` has two slots; `Pair $e` supplies one. The first slot is tracked.
void pair_elements_first_slot() {
  const int* r;
  {
    int a = 0;
    static int b;
    Vector<Pair> v(1, Pair{&a, &b}); // expected-warning {{local variable 'a' does not live long enough}}
    r = v.front().x; // expected-note {{result of call to 'front' aliases the storage of local variable 'a'}}
  } // expected-note {{local variable 'a' is destroyed here}}
  use(*r); // expected-note {{later used here}}
}

// FIXME: the second slot is not tracked. `Pair $e` is short by one lifetime;
// in a non-template that is diagnosed, but well-formedness is not checked in
// instantiations. The unwritten slot is treated as `$unknown`, so the
// constructor drops `b` and `front().y` borrows nothing: the dangle is
// missed. An arity mismatch (`Pair` takes two lifetimes, one was written)
// should be diagnosed at instantiation; the real fix is a way to say
// "whatever lifetimes T has" (template_arg_lifetimes_plan.md).
void pair_elements_second_slot() {
  const int* r;
  {
    static int a;
    int b = 0;
    Vector<Pair> v(1, Pair{&a, &b});
    r = v.front().y;
  }
  use(*r);
}

// The unwritten slot must not be filled in by `$this` elision either: that
// would make `front().y` appear to borrow the vector, and `y` pointing to
// static storage would be reported once the vector is gone.
void pair_elements_second_slot_no_false_borrow() {
  static int a, b;
  const int* r;
  {
    Vector<Pair> v(1, Pair{&a, &b});
    r = v.front().y;
  }
  use(*r);
}
