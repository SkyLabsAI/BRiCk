(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(** clang declares an implicit special member only once something uses it, and
    cpp2v emits the ones it has not declared as placeholders ([Oimplicit_*] in
    <<parser.v>>).  So a header on its own gets placeholders where a translation
    unit that uses the header's classes gets clang's declarations.  Since the
    header is included in the use, the header's translation unit must still be
    a [sub_module] of the use's: that is what lets specifications and
    registrations made against a header carry over to its clients.  That only
    holds if each placeholder has the type clang would have declared, so the
    uses below make clang declare every implicit member the header leaves to
    a placeholder. *)

Require Import skylabs.lang.cpp.parser.
Require Import skylabs.lang.cpp.parser.plugin.cpp2v.
Require Import skylabs.lang.cpp.semantics.sub_module.

Definition get (tu : translation_unit) (n : name) :=
  (n , tu.(symbols) !! n).

(** * Every placeholder, with the [const] forms of the copy members

    Variants:
    - [Oimplicit_default_ctor]
    - [Oimplicit_copy_ctor]
    - [Oimplicit_move_ctor]
    - [Oimplicit_copy_assign] (returning [S&], not [const S&])
    - [Oimplicit_move_assign]
    - [Oimplicit_dtor]

    cf. relevant source files:
    - rocq-skylabs-brick/theories/lang/cpp/parser.v
    - rocq-skylabs-cpp2v/src/PrintDecl.cpp

 *)

#[duplicates(error)]
cpp.prog all_header prog cpp:{{
  struct S { int x; };
}}.

#[duplicates(error)]
cpp.prog all_use prog cpp:{{
  struct S { int x; };
  void test() {
    S a;                          // default constructor, destructor
    S b(a);                       // copy constructor
    S c(static_cast<S&&>(a));     // move constructor
    a = b;                        // copy assignment
    a = static_cast<S&&>(c);      // move assignment
  }
}}.

Eval vm_compute in get all_header "S::S()".
Eval vm_compute in get all_header "S::S(const S&)".
Eval vm_compute in get all_header "S::S(S&&)".
Eval vm_compute in get all_header "S::operator=(const S&)".
Eval vm_compute in get all_header "S::operator=(S&&)".
Eval vm_compute in get all_header "S::~S()".
(* clang's declaration in the use: same type, and a body, since it is used *)
Eval vm_compute in get all_use "S::operator=(const S&)".

Example all_header_sub_module_all_use :
  bool_decide (sub_module all_header all_use) = true.
Proof. vm_compute. reflexivity. Qed.

(** * The non-[const] forms of the copy members

    A member whose copy constructor and copy assignment take a non-[const]
    reference makes the enclosing class's implicit ones do so too
    (https://eel.is/c++draft/class.copy.ctor#7,
    https://eel.is/c++draft/class.copy.assign#2).  [M]'s are user-declared,
    so clang declares [N]'s eagerly (see below); [T], one level further out,
    is left to placeholders. *)

#[duplicates(error)]
cpp.prog nonconst_header prog cpp:{{
  struct M {
    M() = default;
    M(M&) = default;
    M& operator=(M&) = default;
  };
  struct N { M m; };
  struct T { N n; };
}}.

#[duplicates(error)]
cpp.prog nonconst_use prog cpp:{{
  struct M {
    M() = default;
    M(M&) = default;
    M& operator=(M&) = default;
  };
  struct N { M m; };
  struct T { N n; };
  void test() {
    T a;
    T b(a);                       // copy constructor T(T&)
    a = b;                        // copy assignment T& operator=(T&)
  }
}}.

Eval vm_compute in get nonconst_header "N::N(N&)".
Eval vm_compute in get nonconst_header "N::operator=(N&)".
Eval vm_compute in get nonconst_header "T::T(T&)".
Eval vm_compute in get nonconst_header "T::operator=(T&)".

Example nonconst_header_sub_module_nonconst_use :
  bool_decide (sub_module nonconst_header nonconst_use) = true.
Proof. vm_compute. reflexivity. Qed.

(** * Placeholders versus clang's eager declarations

    clang declares an implicit copy member of [T] eagerly, i.e. without any use,
    when deciding it needs overload resolution, which is the case when the
    corresponding member of [T]'s subobject [N] is user-declared (here,
    explicitly defaulted).  Otherwise it is left to a placeholder.  So each
    header below has, for each of [T]'s copy members, either clang's declaration
    or a placeholder, and comparing headers compares the two.  Nothing in a
    header uses these members, so clang never needs their exception
    specifications and cpp2v prints them as [Unknown], the placeholder's
    specification (BRiCk#507).  So each header is a [sub_module] of every
    other. *)

(* both of N's copy members user-declared: both of T's declared eagerly *)
#[duplicates(error)]
cpp.prog const_header prog cpp:{{
  struct N {
    N() = default;
    N(const N&) = default;
    N& operator=(const N&) = default;
  };
  struct T { N n; };
}}.

#[duplicates(error)]
cpp.prog const_use prog cpp:{{
  struct N {
    N() = default;
    N(const N&) = default;
    N& operator=(const N&) = default;
  };
  struct T { N n; };
  void test() {
    T a;
    T b(a);                       // copy constructor T(const T&)
    a = b;                        // copy assignment T& operator=(const T&)
  }
}}.

Eval vm_compute in get const_header "N::N(const N&)".
Eval vm_compute in get const_header "N::operator=(const N&)".
Eval vm_compute in get const_header "T::T(const T&)".
Eval vm_compute in get const_header "T::operator=(const T&)".

Example const_header_sub_module_const_use :
  bool_decide (sub_module const_header const_use) = true.
Proof. vm_compute. reflexivity. Qed.

(* only N's copy ctor user-declared: T's copy ctor eager, T's copy assignment a placeholder *)
#[duplicates(error)]
cpp.prog const_copy_ctor_header prog cpp:{{
  struct N {
    N() = default;
    N(const N&) = default;
  };
  struct T { N n; };
}}.

#[duplicates(error)]
cpp.prog const_copy_ctor_use prog cpp:{{
  struct N {
    N() = default;
    N(const N&) = default;
  };
  struct T { N n; };
  void test() {
    T a;
    T b(a);                       // copy constructor T(const T&)
    a = b;                        // copy assignment T& operator=(const T&)
  }
}}.

Eval vm_compute in get const_copy_ctor_header "N::N(const N&)".
Eval vm_compute in get const_copy_ctor_header "N::operator=(const N&)".
Eval vm_compute in get const_copy_ctor_header "T::T(const T&)".
Eval vm_compute in get const_copy_ctor_header "T::operator=(const T&)".

Example const_copy_ctor_header_sub_module_const_copy_ctor_use :
  bool_decide (sub_module const_copy_ctor_header const_copy_ctor_use) = true.
Proof. vm_compute. reflexivity. Qed.

(* T's [Oimplicit_copy_assign] placeholder is [ObjValue_le] clang's eager declaration *)
Example const_copy_ctor_header_sub_module_const_header :
  bool_decide (sub_module const_copy_ctor_header const_header) = true.
Proof. vm_compute. reflexivity. Qed.

(* T's eagerly declared copy assignment is unused, so [Unknown] like the placeholder *)
Eval vm_compute in sub_module_mismatch.compute const_header const_copy_ctor_header.

Example const_header_sub_module_const_copy_ctor_header :
  bool_decide (sub_module const_header const_copy_ctor_header) = true.
Proof. vm_compute. reflexivity. Qed.

Example const_copy_ctor_use_sub_module_const_use :
  bool_decide (sub_module const_copy_ctor_use const_use) = true.
Proof. vm_compute. reflexivity. Qed.

(* only N's copy assignment user-declared: T's copy assignment eager, T's copy ctor a placeholder *)
#[duplicates(error)]
cpp.prog const_copy_assignment_header prog cpp:{{
  struct N {
    N() = default;
    N& operator=(const N&) = default;
  };
  struct T { N n; };
}}.

#[duplicates(error)]
cpp.prog const_copy_assignment_use prog cpp:{{
  struct N {
    N() = default;
    N& operator=(const N&) = default;
  };
  struct T { N n; };
  void test() {
    T a;
    T b(a);                       // copy constructor T(const T&)
    a = b;                        // copy assignment T& operator=(const T&)
  }
}}.

Eval vm_compute in get const_copy_assignment_header "N::N(const N&)".
Eval vm_compute in get const_copy_assignment_header "N::operator=(const N&)".
Eval vm_compute in get const_copy_assignment_header "T::T(const T&)".
Eval vm_compute in get const_copy_assignment_header "T::operator=(const T&)".

Example const_copy_assignment_header_sub_module_const_copy_assignment_use :
  bool_decide (sub_module const_copy_assignment_header const_copy_assignment_use) = true.
Proof. vm_compute. reflexivity. Qed.

(* T's [Oimplicit_copy_ctor] placeholder is [ObjValue_le] clang's eager declaration *)
Example const_copy_assignment_header_sub_module_const_header :
  bool_decide (sub_module const_copy_assignment_header const_header) = true.
Proof. vm_compute. reflexivity. Qed.

(* Each header has a placeholder for one of T's copy members where the other has
   clang's eager declaration; both are [Unknown] *)
Eval vm_compute in sub_module_mismatch.compute const_copy_assignment_header const_copy_ctor_header.
Eval vm_compute in sub_module_mismatch.compute const_copy_ctor_header const_copy_assignment_header.

Example both_sub_module_const_copy_assignment_header_and_const_copy_ctor_header :
  bool_decide (sub_module const_copy_assignment_header const_copy_ctor_header) = true /\
  bool_decide (sub_module const_copy_ctor_header const_copy_assignment_header) = true.
Proof. vm_compute. split; reflexivity. Qed.

(* T's eagerly declared copy ctor is unused, so [Unknown] like the placeholder *)
Eval vm_compute in sub_module_mismatch.compute const_header const_copy_assignment_header.

Example const_header_sub_module_const_copy_assignment_header :
  bool_decide (sub_module const_header const_copy_assignment_header) = true.
Proof. vm_compute. reflexivity. Qed.

Example const_copy_assignment_use_sub_module_const_use :
  bool_decide (sub_module const_copy_assignment_use const_use) = true.
Proof. vm_compute. reflexivity. Qed.

(** * The non-[const] forms, from a base class

    The forms depend on direct base classes as well as on members
    (https://eel.is/c++draft/class.copy.ctor#7,
    https://eel.is/c++draft/class.copy.assign#2).  As above, [C]'s are
    declared eagerly and [D]'s are left to placeholders. *)

#[duplicates(error)]
cpp.prog base_header prog cpp:{{
  struct B {
    B() = default;
    B(B&) = default;
    B& operator=(B&) = default;
  };
  struct C : B { };
  struct D : C { };
}}.

#[duplicates(error)]
cpp.prog base_use prog cpp:{{
  struct B {
    B() = default;
    B(B&) = default;
    B& operator=(B&) = default;
  };
  struct C : B { };
  struct D : C { };
  void test() {
    D a;
    D b(a);                       // copy constructor D(D&)
    a = b;                        // copy assignment D& operator=(D&)
  }
}}.

Eval vm_compute in get base_header "C::C(C&)".
Eval vm_compute in get base_header "C::operator=(C&)".
Eval vm_compute in get base_header "D::D(D&)".
Eval vm_compute in get base_header "D::operator=(D&)".

Example base_header_sub_module_base_use :
  bool_decide (sub_module base_header base_use) = true.
Proof. vm_compute. reflexivity. Qed.

(** * No move placeholders when the move members are not declared

    A user-declared destructor (likewise a user-declared copy member) means no
    move constructor or move assignment is declared implicitly
    (https://eel.is/c++draft/class.copy.ctor#8,
    https://eel.is/c++draft/class.copy.assign#4); moving such a class copies.
    So the header must have no move placeholders, while the copy members still
    get theirs. *)

#[duplicates(error)]
cpp.prog nomove_header prog cpp:{{
  struct U { int x; ~U() = default; };
}}.

#[duplicates(error)]
cpp.prog nomove_use prog cpp:{{
  struct U { int x; ~U() = default; };
  void test() {
    U a;
    U b(static_cast<U&&>(a));     // copy constructor: there is no move constructor
    a = static_cast<U&&>(b);      // copy assignment: there is no move assignment
  }
}}.

Eval vm_compute in get nomove_header "U::U(U&&)".
Eval vm_compute in get nomove_header "U::operator=(U&&)".
Eval vm_compute in get nomove_header "U::U(const U&)".
Eval vm_compute in get nomove_header "U::operator=(const U&)".

Example nomove_header_sub_module_nomove_use :
  bool_decide (sub_module nomove_header nomove_use) = true.
Proof. vm_compute. reflexivity. Qed.

(** * Class template specializations

    Placeholders are emitted for implicit instantiations too, under their
    [Ninst] names.  The [static_assert] instantiates [W<int>] without using any
    of its members. *)

#[duplicates(error)]
cpp.prog template_header prog cpp:{{
  template <class X> struct W { X x; };
  static_assert(sizeof(W<int>) == sizeof(int), "");
}}.

#[duplicates(error)]
cpp.prog template_use prog cpp:{{
  template <class X> struct W { X x; };
  static_assert(sizeof(W<int>) == sizeof(int), "");
  void test() {
    W<int> a;
    W<int> b(a);
    W<int> c(static_cast<W<int>&&>(a));
    a = b;
    a = static_cast<W<int>&&>(c);
  }
}}.

Eval vm_compute in get template_header "W<int>::W()".
Eval vm_compute in get template_header "W<int>::W(const W<int>&)".
Eval vm_compute in get template_header "W<int>::W(W<int>&&)".
Eval vm_compute in get template_header "W<int>::operator=(const W<int>&)".
Eval vm_compute in get template_header "W<int>::operator=(W<int>&&)".
Eval vm_compute in get template_header "W<int>::~W()".

Example template_header_sub_module_template_use :
  bool_decide (sub_module template_header template_use) = true.
Proof. vm_compute. reflexivity. Qed.

(** * No placeholders for deleted members

    Some members' implicit special members are defined as deleted: a reference
    member deletes the default constructor (unless it has a default member
    initializer) and both assignments, an rvalue reference member also deletes
    the copy constructor, and a [const] member of non-class type deletes both
    assignments (https://eel.is/c++draft/class.default.ctor#2,
    https://eel.is/c++draft/class.copy.ctor#10,
    https://eel.is/c++draft/class.copy.assign#7).  clang records all but the
    default constructor's case on the class without declaring anything, and an
    elaborated translation unit, where clang declares every implicit member,
    has no declarations for deleted members.  So the header must have no
    placeholders for them. *)

#[duplicates(error)]
cpp.prog deleted_header prog cpp:{{
  int g;
  struct R { int& r; };
  struct RR { int&& r; };
  struct C { const int c = 0; };
  struct I { int& r = g; };     // the default constructor is not deleted
}}.

#[duplicates(error), elaborate]
cpp.prog deleted_elaborated prog cpp:{{
  int g;
  struct R { int& r; };
  struct RR { int&& r; };
  struct C { const int c = 0; };
  struct I { int& r = g; };
}}.

Eval vm_compute in get deleted_header "R::R()".
Eval vm_compute in get deleted_header "R::R(const R&)".
Eval vm_compute in get deleted_header "R::operator=(const R&)".
Eval vm_compute in get deleted_header "R::operator=(R&&)".
Eval vm_compute in get deleted_header "RR::RR(const RR&)".
Eval vm_compute in get deleted_header "RR::RR(RR&&)".
Eval vm_compute in get deleted_header "C::operator=(const C&)".
Eval vm_compute in get deleted_header "C::operator=(C&&)".
Eval vm_compute in get deleted_header "I::I()".

Example deleted_header_sub_module_deleted_elaborated :
  bool_decide (sub_module deleted_header deleted_elaborated) = true.
Proof. vm_compute. reflexivity. Qed.

(** * Agreement with elaboration

    A regression test for the deletion checks above, which rely on clang
    keeping its per-class "defaulted member is deleted" bits exact for every
    member it has not declared yet
    (<<CXXRecordDecl::hasSimpleCopyAssignment>> and friends).  The classes
    below cover each rule of https://eel.is/c++draft/class.copy.assign#7,
    https://eel.is/c++draft/class.copy.ctor#10,
    https://eel.is/c++draft/class.dtor#7 and
    https://eel.is/c++draft/class.default.ctor#2, plus cases that must not be
    deleted.  The header must have a placeholder exactly for each implicit
    member that elaboration declares and does not delete, so a rule that clang
    stops recording (e.g. after an LLVM upgrade) shows up here.

    Known gap: clang decides whether a default constructor is deleted only
    when declaring it, so the header still has placeholders for the deleted
    default constructors that are not due to reference members (marked [gap]
    below). *)

#[duplicates(error)]
cpp.prog agree_header prog cpp:{{
  int g;

  // Copy and move assignment
  struct A1 { int& r = g; };                     // reference member
  struct A2 { const int c = 0; };                // const non-class member
  struct A3 { const int a[2] = {1, 2}; };        // ... or array thereof
  struct P0 { int x; };
  struct A4 { const P0 p = {}; };                // const class member: eager
  struct A5 { A1 m; };                           // member with deleted assignment
  struct B6 {
    B6() = default;
    B6(const B6&) = default;
  private:
    B6& operator=(const B6&);
  };
  struct A6 : B6 { };                            // inaccessible base assignment
  struct A7 { A7() = default; A7(A7&&) = default; };  // user-declared move
  struct NT { NT& operator=(const NT&) { return *this; } };
  union A8 { NT n; int i; };                     // non-trivial variant member
  struct A9 { union { NT n; int i; }; };         // ... in an anonymous union
  template <class T> struct W { T t; };
  static_assert(sizeof(W<int&>) > 0, "");        // implicit instantiation
  struct Q { const Q& operator=(const Q&) const { return *this; } };
  struct A13 { const Q q{}; };                   // const member, not deleted
  struct A15 : A1 { };                           // base with deleted assignment
  struct A16 { mutable P0 p; };                  // mutable member, not deleted
  inline auto mk(int x) { return [x] { return x; }; }
  using L1 = decltype(mk(0));                    // capturing lambda
  inline auto mk0() { return [] { return 0; }; }
  using L0 = decltype(mk0());                    // non-capturing lambda

  // Copy and move constructors, destructor
  struct RR { int&& r; };                        // rvalue reference member
  struct NC { NC() = default; NC(const NC&) = delete; };
  struct C2 { NC n; };                           // member with deleted copy
  struct M1 { M1() = default; M1(const M1&) = default; M1(M1&&) = delete; };
  struct MV { M1 m; };                           // member with deleted move
  struct DD { ~DD() = delete; };
  struct X1 { DD d; };                           // member with deleted destructor;
                                                 // gap: its default ctor too
  struct ND { ~ND() {} };
  union X2 { ND n; int i; };                     // non-trivial variant destructor

  // Default constructor
  struct D1 { int& r; };                         // reference member
  struct D4 { D1 m; };                           // ... in a member
  struct R2 { int& r; R2() : r(g) {} };
  struct D9 { R2 m; };                           // ... bound by R2(): not deleted
  struct F0 { F0() {} };
  struct D3b { const F0 f; };                    // const-default-constructible
  struct D2 { const int c; };                    // gap: const non-class member
  struct D3 { const P0 p; };                     // gap: not const-default-constructible
  struct G0 { G0(int); };
  struct D5 { G0 g; };                           // gap: member without default ctor
  struct D6 : G0 { };                            // gap: base without default ctor
  union D7 { const int a; const int b; };        // gap: all variant members const
  struct H0 { H0() {} };
  union D8 { H0 h; int i; };                     // gap: non-trivial variant member
  struct PD { private: ~PD(); };
  struct D10 { PD p; };                          // gap: inaccessible member dtor
}}.

#[duplicates(error), elaborate]
cpp.prog agree_elaborated prog cpp:{{
  int g;

  // Copy and move assignment
  struct A1 { int& r = g; };                     // reference member
  struct A2 { const int c = 0; };                // const non-class member
  struct A3 { const int a[2] = {1, 2}; };        // ... or array thereof
  struct P0 { int x; };
  struct A4 { const P0 p = {}; };                // const class member: eager
  struct A5 { A1 m; };                           // member with deleted assignment
  struct B6 {
    B6() = default;
    B6(const B6&) = default;
  private:
    B6& operator=(const B6&);
  };
  struct A6 : B6 { };                            // inaccessible base assignment
  struct A7 { A7() = default; A7(A7&&) = default; };  // user-declared move
  struct NT { NT& operator=(const NT&) { return *this; } };
  union A8 { NT n; int i; };                     // non-trivial variant member
  struct A9 { union { NT n; int i; }; };         // ... in an anonymous union
  template <class T> struct W { T t; };
  static_assert(sizeof(W<int&>) > 0, "");        // implicit instantiation
  struct Q { const Q& operator=(const Q&) const { return *this; } };
  struct A13 { const Q q{}; };                   // const member, not deleted
  struct A15 : A1 { };                           // base with deleted assignment
  struct A16 { mutable P0 p; };                  // mutable member, not deleted
  inline auto mk(int x) { return [x] { return x; }; }
  using L1 = decltype(mk(0));                    // capturing lambda
  inline auto mk0() { return [] { return 0; }; }
  using L0 = decltype(mk0());                    // non-capturing lambda

  // Copy and move constructors, destructor
  struct RR { int&& r; };                        // rvalue reference member
  struct NC { NC() = default; NC(const NC&) = delete; };
  struct C2 { NC n; };                           // member with deleted copy
  struct M1 { M1() = default; M1(const M1&) = default; M1(M1&&) = delete; };
  struct MV { M1 m; };                           // member with deleted move
  struct DD { ~DD() = delete; };
  struct X1 { DD d; };                           // member with deleted destructor;
                                                 // gap: its default ctor too
  struct ND { ~ND() {} };
  union X2 { ND n; int i; };                     // non-trivial variant destructor

  // Default constructor
  struct D1 { int& r; };                         // reference member
  struct D4 { D1 m; };                           // ... in a member
  struct R2 { int& r; R2() : r(g) {} };
  struct D9 { R2 m; };                           // ... bound by R2(): not deleted
  struct F0 { F0() {} };
  struct D3b { const F0 f; };                    // const-default-constructible
  struct D2 { const int c; };                    // gap: const non-class member
  struct D3 { const P0 p; };                     // gap: not const-default-constructible
  struct G0 { G0(int); };
  struct D5 { G0 g; };                           // gap: member without default ctor
  struct D6 : G0 { };                            // gap: base without default ctor
  union D7 { const int a; const int b; };        // gap: all variant members const
  struct H0 { H0() {} };
  union D8 { H0 h; int i; };                     // gap: non-trivial variant member
  struct PD { private: ~PD(); };
  struct D10 { PD p; };                          // gap: inaccessible member dtor
}}.

Definition only_in (tu tu' : translation_unit) : list name :=
  List.filter (fun n => match tu'.(symbols) !! n with Some _ => false | None => true end)
    (map fst (NM.elements tu.(symbols))).

(* No placeholder is missing *)
Example agree_elaborated_only :
  only_in agree_elaborated agree_header = [].
Proof. vm_compute. reflexivity. Qed.

(* The only extra placeholders are the known gaps *)
Example agree_header_only :
  only_in agree_header agree_elaborated =
  ["D10::D10()"; "D2::D2()"; "D3::D3()"; "D5::D5()"; "D6::D6()"; "D7::D7()";
   "D8::D8()"; "X1::X1()"]%cpp_name.
Proof. vm_compute. reflexivity. Qed.
