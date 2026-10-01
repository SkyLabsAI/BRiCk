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
    (exception specification [NoThrow]) or a placeholder ([Unknown]), and
    comparing headers compares the two.  [N]'s own copy members are [NoThrow] in
    all of them.

    The [= false] examples hold only because a placeholder's exception
    specification over-approximates as [Unknown]: [NoThrow] is not [⊆ Unknown].
    They would flip if placeholders carried a precise specification. *)

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

(* T's eagerly declared copy assignment is [NoThrow]; the placeholder is [Unknown] *)
Eval vm_compute in sub_module_mismatch const_header const_copy_ctor_header.

Example const_header_not_sub_module_const_copy_ctor_header :
  bool_decide (sub_module const_header const_copy_ctor_header) = false.
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
   clang's eager declaration *)
Eval vm_compute in sub_module_mismatch const_copy_assignment_header const_copy_ctor_header.
Eval vm_compute in sub_module_mismatch const_copy_ctor_header const_copy_assignment_header.

Example neither_sub_module_const_copy_assignment_header_and_const_copy_ctor_header :
  bool_decide (sub_module const_copy_assignment_header const_copy_ctor_header) = false /\
  bool_decide (sub_module const_copy_ctor_header const_copy_assignment_header) = false.
Proof. vm_compute. split; reflexivity. Qed.

(* T's eagerly declared copy ctor is [NoThrow]; the placeholder is [Unknown] *)
Eval vm_compute in sub_module_mismatch const_header const_copy_assignment_header.

Example const_header_not_sub_module_const_copy_assignment_header :
  bool_decide (sub_module const_header const_copy_assignment_header) = false.
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
