(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
(** Tests for the new/delete semantics in [skylabs.lang.cpp.logic.new_delete]. *)
Require Import skylabs.iris.extra.proofmode.proofmode.
Require Import skylabs.lang.cpp.parser.
Require Import skylabs.lang.cpp.parser.plugin.cpp2v.
Require Import skylabs.lang.cpp.logic.

cpp.prog source flags "-std=c++23 --target=x86_64-linux-gnu" prog cpp:{{
// The global allocation and deallocation functions are implicitly declared
// in every translation unit (https://eel.is/c++draft/basic.stc.dynamic.general#2);
// the uses below make cpp2v emit them. Declaring [std::align_val_t] ourselves
// would be undefined behavior (https://eel.is/c++draft/namespace.std#1).
struct alignas(64) A { int x; };
void test_global_new() { delete new int(0); }
void test_aligned_new() { delete new A{0}; }

// A class-specific allocation function.
struct D {
  int x;
  static void* operator new(unsigned long sz);
  static void operator delete(void* p);
};

// A class-specific sized deallocation function.
struct E {
  static void operator delete(void* p, unsigned long sz);
};

// A virtual destructor whose deleting destructor calls a member deallocation
// function.
struct S {
  virtual ~S() { }
  static void operator delete(void* p) { }
};

// A virtual destructor without a member deallocation function.
struct B {
  virtual ~B() { }
};

// A class whose (implicit, virtual) destructor selects a member deallocation
// function that its base [B] does not have.
struct V : B {
  static void operator delete(void* p) { }
};

void test_new() { delete new D{0}; }
void test_global_delete(S* p) { ::delete p; }
void test_delete(S* p) { delete p; }
void test_delete_base(B* p) { delete p; }
void test_new_v() { delete new V; }
}}.

(** ** Alignment required of the storage returned by an allocation function

    Only the global allocation functions without an alignment parameter must
    return storage aligned to <<__STDCPP_DEFAULT_NEW_ALIGNMENT__>>
    (<https://eel.is/c++draft/cpp.predefined#1.8>); other allocation functions
    need only align for the allocated type
    (<https://eel.is/c++draft/basic.stc.dynamic.allocation#3>). *)

Example global_new_alignment :
  new_storage_alignment source "operator new(unsigned long)" 4%N =
    STDCPP_DEFAULT_NEW_ALIGNMENT.
Proof. vm_compute. reflexivity. Qed.

Example class_new_alignment :
  new_storage_alignment source "D::operator new(unsigned long)" 4%N = 4%N.
Proof. vm_compute. reflexivity. Qed.

Example aligned_new_alignment :
  new_storage_alignment source "operator new(unsigned long, enum std::align_val_t)" 64%N = 64%N.
Proof. vm_compute. reflexivity. Qed.

(** ** Deallocation function of a delete-expression

    A <<::delete>> calls the function found by global lookup
    (<https://eel.is/c++draft/expr.delete#8>), while a plain <<delete>> of an
    object with a virtual destructor calls the function selected at the
    definition of the dynamic type's destructor
    (<https://eel.is/c++draft/expr.delete#8.1>,
    <https://eel.is/c++draft/class.dtor#15>). Both expressions record the same
    global function when the static type has no member deallocation function,
    so [Edelete] records whether <<::>> was written. *)

Example delete_for_global_delete :
  delete_operator.delete_for source true "operator delete(void*, unsigned long)" "S" =
    Some ("operator delete(void*, unsigned long)"%cpp_name, delete_operator.mk None true false).
Proof. vm_compute. reflexivity. Qed.

Example delete_for_member_delete :
  delete_operator.delete_for source false "S::operator delete(void*)" "S" =
    Some ("S::operator delete(void*)"%cpp_name, delete_operator.mk None false false).
Proof. vm_compute. reflexivity. Qed.

(** <<delete p>> with <<p : B*>> pointing to a <<V>>: the expression's lookup
    in <<B>> finds the global function, but <<V>>'s destructor selects
    <<V::operator delete>>. *)
Example delete_for_dynamic_member_delete :
  delete_operator.delete_for source false "operator delete(void*, unsigned long)" "V" =
    Some ("V::operator delete(void*)"%cpp_name, delete_operator.mk None false false).
Proof. vm_compute. reflexivity. Qed.

Example delete_for_virtual_without_member :
  is_Some (delete_operator.delete_for source false "operator delete(void*)" "B").
Proof. vm_compute. eexists. reflexivity. Qed.

(** ** Deleting <<nullptr>>

    The deallocation function may be called on <<nullptr>>
    (<https://eel.is/c++draft/expr.delete#6>), and the size argument a sized
    deallocation function would receive is not fixed, so the call must be safe
    for every size. *)
Section with_cpp.
  Context `{Σ : cpp_logic} {σ : genv} `{MOD : source ⊧ σ}.

  Lemma wp_delete_null_any_size Q (sz : N) :
    wp_delete_null false "E::operator delete(void*, unsigned long)" "E" Q ⊢
    wp_invoke_delete "E"
      ("E::operator delete(void*, unsigned long)"%cpp_name, delete_operator.mk None true false)
      sz nullptr Q.
  Proof using MOD.
    rewrite wp_delete_null.unlock.
    (* All arguments explicit: [vm_compute] must only run on the closed
       [delete_for source ...]. *)
    rewrite (delete_operator.delete_for_submodule (tu1 := source) (global := false)
      (op := "E::operator delete(void*, unsigned long)") (cls := "E")
      (result := ("E::operator delete(void*, unsigned long)"%cpp_name,
                  delete_operator.mk None true false))
      ltac:(vm_compute; reflexivity) (genv_compat_submodule _ _ MOD)).
    iIntros "[H _]". iApply "H".
  Qed.
End with_cpp.
