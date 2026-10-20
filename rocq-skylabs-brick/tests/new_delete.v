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

void test_new() { delete new D{0}; }
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

