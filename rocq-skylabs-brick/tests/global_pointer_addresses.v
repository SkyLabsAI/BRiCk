(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import Stdlib.micromega.Lia.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.semantics.values.

Open Scope pstring_scope.
Set Default Proof Using "Type*".

(* A zero-sized class wrapping a zero-length array, as in the compiler
   extension used by the original counterexample. Its type is not itself an
   array, so a syntactic zero-length-array check would miss this case. *)
Definition empty_global_struct : Struct :=
  Build_Struct []
    [mkMember (Nid "bytes") "unsigned char[0]" false None {| li_offset := 0 |}]
    [] [] "Empty::~Empty()"%cpp_name true None POD 0 1.

Definition global_address_env (ty1 ty2 : type) : genv :=
  {| genv_tu := makeTranslationUnit
       {[ "first"%cpp_name := Ovar ty1 global_init.NoInit;
          "second"%cpp_name := Ovar ty2 global_init.NoInit ]}
       {[ "Empty"%cpp_name := Gstruct empty_global_struct ]}
       ∅ [] [] abi.abi_default ∅ ∅ ∅ ∅;
     member_pointer_bitsize := bitsize.W64 |}.

(* Name and allocation identity remain distinct even when addresses may alias. *)
Example global_pointer_identity tu : Inj (=) (=) (global_ptr tu).
Proof. apply _. Qed.
Example global_allocation_identity tu :
  Inj (=) (=) (fun n => ptr_alloc_id (global_ptr tu n)).
Proof. apply _. Qed.

(* There must be no unguarded address-injectivity instance, even for the current
   environment. The old counterexample acquired exactly this instance via inj. *)
Fail Definition unrestricted_global_addresses (σ : genv) :
  Inj (=) (=) (fun n => @ptr_vaddr σ (global_ptr σ.(genv_tu) n)) := _.

Lemma nonempty_globals_apart ty1 ty2 sz1 sz2 :
  size_of (global_address_env ty1 ty2) ty1 = Some sz1 -> (0 < sz1)%N ->
  size_of (global_address_env ty1 ty2) ty2 = Some sz2 -> (0 < sz2)%N ->
  same_property (@ptr_vaddr (global_address_env ty1 ty2))
    (global_ptr (global_address_env ty1 ty2).(genv_tu) "first")
    (global_ptr (global_address_env ty1 ty2).(genv_tu) "second") -> False.
Proof.
  intros Hsz1 Hpos1 Hsz2 Hpos2 Haddr.
  have Hnames := @global_ptr_addr_inj (global_address_env ty1 ty2)
    "first" "second" ty1 ty2 global_init.NoInit global_init.NoInit sz1 sz2
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    Hsz1 Hpos1 Hsz2 Hpos2 Haddr.
  discriminate Hnames.
Qed.

Example positive_size_globals_apart :
  same_property (@ptr_vaddr (global_address_env "unsigned char" "int"))
    (global_ptr (global_address_env "unsigned char" "int").(genv_tu) "first")
    (global_ptr (global_address_env "unsigned char" "int").(genv_tu) "second") -> False.
Proof.
  apply (nonempty_globals_apart "unsigned char" "int" 1 4); reflexivity.
Qed.

(* Neither zero-sized side can discharge positivity, including qualified
   classes wrapping zero-sized storage. Incomplete types fail defined size. *)
Fail Check (nonempty_globals_apart "unsigned char[0]" "int" 0 4
  eq_refl ltac:(lia) eq_refl ltac:(lia)).
Fail Check (nonempty_globals_apart "unsigned char" "Empty" 1 0
  eq_refl ltac:(lia) eq_refl ltac:(lia)).
Fail Check (nonempty_globals_apart "const Empty" "int" 0 4
  eq_refl ltac:(lia) eq_refl ltac:(lia)).
Fail Check (nonempty_globals_apart "Forward" "int" 1 4
  eq_refl ltac:(lia) eq_refl ltac:(lia)).

(* A declaration is required independently of knowing a positive type size. *)
Fail Check (@global_ptr_addr_inj (global_address_env "unsigned char" "int")
  "missing" "second" "unsigned char" "int"
  global_init.NoInit global_init.NoInit 1 4 ltac:(vm_compute; reflexivity)).

Set Printing Width 4611686018427387903.
Set Printing Fully Qualified.
Print Assumptions nonempty_globals_apart.
Print Assumptions positive_size_globals_apart.
Print Assumptions global_pointer_identity.
Print Assumptions global_allocation_identity.
