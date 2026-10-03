(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.iris.extra.proofmode.proofmode.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.semantics.
Require Import skylabs.lang.cpp.logic.heap_pred.
Require Import skylabs.lang.cpp.logic.object_repr.

Set Default Proof Using "Type*".

Fail Check _at_anyR_ptr_congP_transport.

Section with_cpp.
  Context `{Σ : cpp_logic} {σ : genv}.

  (* The frame need not be affine, and the byte need not have a raw encoding. *)
  Example transport_uninitialized_byte (p p' : ptr) (q : cQp.t) (P : mpred) :
    ptr_congP σ p p' ** p |-> tptstoR Tbyte q Vundef ** P
    |-- p' |-> anyR Tbyte q ** P.
  Proof.
    rewrite (tptstoR_anyR_val Tbyte q Vundef).
    iIntros "(#C & B & F)". iFrame "F".
    by iApply (_at_anyR_byte_ptr_congP_transport with "C B").
  Qed.

  Example transport_raw_byte (p p' : ptr) (q : cQp.t) (r : raw_byte) (P : mpred) :
    ptr_congP σ p p' ** p |-> tptstoR Tbyte q (Vraw r) ** P
    |-- p' |-> anyR Tbyte q ** P.
  Proof.
    rewrite (tptstoR_anyR_val Tbyte q (Vraw r)).
    iIntros "(#C & B & F)". iFrame "F".
    by iApply (_at_anyR_byte_ptr_congP_transport with "C B").
  Qed.

  Example transport_three_byte_block (p p' : ptr) (q : cQp.t) (P : mpred) :
    ptr_congP σ p p' ** type_ptr (Tarray Tbyte 3) p **
    type_ptr (Tarray Tbyte 3) p' ** p |-> blockR 3 q ** P
    |-- p' |-> blockR 3 q ** P.
  Proof.
    iIntros "(#C & #T & #T' & B & F)". iFrame "F".
    iApply (blockR_ptr_congP_transport 3 p p' (Tarray Tbyte 3) q eq_refl with "[$] B").
  Qed.

  Example transport_empty_byte_block (p p' : ptr) (q : cQp.t) (P : mpred) :
    ptr_congP σ p p' ** type_ptr (Tarray Tbyte 0) p **
    type_ptr (Tarray Tbyte 0) p' ** p |-> blockR 0 q ** P
    |-- p' |-> blockR 0 q ** P.
  Proof.
    iIntros "(#C & #T & #T' & B & F)". iFrame "F".
    iApply (blockR_ptr_congP_transport 0 p p' (Tarray Tbyte 0) q eq_refl with "[$] B").
  Qed.

End with_cpp.

Set Printing Width 4611686018427387903.
Set Printing Fully Qualified.
Print Assumptions _at_anyR_byte_ptr_congP_transport.
Print Assumptions blockR_ptr_congP_transport_raw.
Print Assumptions blockR_ptr_congP_transport.
Print Assumptions transport_uninitialized_byte.
Print Assumptions transport_raw_byte.
Print Assumptions transport_three_byte_block.
Print Assumptions transport_empty_byte_block.
