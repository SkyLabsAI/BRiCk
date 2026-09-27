(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.semantics.
Require Import skylabs.lang.cpp.logic.pred.
Require Import skylabs.lang.cpp.logic.heap_pred.
Require Import skylabs.lang.cpp.logic.layout.
Require Import skylabs.iris.extra.proofmode.proofmode.


Set Default Proof Using "Type*".

Section with_cpp.
  Context `{Σ : cpp_logic} {σ : genv}.

  (* The direct proof from tblockR does not use either general decomposition. *)
  Example empty_array_layout t q sz :
    size_of σ t = Some sz ->
    tblockR (Tarray t 0) q -|- validR ** aligned_ofR t.
  Proof. apply tblockR_array_zero. Qed.

  Example empty_array_byte_decomposition t q sz :
    size_of σ t = Some sz ->
    tblockR (Tarray t 0) q -|- aligned_ofR t ** validR.
  Proof.
    move=> Hsz. rewrite (tblockR_array_better t 0 q sz) //=.
    by rewrite _offsetR_sub_0 ?right_id.
  Qed.

  Example empty_array_typed_decomposition t q sz :
    size_of σ t = Some sz ->
    tblockR (Tarray t 0) q -|- aligned_ofR t ** validR.
  Proof.
    move=> Hsz. rewrite tblockR_array; last by eexists.
    rewrite /= _offsetR_sub_0 ?right_id //; by eexists.
  Qed.

  (* A zero length must not make an unsized element type admissible. *)
  Example empty_array_unsized q :
    tblockR (Tarray "void" 0) q -|- False.
  Proof. by rewrite /tblockR. Qed.

  (* A non-affine frame and all three chunks survive in both directions. *)
  Example three_ushort_cells (q : cQp.t) (P : Rep) :
    tblockR (Tarray "unsigned short" 3) q ** P -|-
    (aligned_ofR "unsigned short" ** .[ Tbyte ! 6 ] |-> validR **
      tblockR "unsigned short" q **
      .[ Tbyte ! 2 ] |-> tblockR "unsigned short" q **
      .[ Tbyte ! 4 ] |-> tblockR "unsigned short" q) ** P.
  Proof.
    rewrite (tblockR_array_better "unsigned short" 3 q 2) //=.
    rewrite _offsetR_sub_0 ?right_id //.
  Qed.

  (* Splitting an empty block into three zero-sized chunks must
     preserve validity without inventing byte ownership. *)
  Example zero_sized_chunks (q : cQp.t) (P : Rep) :
    validR ** P -|-
    (validR ** blockR 0 q ** blockR 0 q ** blockR 0 q) ** P.
  Proof.
    have H := blockR_chunks 3 0 q.
    specialize (H _ _ Σ σ).
    rewrite /= !_offsetR_sub_0 ?right_id // in H.
    rewrite -H blockR_eq /blockR_def /= _offsetR_sub_0 ?right_id //.
  Qed.

  Example zero_sized_element_pair (q : cQp.t) :
    tblockR (Tarray (Tarray "unsigned short" 0) 2) q -|-
    validR ** aligned_ofR "unsigned short".
  Proof.
    rewrite (tblockR_array_better (Tarray "unsigned short" 0) 2 q 0) //=.
    rewrite !_offsetR_sub_0 ?right_id //.
    rewrite (tblockR_array_zero "unsigned short" q 2) //.
    have HA : aligned_ofR (Tarray "unsigned short" 0) -|- aligned_ofR "unsigned short".
    { by rewrite aligned_ofR.unlock align_of_array. }
    rewrite HA.
    iSplit.
    - iIntros "(_ & _ & $ & _)".
    - iIntros "#[V A]". iFrame "#".
  Qed.
End with_cpp.

Set Printing Width 4611686018427387903.
Set Printing Fully Qualified.
