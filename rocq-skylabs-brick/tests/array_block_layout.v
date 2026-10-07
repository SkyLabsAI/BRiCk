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
Require Import skylabs.lang.cpp.logic.object_repr.
Require Import skylabs.iris.extra.proofmode.proofmode.


Set Default Proof Using "Type*".

(* Storage alone cannot justify nonzero typed offsets for zero-sized elements. *)
Fail Check tblockR_array.

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
    move=> Hsz. by rewrite (tblockR_array_zero t q sz Hsz) comm.
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

  Example zero_stride_null_storage (q : cQp.t) :
    emp |-- nullptr |-> tblockR (Tarray (Tarray Tbyte 0) 1) q.
  Proof.
    rewrite /tblockR /= !align_of_array align_of_uchar.
    rewrite blockR_eq /blockR_def /= _offsetR_sub_0 // right_id.
    rewrite _at_sep _at_validR _at_alignedR.
    iIntros "_". iSplit; [iApply valid_ptr_nullptr | iPureIntro; apply aligned_ptr_min].
  Qed.
  Example three_typed_ushort_cells (p : ptr) (q : cQp.t) (P : mpred) :
    type_ptr (Tarray "unsigned short" 3) p |--
    ((p |-> tblockR (Tarray "unsigned short" 3) q ** P) ∗-∗
     (p |-> aligned_ofR "unsigned short" **
      p .["unsigned short" ! 3] |-> validR **
      p |-> tblockR "unsigned short" q **
      p .["unsigned short" ! 1] |-> tblockR "unsigned short" q **
      p .["unsigned short" ! 2] |-> tblockR "unsigned short" q) ** P).
  Proof.
    iIntros "#T".
    iDestruct (tblockR_array_typed p "unsigned short" 3 2 q eq_refl with "T") as "#C".
    iEval (rewrite /= !_offsetR_sub_0 ?right_id //) in "C".
    iEval (rewrite !_at_sep !_at_offsetR) in "C".
    iSplit; iIntros "[B $]"; by iApply "C".
  Qed.

  Example zero_stride_typed_pair (p : ptr) (q : cQp.t) :
    type_ptr (Tarray (Tarray Tbyte 0) 2) p |--
    (p |-> tblockR (Tarray (Tarray Tbyte 0) 2) q ∗-∗
     p |-> (aligned_ofR (Tarray Tbyte 0) **
       .[Tarray Tbyte 0 ! 2] |-> validR **
       tblockR (Tarray Tbyte 0) q **
       .[Tarray Tbyte 0 ! 1] |-> tblockR (Tarray Tbyte 0) q)).
  Proof.
    iIntros "#T".
    iDestruct (tblockR_array_typed p (Tarray Tbyte 0) 2 0 q eq_refl with "T") as "C".
    by iEval (rewrite /= !_offsetR_sub_0 ?right_id //) in "C".
  Qed.

  Example zero_stride_null_not_array_object :
    type_ptr (Tarray (Tarray Tbyte 0) 1) nullptr |-- (False : mpred).
  Proof.
    iIntros "T".
    iDestruct (type_ptr_array_end nullptr (Tarray Tbyte 0) 1 ltac:(eexists; reflexivity) with "T") as "V".
    by iApply (_valid_ptr_nullptr_sub_false Relaxed (Tarray Tbyte 0) 1 ltac:(lia) with "V").
  Qed.



End with_cpp.

Set Printing Width 4611686018427387903.
Set Printing Fully Qualified.



Section alignment_source_validity.
  Context `{Σ : cpp_logic} {σ : genv}.

  Lemma byte_alignment_without_source_validity (p : ptr) (t : Rtype) (sz i : N)
      (Hsz : size_of σ t = Some sz) :
    p |-> aligned_ofR t ** p .[ Tbyte ! Z.of_N (i * sz) ] |-> validR
    |-- p .[ Tbyte ! Z.of_N (i * sz) ] |-> aligned_ofR t.
  Proof.
    iIntros "[A D]".
    iEval (rewrite -_at_offsetR -(aligned_ofR_byte_sub t sz i Hsz)
      !_at_sep _at_offsetR _at_validR).
    Fail solve [iFrame].
  Abort.

  Example byte_alignment_with_source_validity (p : ptr) (t : Rtype) (sz i : N)
      (Hsz : size_of σ t = Some sz) :
    p |-> aligned_ofR t ** valid_ptr p **
    p .[ Tbyte ! Z.of_N (i * sz) ] |-> validR
    |-- p .[ Tbyte ! Z.of_N (i * sz) ] |-> aligned_ofR t.
  Proof.
    iIntros "(A & V & D)".
    iEval (rewrite -_at_offsetR -(aligned_ofR_byte_sub t sz i Hsz)
      !_at_sep _at_offsetR _at_validR).
    by iFrame.
  Qed.
End alignment_source_validity.
