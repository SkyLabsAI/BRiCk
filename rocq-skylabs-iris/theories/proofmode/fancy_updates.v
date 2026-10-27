(*
 * Copyright (C) 2021 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import stdpp.namespaces.
Require Import iris.bi.derived_laws.
Require Import skylabs.iris.extra.proofmode.proofmode.
Require Import iris.proofmode.classes.

Implicit Types (E : coPset).

(*** Failing Tests *)
Section failing_tests.
  Context {SI : sidx} {PROP : bi} `{!BiFUpd PROP}.
  Implicit Types (P Q : PROP).

  Lemma frame_empty_test E1 E1' E3 P :
    (|={E1,∅}=> P)%I -∗
    (|={E1',E3}=> P)%I.
  Proof.
    iIntros "H". Fail iMod "H".
  Abort.

  Lemma frame_emptier_test E1 E2 P (Hmask : E2 ⊆ E1) :
    (|={∅}=> P)%I -∗
    (|={E1,E2}=> P)%I.
  Proof.
    iIntros "H". Fail iMod "H".
  Abort.

  Lemma frame_test E1 E1' E2 E3 P :
    (|={E1,E2}=> P)%I -∗
    (|={E1',E3}=> P)%I.
  Proof.
    iIntros "H". Fail iMod "H".
  Abort.

  Lemma frame_submask E1 E1' P Q (Hmask : E1 ⊆ E1') :
    (|={E1}=> Q) ={E1'}=∗ Q.
  Proof.
    iIntros "H". Fail iMod "H".
  Abort.

  Lemma frame_submasks E1 E1' E2 P Q (Hmask : E1 ⊆ E1') (Hmask' : E1' ⊆ E2):
    (|={E1, E2}=> Q) ={E1', E2}=∗ Q.
  Proof.
    iIntros "H". Fail iMod "H".
  Abort.
End failing_tests.

(*** ElimModal Instances *)
(** Iris proofmode instances for [iMod]. Tests below the instances
document the enabled [iMod] patterns.
Beware: iMod does NOT backtrack when it fails solving a side condition.
However, all these instances appear syntactically non-overlapping.
*)
Section elim_modal_instances.
  Context {SI : sidx} {PROP : bi} `{!BiFUpd PROP}.
  Implicit Types P Q R : PROP.
  Import bi.

  #[global] Instance elim_modal_fupd_fupd_submask p E1 E1' P Q :
    ElimModal (E1 ⊆ E1') p false (|={E1}=> P)%I P
              (|={E1'}=> Q)%I (|={E1'}=> Q)%I | 20.
  Proof.
    intros ?. rewrite intuitionistically_if_elim /= fupd_frame_r wand_elim_r.
    rewrite (fupd_mask_frame_r E1 _ (E1' ∖ E1)); last by solve_ndisj.
    by rewrite -union_difference_L // fupd_trans.
  Qed.

  #[global] Instance elim_modal_fupd_fupd_mask_frame_empty
        p E1 E1' E3 P Q :
    ElimModal (E1 ⊆ E1') p false (|={E1,∅}=> P)%I P
              (|={E1',E3}=> Q)%I (|={E1'∖E1,E3}=> Q)%I | 30.
  Proof.
    intros ?. rewrite intuitionistically_if_elim /= fupd_frame_r wand_elim_r.
    rewrite (fupd_mask_frame_r E1 _ (E1' ∖ E1)); last by solve_ndisj.
    by rewrite left_id_L -union_difference_L // fupd_trans.
  Qed.

  #[global] Instance elim_modal_fupd_fupd_mask_frame_empty_empty
        p E1 E2 P Q :
    ElimModal True p false (|={∅}=> P)%I P
              (|={E1,E2}=> Q)%I (|={E1,E2}=> Q)%I | 20.
  Proof.
    intros ?. rewrite intuitionistically_if_elim /= fupd_frame_r wand_elim_r.
    iIntros ">?". by rewrite difference_empty_L.
  Qed.

  #[global] Instance elim_modal_fupd_fupd_frame
        p E1 E1' E2 E3 P Q :
    ElimModal (E1 ⊆ E1') p false (|={E1,E2}=> P) P
              (|={E1',E3}=> Q) (|={E2 ∪ E1'∖E1,E3}=> Q) | 40.
  Proof.
    intros ?. rewrite intuitionistically_if_elim /= fupd_frame_r wand_elim_r.
    rewrite (fupd_mask_frame_r E1 _ (E1' ∖ E1)); last by solve_ndisj.
    by rewrite -union_difference_L // fupd_trans.
  Qed.

  #[global] Instance elim_modal_fupd_fupd_submasks
        p E1 E1' E2 (P Q : PROP) :
    ElimModal (E1 ⊆ E1' ⊆ E2) p false (|={E1, E2}=> P)%I P
              (|={E1', E2}=> Q)%I (|={E2}=> Q)%I | 10.
  Proof.
    intros [??]. rewrite intuitionistically_if_elim /= fupd_frame_r wand_elim_r.
    iIntros ">?". enough (E2 ∪ E1' ∖ E1 = E2) as -> by done. set_solver.
  Qed.
End elim_modal_instances.

(*** Tests *)
Section tests.
  Context {SI : sidx} {PROP : bi} `{!BiFUpd PROP}.
  Implicit Types (P Q : PROP).

  Lemma frame_empty_test E1 E1' E3 P :
    (|={E1,∅}=> P)%I -∗
    (|={E1',E3}=> P)%I.
  Proof.
    iIntros "H". iMod "H".
  Abort.

  Lemma frame_emptier_test E1 E2 P (Hmask : E2 ⊆ E1) :
    (|={∅}=> P)%I -∗
    (|={E1,E2}=> P)%I.
  Proof.
    iIntros "H". iMod "H". iFrame.
    iApply (fupd_mask_intro E1 E2); [done|].
  Abort.

  Lemma frame_test E1 E1' E2 E3 P :
    (|={E1,E2}=> P)%I -∗
    (|={E1',E3}=> P)%I.
  Proof.
    iIntros "H". iMod "H".
  Abort.

  Lemma frame_submask E1 E1' P Q (Hmask : E1 ⊆ E1') :
    (|={E1}=> Q) ={E1'}=∗ Q.
  Proof.
    iIntros "H". iMod "H".
    by iFrame.
    all: fail.
  Abort.

  Lemma frame_submasks E1 E1' E2 P Q (Hmask : E1 ⊆ E1') (Hmask' : E1' ⊆ E2):
    (|={E1, E2}=> Q) ={E1', E2}=∗ Q.
  Proof.
    iIntros "H". iMod "H".
    by iFrame.
    all: fail.
  Abort.
End tests.
