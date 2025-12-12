(*
 * Copyright (c) 2021 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *
 * This file is derived from code original to the Iris project. That
 * original code is
 *
 *	Copyright Iris developers and contributors
 *
 * and used according to the following license.
 *
 *	SPDX-License-Identifier: BSD-3-Clause
 *
 * Original Code:
 * https://gitlab.mpi-sws.org/iris/iris/-/blob/7ccdfe0df5832b69742306302144b5358c9ed843/iris/base_logic/lib/invariants.v
 * https://gitlab.mpi-sws.org/iris/iris/-/blob/7ccdfe0df5832b69742306302144b5358c9ed843/iris/base_logic/lib/cancelable_invariants.v
 *
 * Original Iris License:
 * https://gitlab.mpi-sws.org/iris/iris/-/blob/7ccdfe0df5832b69742306302144b5358c9ed843/LICENSE-CODE
 *)

(* The iProp instances for invariants. *)
Require Import bluerock.iris.extra.proofmode.proofmode.

Require Import bluerock.iris.extra.bi.na_invariants.
Require Import bluerock.iris.extra.bi.cancelable_invariants.
Require Import bluerock.iris.extra.bi.invariants.
Require Import bluerock.iris.extra.base_logic.iprop_own.

(*** Invariants for iProp **)
(* Copy from
  https://gitlab.mpi-sws.org/iris/iris/-/blob/7ccdfe0df5832b69742306302144b5358c9ed843/iris/base_logic/lib/invariants.v *)
Section inv.
  Context `{!invGS Σ}.
  Implicit Types (P : iProp Σ).

  #[local] Lemma own_inv_to_inv M P: own_inv M P -∗ inv M P.
  Proof.
    iIntros "#I". rewrite inv_eq. iIntros (E H).
    iPoseProof (own_inv_acc with "I") as "H"; eauto.
  Qed.

  Lemma inv_alloc N E P : ▷ P ⊢ |={E}=> inv N P.
  Proof.
    iIntros "HP". iApply own_inv_to_inv.
    iApply (own_inv_alloc N E with "HP").
  Qed.

  Lemma inv_alloc_open N E P :
    ↑N ⊆ E → ⊢ |={E, E∖↑N}=> inv N P ∗ (▷P ={E∖↑N, E}=∗ True).
  Proof.
    iIntros (?). iMod own_inv_alloc_open as "[HI $]"; first done.
    iApply own_inv_to_inv. done.
  Qed.
End inv.

(*** Non-atomic invariants for iProp *)
(* Copy from
  https://gitlab.mpi-sws.org/iris/iris/-/blob/90b6007faea2b61546aed01fe0ed9936b55468d1/iris/base_logic/lib/na_invariants.v *)
Section na_inv.
  Import iris.algebra.gset iris.algebra.coPset.
  Context `{!invGS Σ, !na_invG Σ}.
  #[local] Existing Instance na_inv_inG.
  #[local] Typeclasses Transparent na_own na_inv.

  Implicit Types (P : iProp Σ).

  Lemma na_inv_alloc p E N P : ▷ P ⊢ |={E}=> na_inv p N P.
  Proof.
    iIntros "HP".
    iMod (own_unit (A:=prodUR coPset_disjUR (gset_disjUR positive)) p) as "Hempty".
    iMod (own_updateP with "Hempty") as ([m1 m2]) "[Hm Hown]".
    { apply prod_updateP'.
      - apply cmra_updateP_id, (reflexivity (R:=eq)).
      - apply (gset_disj_alloc_empty_updateP_strong' (λ i, i ∈ (↑N:coPset))).
        intros Ef. exists (coPpick (↑ N ∖ gset_to_coPset Ef)).
        rewrite -elem_of_gset_to_coPset comm -elem_of_difference.
        apply coPpick_elem_of=> Hfin.
        eapply nclose_infinite, (difference_finite_inv _ _), Hfin.
        apply gset_to_coPset_finite. }
    simpl. iDestruct "Hm" as %(<- & i & -> & ?).
    rewrite /na_inv.
    iMod (inv_alloc N with "[-]"); last (iModIntro; iExists i; eauto).
    iNext. iLeft. by iFrame.
  Qed.
End na_inv.

(*** Cancelable invariants for iProp *)
(* Copy from
  https://gitlab.mpi-sws.org/iris/iris/-/blob/7ccdfe0df5832b69742306302144b5358c9ed843/iris/base_logic/lib/cancelable_invariants.v *)
Section cinv.
  Context `{!invGS Σ, !cinvG Σ}.
  #[local] Existing Instance cinv_inG.
  #[local] Typeclasses Transparent cinv_own cinv.

  Implicit Types (P : iProp Σ).

  (*** Allocation rules. *)
  (** The "strong" variants permit any infinite [I], and choosing [P] is delayed
  until after [γ] was chosen.*)
  Lemma cinv_alloc_strong (I : gname → Prop) E N :
    pred_infinite I →
    ⊢ |={E}=> ∃ γ, ⌜ I γ ⌝ ∗ cinv_own γ 1 ∗ ∀ P, ▷ P ={E}=∗ cinv N γ P.
  Proof.
    iIntros (?). iMod (own_alloc_strong 1%Qp I) as (γ) "[Hfresh Hγ]"; [done|done|].
    iExists γ. iIntros "!> {$Hγ $Hfresh}" (P) "HP".
    iMod (inv_alloc N _ (P ∨ cinv_own γ 1) with "[HP]"); eauto.
  Qed.

  (** The "open" variants create the invariant in the open state, and delay
  having to prove [P].
  These do not imply the other variants because of the extra assumption [↑N ⊆ E]. *)
  Lemma cinv_alloc_strong_open (I : gname → Prop) E N :
    pred_infinite I →
    ↑N ⊆ E →
    ⊢ |={E}=> ∃ γ, ⌜ I γ ⌝ ∗ cinv_own γ 1 ∗ ∀ P,
      |={E,E∖↑N}=> cinv N γ P ∗ (▷ P ={E∖↑N,E}=∗ emp).
  Proof.
    iIntros (??). iMod (own_alloc_strong 1%Qp I) as (γ) "[Hfresh Hγ]"; [done|done|].
    iExists γ. iIntros "!> {$Hγ $Hfresh}" (P).
    iMod (inv_alloc_open N _ (P ∨ cinv_own γ 1)) as "[Hinv Hclose]"; first by eauto.
    iIntros "!>". iFrame. iIntros "HP". iApply "Hclose". iLeft. done.
  Qed.

  Lemma cinv_alloc_cofinite (G : gset gname) E N :
    ⊢ |={E}=> ∃ γ, ⌜ γ ∉ G ⌝ ∗ cinv_own γ 1 ∗ ∀ P, ▷ P ={E}=∗ cinv N γ P.
  Proof.
    apply cinv_alloc_strong. apply (pred_infinite_set (C:=gset gname))=> E'.
    exists (fresh (G ∪ E')). apply not_elem_of_union, is_fresh.
  Qed.

  Lemma cinv_alloc E N P : ▷ P ⊢ |={E}=> ∃ γ, cinv N γ P ∗ cinv_own γ 1.
  Proof.
    iIntros "HP". iMod (cinv_alloc_cofinite ∅ E N) as (γ _) "[Hγ Halloc]".
    iExists γ. iFrame "Hγ". by iApply "Halloc".
  Qed.

  Lemma cinv_alloc_open E N P :
    ↑N ⊆ E → ⊢ |={E,E∖↑N}=> ∃ γ, cinv N γ P ∗ cinv_own γ 1 ∗ (▷ P ={E∖↑N,E}=∗ emp).
  Proof.
    iIntros (?). iMod (cinv_alloc_strong_open (λ _, True)) as (γ) "(_ & Htok & Hmake)"; [|done|].
    { apply pred_infinite_True. }
    iMod ("Hmake" $! P) as "[Hinv Hclose]". iIntros "!>". iExists γ. iFrame.
  Qed.

  Corollary cinv_alloc_ghost_named_inv E N (I : gname → iProp _) :
    (∀ γ , I γ) ⊢ |={E}=> ∃ γ, cinv N γ (I γ) ∗ cinv_own γ 1.
  Proof.
    iIntros "I".
    iMod (cinv_alloc_cofinite empty E N) as (γ ?) "[HO HI]".
    iSpecialize ("I" $! γ).
    iMod ("HI" $! (I γ) with "[$I]") as "HI".
    iIntros "!>". eauto with iFrame.
  Qed.
End cinv.
