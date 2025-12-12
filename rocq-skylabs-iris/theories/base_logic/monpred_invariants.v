(*
 * Copyright (c) 2021-2025 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *
 * Part of this file is derived from code original to the Iris project. That
 * original code is
 *
 *	Copyright Iris developers and contributors
 *
 * and used according to the following license.
 *
 *	SPDX-License-Identifier: BSD-3-Clause
 *
 * Original Code:
 * https://gitlab.mpi-sws.org/iris/iris/-/blob/90b6007faea2b61546aed01fe0ed9936b55468d1/iris/base_logic/lib/na_invariants.v
 *
 * Original Iris License:
 * https://gitlab.mpi-sws.org/iris/iris/-/blob/90b6007faea2b61546aed01fe0ed9936b55468d1/LICENSE-CODE
 *)


Require Import bluerock.iris.extra.bi.monpred.
Require Import bluerock.iris.extra.proofmode.proofmode.
Require Import iris.proofmode.monpred.

Require Import bluerock.iris.extra.bi.only_provable.
Require Import bluerock.iris.extra.bi.invariants.
Require Import bluerock.iris.extra.bi.na_invariants.
Require Import bluerock.iris.extra.bi.cancelable_invariants.
Require Import bluerock.iris.extra.bi.weakly_objective.
Require Import bluerock.iris.extra.base_logic.monpred_own.

(*** Invariants for monPred **)

(* Allocations are not general for arbitrary BI. This one here is developed for
  monPred, basing on iProp. *)
Section allocation.
  Context {I : biIndex} `{!invGS Σ}.
  Notation monPred := (monPred I (iPropI Σ)).
  Implicit Types (i j : I) (γ : gname) (P Q R : monPred).

  (** ** Internal model of invariants *)
  #[local] Definition own_inv (N : namespace) P : monPred :=
    ⌜ WeaklyObjective P ⌝ ∧
    ∃ i, monPred_in i ∧ (* >> this says the current local state is at least i *)
      ⎡ base_logic.lib.invariants.inv N (P i) ⎤.

  #[local] Lemma own_inv_acc E N P :
    ↑N ⊆ E → own_inv N P ⊢ |={E,E∖↑N}=> ▷ P ∗ (▷ P ={E∖↑N,E}=∗ emp).
  Proof.
    intros SUB. constructor => j.
    iDestruct 1 as (WK i Le) "INV".
    iInv N as "P" "Close".
    iIntros "!>". iFrame "P".
    iIntros (i' Lei) "P".
    iMod ("Close" with "[P]"); last done.
    rewrite weakly_objective. iFrame. by etrans.
  Qed.

  #[local] Lemma own_inv_alloc N E P {WK: WeaklyObjective P} :
    ▷ P ⊢ |={E}=> own_inv N P.
  Proof.
    iIntros "P". iDestruct (monPred_in_intro with "P") as (i) "[In P]".
    iFrame (WK). iExists i. iFrame "In".
    iMod (base_logic.lib.invariants.inv_alloc _ _ (P i) with "[P]") as "$"; last done.
    rewrite monPred_at_later. by iFrame.
  Qed.

  (* This does not imply [own_inv_alloc] due to the extra assumption [↑N ⊆ E]. *)
  #[local] Lemma own_inv_alloc_open N E P {WK: WeaklyObjective P} :
    ↑N ⊆ E → ⊢ |={E, E∖↑N}=> own_inv N P ∗ (▷P ={E∖↑N, E}=∗ emp).
  Proof.
    intros Sub.
    iDestruct (monPred_in_intro emp with "[//]") as (i) "[Ini _]".
    iMod (base_logic.lib.invariants.inv_alloc_open N E (P i)) as "[Inv Close]"; [done|].
    iIntros "!>". iFrame (WK). iSplit.
    - iExists i. by iFrame "#∗".
    - iIntros "P". iMod ("Close" with "[P]"); last done.
      iCombine "Ini" "P" as "Pi".
      iDestruct (monPred_in_intro with "Pi") as (j) "(_ & % & P)".
      by rewrite weakly_objective.
  Qed.

  #[local] Lemma own_inv_to_inv M P: own_inv M P ⊢ inv M P.
  Proof.
    iIntros "#I". rewrite inv_eq. iIntros (E H).
    iPoseProof (own_inv_acc with "I") as "H"; eauto.
  Qed.

  Lemma inv_alloc N E P `{!WeaklyObjective P} : ▷ P ⊢ |={E}=> inv N P.
  Proof.
    iIntros "HP". iApply own_inv_to_inv.
    iApply (own_inv_alloc N E with "HP").
  Qed.

  Lemma inv_alloc_open N E P `{!WeaklyObjective P} :
    ↑N ⊆ E → ⊢ |={E, E∖↑N}=> inv N P ∗ (▷P ={E∖↑N, E}=∗ emp).
  Proof.
    iIntros (?). iMod own_inv_alloc_open as "[HI $]"; first done.
    iApply own_inv_to_inv. done.
  Qed.
End allocation.
#[global] Hint Opaque own_inv : typeclass_instances br_opacity.

(* A proof that inv is objective if its content is objective. *)
Section minv.
  Context {I J : biIndex} `{!BiFUpd PROP}.
  Implicit Types (P : monPred I PROP).

  #[global] Instance inv_objective N P : Objective P -> Objective (inv N P).
  Proof.
    intros HP i1 i2. rewrite !inv_eq /inv_def. iIntros "#INV !>" (E i3 _ NE).
    iMod ("INV" $! E NE) as "[P Close]". iClear "INV". iIntros "!>".
    rewrite !(objective_at _ _ i3). iFrame "P Close".
  Qed.

  #[global] Instance inv_weakly_objective N P :
    WeaklyObjective P -> WeaklyObjective (inv N P).
  Proof.
    intros HP i1 i2 Lei. rewrite !inv_eq /inv_def. iIntros "#INV !>" (E).
    iSpecialize ("INV" $! E).
    iDestruct (weakly_objective _ _ _ Lei with "INV") as "{INV} #INV".
    iIntros (i3 Lei3 NE).
    iDestruct (monPred_mono _ _ _ Lei3 with "INV" ) as "{INV} INV".
    iMod ("INV" $! NE) as "{INV} $".
    done.
  Qed.

  (**
  Stronger result that can also be used to prove [inv_objective_with].
  *)

  Lemma inv_obj_obj_inv N P `{!BiPersistentlyForall PROP, Objective I PROP P} :
    inv N P ⊣⊢ <obj> inv N P.
  Proof.
    constructor => i. rewrite inv_eq /inv_def monPred_at_objectively. iSplit.
    - iIntros "#INV" (j) "!>". iIntros (E j1 Lej1 NE).
      iMod ("INV" $! E NE) as "[P Close]". iClear "INV".
      iIntros "!>". rewrite objective_at. iFrame "P".
      iIntros (??) "P".
      iMod ("Close" with "[P]"); last done. by rewrite objective_at.
    - iIntros "#INV !>" (E ?? NE).
      iSpecialize ("INV" $! i). iDestruct "INV" as "#INV".
      iMod ("INV" $! E NE) as "[P Close]".
      iIntros "!>". rewrite objective_at. iFrame "P".
      iIntros (??) "P".
      iMod ("Close" with "[P]"); last done. by rewrite objective_at.
  Qed.

  Lemma inv_obj_obj_inv' N P `{!BiPersistentlyForall PROP} :
    inv N (<obj> P) ⊣⊢ <obj> inv N (<obj> P).
  Proof. apply: inv_obj_obj_inv. Qed.

  Lemma inv_objective_alt N P `{!BiPersistentlyForall PROP} :
    Objective P -> Objective (inv N P).
  Proof. intros. rewrite inv_obj_obj_inv. apply _. Qed.

End minv.

(* This establish the equivalence between base_logic.lib.invariants.inv and inv for monPred. *)
Section oinv.
  Context {I : biIndex} `{!invGS Σ}.
  #[local] Notation monPred := (monPred I (iPropI Σ)).

  Implicit Type (P : monPred).
  Definition oinv N P : monPred := ⎡ base_logic.lib.invariants.inv N (∀ i, P i) ⎤%I.

  Lemma inv_obj_oinv N P `{Objective I _ P} : <obj> inv N P ⊣⊢ oinv N P.
  Proof.
    constructor => i.
    rewrite inv_eq /inv_def /oinv monPred_at_embed monPred_at_objectively.
    rewrite base_logic.lib.invariants.inv_unseal /base_logic.lib.invariants.inv_def.
    iSplit.
    - iIntros "#INV !>" (E NE).
      iSpecialize ("INV" $! i). iDestruct "INV" as "#INV".
      iMod ("INV" $! E NE) as "[P Close]".
      iIntros "!>". iSplitL "P".
      + iIntros (i'). by rewrite objective_at.
      + iIntros "P". iMod ("Close" with "[P]"); last done.
        iIntros "!>". by iApply "P".
    - iIntros "#INV" (j) "!>". iIntros (E j1 ? NE).
      iMod ("INV" $! E NE) as "[P Close]".
      iIntros "!>". iSplitL "P".
      + iNext. by iApply "P".
      + iIntros (j2 ?) "P". iMod ("Close" with "[P]"); last done.
        iIntros "!>" (j3). by rewrite objective_at.
  Qed.

  Lemma inv_obj_oinv' N P : <obj> inv N (<obj> P) ⊣⊢ oinv N P.
  Proof.
    constructor => i.
    rewrite inv_eq /inv_def /oinv monPred_at_embed monPred_at_objectively.
    rewrite base_logic.lib.invariants.inv_unseal /base_logic.lib.invariants.inv_def.
    iSplit.
    - iIntros "#INV !>" (E NE).
      iSpecialize ("INV" $! i). iDestruct "INV" as "#INV".
      iMod ("INV" $! E NE) as "[P Close]".
      iIntros "!>". iSplitL "P".
      + iIntros (i'). rewrite monPred_at_objectively.
        iNext. by iApply "P".
      + iIntros "P". iMod ("Close" with "[P]"); last done.
        iIntros "!>". rewrite monPred_at_objectively. by iApply "P".
    - iIntros "#INV" (j) "!>". iIntros (E j1 ? NE).
      iMod ("INV" $! E NE) as "[P Close]".
      iIntros "!>". iSplitL "P".
      + iNext. rewrite monPred_at_objectively. by iApply "P".
      + iIntros (j2 ?) "P". iMod ("Close" with "[P]"); last done.
        iIntros "!>" (j3). rewrite monPred_at_objectively.
        by iApply "P".
  Qed.
End oinv.

#[global] Hint Opaque oinv : typeclass_instances br_opacity.


(** Non-atomic invariants for monPred. *)
(* TODO FM-2323 *)
#[global] Remove Hints na_inv_inG : typeclass_instances.
#[global] Existing Instance na_inv_inG.
(** Allocation rules for monPred that are tied specifically to iProp. *)
(* Derived from
  https://gitlab.mpi-sws.org/iris/iris/-/blob/90b6007faea2b61546aed01fe0ed9936b55468d1/iris/base_logic/lib/na_invariants.v *)
Section na_inv_alloc.
  Import iris.algebra.gset iris.algebra.coPset.
  Context {K J : biIndex} `{!invGS Σ, !na_invG Σ}.

  Notation monPred := (monPred K (iPropI Σ)).
  Notation monPredI := (monPredI K (iPropI Σ)).

  Implicit Types (i j : K) (p : na_inv_pool_name) (P Q R : monPred).
  #[local] Typeclasses Transparent na_own na_inv.

  #[global] Instance na_own_weakly_objective p E :
    WeaklyObjective (na_own p E : monPred) := _.

  #[global] Instance na_inv_objective p N P :
    Objective P -> Objective (na_inv p N P) := _.

  Lemma na_inv_alloc p E N P `{!WeaklyObjective P} : ▷ P ⊢ |={E}=> na_inv p N P.
  Proof.
    iIntros "HP".
    iMod (own_unit (A:=prodUR coPset_disjUR (gset_disjUR positive)) p) as "Hempty".
    iMod (own_updateP with "Hempty") as ([m1 m2]) "[Hm Hown]".
    { apply prod_updateP'.
      - apply cmra_updateP_id, (reflexivity (R:=eq)).
      - apply (gset_disj_alloc_empty_updateP_strong' (K:=positive) (λ i : positive, i ∈ (↑N:coPset))).
        intros Ef. exists (coPpick (↑ N ∖ gset_to_coPset Ef)).
        rewrite -elem_of_gset_to_coPset comm -elem_of_difference.
        apply coPpick_elem_of=> Hfin.
        eapply nclose_infinite, (difference_finite_inv _ _), Hfin.
        apply gset_to_coPset_finite. }
    simpl. iDestruct "Hm" as %(<- & i & -> & ?).
    iMod (inv_alloc N with "[-]"); last (iModIntro; iExists i; eauto).
    { apply _. }
    iNext. iLeft. by iFrame.
  Qed.
End na_inv_alloc.

#[global] Hint Opaque na_own na_inv : typeclass_instances br_opacity.

(** Cancelable invariants for monPred *)
(* TODO FM-2323 *)
#[global] Remove Hints cinv_inG : typeclass_instances.
#[global] Existing Instance cinv_inG.
(* Allocation rules for monPred that are tied specifically to iProp. *)
Section allocation.
  Context {K J : biIndex} `{!invGS Σ, !cinvG Σ}.
  #[local] Typeclasses Transparent cinv_own cinv.


  Notation monPred := (monPred K (iPropI Σ)).
  Notation monPredI := (monPredI K (iPropI Σ)).

  Implicit Types (i j : K) (γ : gname) (P Q R : monPred).

  #[global] Instance cinv_own_weakly_objective γ q :
    WeaklyObjective (cinv_own γ q : monPred) := _.
  (* Note: Eventually the following instance may cease to hold *)

  #[global] Instance cinv_objective N γ P :
    Objective P -> Objective (cinv N γ P) := _.

  #[global] Instance cinv_weakly_objective N γ P :
    WeaklyObjective P -> WeaklyObjective (cinv N γ P) := _.

  (*** Allocation rules. *)
  (** The "strong" variants permit any infinite [I], and choosing [P] is delayed
  until after [γ] was chosen.*)
  Lemma cinv_alloc_strong (I : gname → Prop) E N :
    pred_infinite I →
    ⊢ |={E}=> ∃ γ, [| I γ |] ∗ cinv_own γ 1 ∗
                    ∀ P (_ : WeaklyObjective P), ▷ P ={E}=∗ cinv N γ P.
  Proof.
    iIntros (?). iMod (own_alloc_strong' 1%Qp I) as (γ) "[Hfresh Hγ]"; [done|done|].
    iExists γ. iIntros "!> {$Hγ $Hfresh}" (P WO) "HP".
    iMod (inv_alloc N _ (P ∨ cinv_own γ 1) with "[HP]"); eauto.
  Qed.

  (** The "open" variants create the invariant in the open state, and delay
  having to prove [P].
  These do not imply the other variants because of the extra assumption [↑N ⊆ E]. *)
  Lemma cinv_alloc_strong_open (I : gname → Prop) E N :
    pred_infinite I →
    ↑N ⊆ E →
    ⊢ |={E}=> ∃ γ, [| I γ |] ∗ cinv_own γ 1 ∗
      ∀ P (_ : WeaklyObjective P), |={E,E∖↑N}=> cinv N γ P ∗ (▷ P ={E∖↑N,E}=∗ emp).
  Proof.
    iIntros (??). iMod (own_alloc_strong' 1%Qp I) as (γ) "[Hfresh Hγ]"; [done|done|].
    iExists γ. iIntros "!> {$Hγ $Hfresh}" (P WO).
    iMod (inv_alloc_open N _ (P ∨ cinv_own γ 1)) as "[Hinv Hclose]"; first by eauto.
    iIntros "!>". iFrame. iIntros "HP". iApply "Hclose". iLeft. done.
  Qed.

  Lemma cinv_alloc_cofinite (G : gset gname) E N :
    ⊢ |={E}=> ∃ γ, [| γ ∉ G |] ∗ cinv_own γ 1 ∗
                    ∀ P (_ : WeaklyObjective P), ▷ P ={E}=∗ cinv N γ P.
  Proof.
    apply cinv_alloc_strong. apply (pred_infinite_set (C:=gset gname))=> E'.
    exists (fresh (G ∪ E')). apply not_elem_of_union, is_fresh.
  Qed.

  Lemma cinv_alloc E N P `{!WeaklyObjective P} :
    ▷ P ⊢ |={E}=> ∃ γ, cinv N γ P ∗ cinv_own γ 1.
  Proof.
    iIntros "HP". iMod (cinv_alloc_cofinite ∅ E N) as (γ _) "[Hγ Halloc]".
    iExists γ. iFrame "Hγ". by iApply "Halloc".
  Qed.

  Lemma cinv_alloc_open E N P `{WO: WeaklyObjective _ _ P} :
    ↑N ⊆ E → ⊢ |={E,E∖↑N}=> ∃ γ, cinv N γ P ∗ cinv_own γ 1 ∗ (▷ P ={E∖↑N,E}=∗ emp).
  Proof.
    iIntros (?). iMod (cinv_alloc_strong_open (λ _, True)) as (γ) "(_ & Htok & Hmake)"; [|done|].
    { apply pred_infinite_True. }
    iMod ("Hmake" $! P WO) as "[Hinv Hclose]". iIntros "!>". iExists γ. iFrame.
  Qed.

  Lemma cinv_alloc_ghost_named_inv
    E N (I : gname → monPred) `{WO: ∀ γ, WeaklyObjective (I γ)} :
    (∀ γ , I γ) ⊢ |={E}=> ∃ γ, cinv N γ (I γ) ∗ cinv_own γ 1.
  Proof.
    iIntros "I".
    iMod (cinv_alloc_cofinite empty E N) as (γ ?) "[HO HI]".
    iSpecialize ("I" $! γ).
    iMod ("HI" $! (I γ) (WO _) with "[$I]") as "HI".
    iIntros "!>". eauto with iFrame.
  Qed.
End allocation.
