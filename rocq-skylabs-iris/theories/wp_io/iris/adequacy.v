(*
 * Copyright (c) 2023 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.

 * ALL of the following code is derived from code original to the
 * Iris project. That original code is
 *
 *	Copyright Iris developers and contributors
 *
 * and used according to the following license.
 *
 *	SPDX-License-Identifier: BSD-3-Clause
 *
 * Original Iris License:
 * https://gitlab.mpi-sws.org/iris/iris/-/blob/cb324b81f5b00a7cb8ae186d7aca5011350037cd/LICENSE-CODE
 *)

(**
This generalize [iris.program_logic.adequacy] for PROP.

This is ignoring later credits (£).

TODO : upstream.
*)

Require Import iris.algebra.gmap.
Require Import iris.algebra.auth.
Require Import iris.algebra.agree.
Require Import iris.algebra.gset.
Require Import iris.algebra.coPset.
Require Import bluerock.iris.extra.proofmode.proofmode.
Require Import iris.program_logic.adequacy.
Require Export bluerock.iris.extra.wp_io.iris.weakestpre.

(** This file contains the adequacy statements of the Iris program logic. First
we prove a number of auxilary results. *)
Section adequacy.
Context {Λ} {PROP : bi} `{!BiFUpd PROP} `{!BiLaterContractive PROP}
        `{!irisGS_gen Λ PROP}.

Implicit Types e : expr Λ.
Implicit Types P Q : PROP.
Implicit Types Φ : val Λ → PROP.
Implicit Types Φs : list (val Λ → PROP).

Notation wptp s t Φs := ([∗ list] e;Φ ∈ t;Φs, WP e @ s; ⊤ {{ Φ }})%I.

#[local] Lemma wp_step s e1 σ1 ns κ κs e2 σ2 efs nt Φ :
  prim_step e1 σ1 κ e2 σ2 efs →
  state_interp σ1 ns (κ ++ κs) nt -∗
  (* £ (S (num_laters_per_step ns)) -∗ *)
  WP e1 @ s; ⊤ {{ Φ }}
    ={⊤,∅}=∗ |={∅}▷=>^(S $ num_laters_per_step ns) |={∅,⊤}=>
    state_interp σ2 (S ns) κs (nt + length efs) ∗ WP e2 @ s; ⊤ {{ Φ }} ∗
    wptp s efs (replicate (length efs) fork_post).
Proof.
  rewrite {1}wp_unfold /wp_pre. iIntros (?) "Hσ H".
  rewrite (val_stuck e1 σ1 κ e2 σ2 efs) //.
  iMod ("H" $! σ1 ns with "Hσ") as "(_ & H)". iModIntro.
  iApply (step_fupdN_wand with "(H [//])"). iIntros ">H !>".
  by rewrite Nat.add_comm big_sepL2_replicate_r.
Qed.

#[local] Lemma wptp_step s es1 es2 κ κs σ1 ns σ2 Φs nt :
  step (es1,σ1) κ (es2, σ2) →
  state_interp σ1 ns (κ ++ κs) nt -∗
  (* £ (S (num_laters_per_step ns)) -∗ *)
  wptp s es1 Φs -∗
  ∃ nt', |={⊤,∅}=> |={∅}▷=>^(S $ num_laters_per_step$ ns) |={∅,⊤}=>
         state_interp σ2 (S ns) κs (nt + nt') ∗
         wptp s es2 (Φs ++ replicate nt' fork_post).
Proof.
  iIntros (Hstep) "Hσ Ht".
  destruct Hstep as [e1' σ1' e2' σ2' efs t2' t3 Hstep]; simplify_eq/=.
  iDestruct (big_sepL2_app_inv_l with "Ht") as (Φs1 Φs2 ->) "[? Ht]".
  iDestruct (big_sepL2_cons_inv_l with "Ht") as (Φ Φs3 ->) "[Ht ?]".
  iExists _. iMod (wp_step with "Hσ Ht") as "H"; first done. iModIntro.
  iApply (step_fupdN_wand with "H"). iIntros ">($ & He2 & Hefs) !>".
  rewrite -(assoc_L app) -app_comm_cons. iFrame.
Qed.


(* The total number of laters used between the physical steps number
   [start] (included) to [start+ns] (excluded). *)
#[local] Fixpoint steps_sum (num_laters_per_step : nat → nat) (start ns : nat) : nat :=
  match ns with
  | O => 0
  | S ns =>
    S $ num_laters_per_step start + steps_sum num_laters_per_step (S start) ns
  end.

#[local] Lemma wptp_preservation s n es1 es2 κs κs' σ1 ns σ2 Φs nt :
  nsteps n (es1, σ1) κs (es2, σ2) →
  state_interp σ1 ns (κs ++ κs') nt -∗
  (* £ (steps_sum num_laters_per_step ns n) -∗ *)
  wptp s es1 Φs
  ={⊤,∅}=∗ |={∅}▷=>^(steps_sum num_laters_per_step ns n) |={∅,⊤}=> ∃ nt',
    state_interp σ2 (n + ns) κs' (nt + nt') ∗
    wptp s es2 (Φs ++ replicate nt' fork_post).
Proof.
  revert nt es1 es2 κs κs' σ1 ns σ2 Φs.
  induction n as [|n IH]=> nt es1 es2 κs κs' σ1 ns σ2 Φs.
  { inversion_clear 1; iIntros "? ?"; iExists 0=> /=.
    rewrite Nat.add_0_r right_id_L. iFrame. by iApply fupd_mask_subseteq. }
  iIntros (Hsteps) "Hσ He". inversion_clear Hsteps as [|?? [t1' σ1']].
  rewrite -(assoc_L (++)) /= Nat.iter_add -{1}plus_Sn_m /= plus_n_Sm.
  (* rewrite lc_split. iDestruct "Hcred" as "[Hc1 Hc2]". *)
  iDestruct (wptp_step with "Hσ He") as (nt') ">H"; first eauto; simplify_eq.
  iModIntro. iApply step_fupdN_S_fupd. iApply (step_fupdN_wand with "H").
  iIntros ">(Hσ & He)". iMod (IH with "Hσ He") as "IH"; first done. iModIntro.
  iApply (step_fupdN_wand with "IH"). iIntros ">IH".
  iDestruct "IH" as (nt'') "[??]".
  rewrite -Nat.add_assoc -(assoc_L app) -replicate_add. by eauto with iFrame.
Qed.

#[local] Lemma wp_not_stuck κs nt e σ ns Φ :
  state_interp σ ns κs nt -∗ WP e {{ Φ }} ={⊤, ∅}=∗ ⌜not_stuck e σ⌝.
Proof.
  rewrite wp_unfold /wp_pre /not_stuck. iIntros "Hσ H".
  destruct (to_val e) as [v|] eqn:?.
  { iMod (fupd_mask_subseteq ∅); first set_solver. iModIntro. eauto. }
  iMod ("H" $! σ ns [] κs with "Hσ") as "[% He]".
  iModIntro. eauto.
Qed.

(** The adequacy statement of Iris consists of two parts:
      (1) the postcondition for all threads that have terminated in values
      and (2) progress (i.e., after n steps the program is not stuck).
    For an n-step execution of a thread pool, the two parts are given by
    [wptp_strong_adequacy] and [wptp_progress] below.

    For the final adequacy theorem of Iris, [wp_strong_adequacy_gen], we would
    like to instantiate the Iris proof (i.e., instantiate the
    [∀ {Hinv : !invGS_gen hlc Σ} κs, ...]) and then use both lemmas to get
    progress and the postconditions. Unfortunately, since the addition of later
    credits, this is no longer possible, because the original proof relied on an
    interaction of the update modality and plain propositions. So instead, we
    employ a trick: we duplicate the instantiation of the Iris proof, such
    that we can "run the WP proof twice". That is, we instantiate the
    [∀ {Hinv : !invGS_gen hlc Σ} κs, ...] both in [wp_progress_gen] and
    [wp_strong_adequacy_gen]. In doing  so, we can avoid the interactions with
    the plain modality. In [wp_strong_adequacy_gen], we can then make use of
    [wp_progress_gen] to prove the progress component of the main adequacy theorem.
*)

#[local] Lemma wptp_postconditions Φs κs' s n es1 es2 κs σ1 ns σ2 nt:
  nsteps n (es1, σ1) κs (es2, σ2) →
  state_interp σ1 ns (κs ++ κs') nt -∗
  (* £ (steps_sum num_laters_per_step ns n) -∗ *)
  wptp s es1 Φs
  ={⊤,∅}=∗ |={∅}▷=>^(steps_sum num_laters_per_step ns n) |={∅,⊤}=> ∃ nt',
    state_interp σ2 (n + ns) κs' (nt + nt') ∗
    [∗ list] e;Φ ∈ es2;Φs ++ replicate nt' fork_post, from_option Φ True (to_val e).
Proof.
  iIntros (Hstep) "Hσ He". iMod (wptp_preservation with "Hσ He") as "Hwp"; first done.
  iModIntro. iApply (step_fupdN_wand with "Hwp").
  iMod 1 as (nt') "(Hσ & Ht)"; simplify_eq/=.
  iExists _. iFrame "Hσ".
  iApply big_sepL2_fupd.
  iApply (big_sepL2_impl with "Ht").
  iIntros "!#" (? e Φ ??) "Hwp".
  destruct (to_val e) as [v2|] eqn:He2'; last done.
  apply of_to_val in He2' as <-. simpl. iApply wp_value_fupd'. done.
Qed.

#[local] Lemma wptp_progress Φs κs' n es1 es2 κs σ1 ns σ2 nt e2 :
  nsteps n (es1, σ1) κs (es2, σ2) →
  e2 ∈ es2 →
  state_interp σ1 ns (κs ++ κs') nt -∗
  (* £ (steps_sum num_laters_per_step ns n) -∗ *)
  wptp NotStuck es1 Φs
  ={⊤,∅}=∗ |={∅}▷=>^(steps_sum num_laters_per_step ns n) |={∅}=> ⌜not_stuck e2 σ2⌝.
Proof.
  iIntros (Hstep Hel) "Hσ He". iMod (wptp_preservation with "Hσ He") as "Hwp"; first done.
  iModIntro. iApply (step_fupdN_wand with "Hwp").
  iMod 1 as (nt') "(Hσ & Ht)"; simplify_eq/=.
  eapply elem_of_list_lookup in Hel as [i Hlook].
  destruct ((Φs ++ replicate nt' fork_post) !! i) as [Φ|] eqn: Hlook2; last first.
  { rewrite big_sepL2_alt. iDestruct "Ht" as "[%Hlen _]". exfalso.
    eapply lookup_lt_Some in Hlook. rewrite Hlen in Hlook.
    eapply lookup_lt_is_Some_2 in Hlook. rewrite Hlook2 in Hlook.
    destruct Hlook as [? ?]. naive_solver. }
  iDestruct (big_sepL2_lookup_acc with "Ht") as "[Ht ?]"; [try done..|].
  iApply (wp_not_stuck with "Hσ Ht").
Qed.
End adequacy.

(** * ALL RESULTS BELOW ARE TIED SPECIFICALLY TO [iProp] *)
Import uPred.

#[local] Lemma wp_progress_gen Σ Λ `{!invGpreS Σ} es σ1 n κs t2 σ2 e2
        (num_laters_per_step : nat → nat)  :
    (∀ `{Hinv : !invGS_gen HasNoLc Σ},
      ⊢ |={⊤}=> ∃
        (stateI : state Λ → nat → list (observation Λ) → nat → iProp Σ)
        (Φs : list (val Λ → iProp Σ))
        (fork_post : val Λ → iProp Σ)
        state_interp_mono,
        let _ : irisGS_gen Λ (iProp Σ) :=
          IrisG stateI fork_post num_laters_per_step state_interp_mono in
        stateI σ1 0 κs 0 ∗ ([∗ list] e;Φ ∈ es;Φs, WP e @ ⊤ {{ Φ }})) →
  nsteps n (es, σ1) κs (t2, σ2) →
  e2 ∈ t2 →
  not_stuck e2 σ2.
Proof.
  iIntros (Hwp ??).
  eapply pure_soundness.
  eapply (step_fupdN_soundness_gen _ HasNoLc (steps_sum num_laters_per_step 0 n)
    (steps_sum num_laters_per_step 0 n)).
  iIntros (Hinv) "Hcred".
  iMod Hwp as (stateI Φ fork_post state_interp_mono) "(Hσ & Hwp)".
  iDestruct (big_sepL2_length with "Hwp") as %Hlen1.
  iMod (@wptp_progress _ _ _ _
       (IrisG stateI fork_post num_laters_per_step state_interp_mono) _ []
    with "[Hσ] Hwp") as "H"; [done| done |by rewrite right_id_L|].
  iAssert (|={∅}▷=>^(steps_sum num_laters_per_step 0 n) |={∅}=> ⌜not_stuck e2 σ2⌝)%I
    with "[-]" as "H"; last first.
  { destruct steps_sum; [done|].  by iApply step_fupdN_S_fupd. }
  iApply (step_fupdN_wand with "H"). iIntros "$".
Qed.

(** Iris's generic adequacy result *)
Lemma wp_strong_adequacy_gen Σ Λ `{!invGpreS Σ} s es σ1 n κs t2 σ2 φ
        (num_laters_per_step : nat → nat) :
  (* WP *)
  (∀ `{Hinv : !invGS_gen HasNoLc Σ},
      ⊢ |={⊤}=> ∃
          (stateI : state Λ → nat → list (observation Λ) → nat → iProp Σ)
          (Φs : list (val Λ → iProp Σ))
          (fork_post : val Λ → iProp Σ)
          (* Note: existentially quantifying over Iris goal! [iExists _] should
          usually work. *)
          state_interp_mono,
        let _ : irisGS_gen Λ (iProp Σ) :=
          IrisG stateI fork_post num_laters_per_step state_interp_mono in
        stateI σ1 0 κs 0 ∗
        ([∗ list] e;Φ ∈ es;Φs, WP e @ s; ⊤ {{ Φ }}) ∗
        (∀ es' t2',
          (* es' is the final state of the initial threads, t2' the rest *)
          ⌜ t2 = es' ++ t2' ⌝ -∗
          (* es' corresponds to the initial threads *)
          ⌜ length es' = length es ⌝ -∗
          (* If this is a stuck-free triple (i.e. [s = NotStuck]), then all
          threads in [t2] are not stuck *)
          ⌜ ∀ e2, s = NotStuck → e2 ∈ t2 → not_stuck e2 σ2 ⌝ -∗
          (* The state interpretation holds for [σ2] *)
          stateI σ2 n [] (length t2') -∗
          (* If the initial threads are done, their post-condition [Φ] holds *)
          ([∗ list] e;Φ ∈ es';Φs, from_option Φ True (to_val e)) -∗
          (* For all forked-off threads that are done, their postcondition
              [fork_post] holds. *)
          ([∗ list] v ∈ omap to_val t2', fork_post v) -∗
          (* Under all these assumptions, and while opening all invariants, we
          can conclude [φ] in the logic. After opening all required invariants,
          one can use [fupd_mask_subseteq] to introduce the fancy update. *)
          |={⊤,∅}=> ⌜ φ ⌝)) →
  nsteps n (es, σ1) κs (t2, σ2) →
  (* Then we can conclude [φ] at the meta-level. *)
  φ.
Proof.
  iIntros (Hwp ?).
  eapply pure_soundness.
  eapply (step_fupdN_soundness_gen _ HasNoLc (steps_sum num_laters_per_step 0 n)
    (steps_sum num_laters_per_step 0 n)).
  iIntros (Hinv) "Hcred".
  iMod Hwp as (stateI Φ fork_post state_interp_mono) "(Hσ & Hwp & Hφ)".
  iDestruct (big_sepL2_length with "Hwp") as %Hlen1.
  iMod (@wptp_postconditions _ _ _ _
       (IrisG stateI fork_post num_laters_per_step state_interp_mono) _ []
    with "[Hσ] Hwp") as "H"; [done|by rewrite right_id_L|].
  iAssert (|={∅}▷=>^(steps_sum num_laters_per_step 0 n) |={∅}=> ⌜φ⌝)%I
    with "[-]" as "H"; last first.
  { destruct steps_sum; [done|]. by iApply step_fupdN_S_fupd. }
  iApply (step_fupdN_wand with "H").
  iMod 1 as (nt') "(Hσ & Hval) /=".
  iDestruct (big_sepL2_app_inv_r with "Hval") as (es' t2' ->) "[Hes' Ht2']".
  iDestruct (big_sepL2_length with "Ht2'") as %Hlen2.
  rewrite length_replicate in Hlen2; subst.
  iDestruct (big_sepL2_length with "Hes'") as %Hlen3.
  rewrite -plus_n_O.
  iApply ("Hφ" with "[//] [%] [ ] Hσ Hes'");
    (* FIXME: Different implicit types for [length] are inferred, so [lia] and
    [congruence] do not work due to https://github.com/coq/coq/issues/16634 *)
    [by rewrite Hlen1 Hlen3| |]; last first.
  { by rewrite big_sepL2_replicate_r // big_sepL_omap. }
  (* At this point in the adequacy proof, we use a trick: we effectively run the
    user-provided WP proof again (i.e., instantiate the `invGS_gen` and execute the
    program) by using the lemma [wp_progress_gen]. In doing so, we can obtain
    the progress part of the adequacy theorem.
  *)
  iPureIntro. intros e2 -> Hel.
  eapply (wp_progress_gen);
    [ done | clear stateI Φ fork_post state_interp_mono Hlen1 Hlen3 | done|done].
  iIntros (?).
  iMod Hwp as (stateI Φ fork_post state_interp_mono) "(Hσ & Hwp & Hφ)".
  iModIntro. iExists _, _, _, _. iFrame.
Qed.

(** This simpler form of adequacy requires the [irisGS] instance that you use
everywhere to syntactically be of the form
{|
  iris_invGS := ...;
  state_interp σ _ κs _ := ...;
  fork_post v := ...;
  num_laters_per_step _ := 0;
  state_interp_mono _ _ _ _ := fupd_intro _ _;
|}
In other words, the state interpretation must ignore [ns] and [nt], the number
of laters per step must be 0, and the proof of [state_interp_mono] must have
this specific proof term.
*)
Lemma wp_adequacy_gen Σ Λ `{!invGpreS Σ} s e σ φ :
  (∀ `{Hinv : !invGS_gen HasNoLc Σ} κs,
    ⊢ |={⊤}=> ∃
        (stateI : state Λ → list (observation Λ) → iProp Σ)
        (fork_post : val Λ → iProp Σ),
        let _ : irisGS_gen Λ (iProp Σ) :=
          IrisG (λ σ _ κs _, stateI σ κs) fork_post (λ _, 0) (λ _ _ _ _, fupd_intro _ _) in
        stateI σ κs ∗ WP e @ s; ⊤ {{ v, ⌜φ v⌝ }}) →
  adequate s e σ (λ v _, φ v).
Proof.
  intros Hwp. apply adequate_alt; intros t2 σ2 [n [κs ?]]%erased_steps_nsteps.
  eapply (wp_strong_adequacy_gen Σ _); [ | done]=> ?.
  iMod Hwp as (stateI fork_post) "[Hσ Hwp]".
  iExists (λ σ _ κs _, stateI σ κs), [(λ v, ⌜φ v⌝%I)], fork_post, _ => /=.
  iIntros "{$Hσ $Hwp} !>" (e2 t2' -> ? ?) "_ H _".
  iApply fupd_mask_intro_discard; [done|]. iSplit; [|done].
  iDestruct (big_sepL2_cons_inv_r with "H") as (e' ? ->) "[Hwp H]".
  iDestruct (big_sepL2_nil_inv_r with "H") as %->.
  iIntros (v2 t2'' [= -> <-]). by rewrite to_of_val.
Qed.

Lemma wp_invariance_gen Σ Λ `{!invGpreS Σ} s e1 σ1 t2 σ2 φ :
  (∀ `{Hinv : !invGS_gen HasNoLc Σ} κs,
    ⊢ |={⊤}=> ∃
        (stateI : state Λ → list (observation Λ) → nat → iProp Σ)
        (fork_post : val Λ → iProp Σ),
        let _ : irisGS_gen Λ (iProp Σ) :=
          IrisG (λ σ _, stateI σ) fork_post (λ _, 0) (λ _ _ _ _, fupd_intro _ _) in
        stateI σ1 κs 0 ∗ WP e1 @ s; ⊤ {{ _, True }} ∗
        (stateI σ2 [] (pred (length t2)) -∗ ∃ E, |={⊤,E}=> ⌜φ⌝)) →
  rtc erased_step ([e1], σ1) (t2, σ2) →
  φ.
Proof.
  intros Hwp [n [κs ?]]%erased_steps_nsteps.
  eapply (wp_strong_adequacy_gen Σ); [done| |done]=> ?.
  iMod (Hwp _ κs) as (stateI fork_post) "(Hσ & Hwp & Hφ)".
  iExists (λ σ _, stateI σ), [(λ _, True)%I], fork_post, _ => /=.
  iIntros "{$Hσ $Hwp} !>" (e2 t2' -> _ _) "Hσ H _ /=".
  iDestruct (big_sepL2_cons_inv_r with "H") as (? ? ->) "[_ H]".
  iDestruct (big_sepL2_nil_inv_r with "H") as %->.
  iDestruct ("Hφ" with "Hσ") as (E) ">Hφ".
  by iApply fupd_mask_intro_discard; first set_solver.
Qed.
