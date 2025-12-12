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

(** ** General WP for [PROP : bi]

This generalizes [iris.program_logic.weakestpre] to any PROP.

However, this is ignoring later credits (£) which, for now, are still tied
to iProp.

TODO : upstream.
*)

Require Import iris.proofmode.base.
Require Import bluerock.iris.extra.proofmode.proofmode.
Require Import iris.proofmode.classes.
Require Export bluerock.iris.extra.bi.only_provable.
Require Export bluerock.iris.extra.wp_io.iris.ghost.

(** The predicate we take the fixpoint of in order to define the WP. *)
(** In the step case, we both provide [S (num_laters_per_step ns)]
  later credits, as well as an iterated update modality that allows
  stripping as many laters, where [ns] is the number of steps already taken.
  We have both as each of these provides distinct advantages:
  - Later credits do not have to be used right away, but can be kept to
    eliminate laters at a later point.
  - The step-taking update composes well in parallel: we can independently
    compose two clients who want to eliminate their laters for the same
    physical step, which is not possible with later credits, as they
    can only be used by exactly one client.
  - The step-taking update can even be used by clients that opt out of
    later credits, e.g. because they use [BiFUpdPlainly]. *)
Definition wp_pre
    {Λ} {PROP : bi} `{!FUpd PROP} `{!irisGS_gen Λ PROP}
    (s : stuckness)
    (wp : coPset -d> expr Λ -d> (val Λ -d> PROP) -d> PROP) :
    coPset -d> expr Λ -d> (val Λ -d> PROP) -d> PROP := λ E e1 Φ,
  match to_val e1 with
  | Some v => |={E}=> Φ v
  | None => ∀ σ1 ns κ κs nt,
     state_interp σ1 ns (κ ++ κs) nt ={E,∅}=∗
       [| if s is NotStuck then reducible e1 σ1 else True |] ∗
       ∀ e2 σ2 efs, [| prim_step e1 σ1 κ e2 σ2 efs |]
         (* -∗ *)
         (* £ (S (num_laters_per_step ns)) *)
         ={∅}▷=∗^(S $ num_laters_per_step ns) |={∅,E}=>
         state_interp σ2 (S ns) κs (length efs + nt) ∗
         wp E e2 Φ ∗
         [∗ list] i ↦ ef ∈ efs, wp ⊤ ef fork_post
  end%I.

Local Instance wp_pre_contractive
  {Λ} {PROP : bi} `{!BiFUpd PROP} `{!BiLaterContractive PROP}
  `{!irisGS_gen Λ PROP} s : Contractive (wp_pre s).
Proof.
  rewrite /wp_pre /= => n wp wp' Hwp E e1 Φ.
  do 24 (f_contractive || f_equiv).
  (* FIXME : simplify this proof once we have a good definition and a
     proper instance for step_fupdN. *)
  induction num_laters_per_step as [|k IH]; simpl.
  - f_equiv. repeat (f_contractive || f_equiv); apply Hwp.
  - by rewrite -IH.
Qed.

Local Definition wp_def
  {Λ} {PROP : bi} `{!BiFUpd PROP} `{!BiLaterContractive PROP}
  `{!irisGS_gen Λ PROP} :
  Wp PROP (expr Λ) (val Λ) stuckness :=
  λ s : stuckness, fixpoint (wp_pre s).
Local Definition wp_aux : seal (@wp_def). Proof. by eexists. Qed.
Definition wp' := wp_aux.(unseal).
Global Arguments wp' {Λ PROP _ _ _}.
Global Existing Instance wp'.
Local Lemma wp_unseal
  {Λ} {PROP : bi} `{!BiFUpd PROP} `{!BiLaterContractive PROP}
  `{!irisGS_gen Λ PROP} : wp = @wp_def Λ PROP _ _ _.
Proof. rewrite -wp_aux.(seal_eq) //. Qed.

Section wp.
Context {Λ} {PROP : bi} `{!BiFUpd PROP} `{!BiLaterContractive PROP}
        `{!irisGS_gen Λ PROP}.
Implicit Types s : stuckness.
Implicit Types P : PROP.
Implicit Types Φ : val Λ → PROP.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.

(* Weakest pre *)
Lemma wp_unfold s E e Φ :
  WP e @ s; E {{ Φ }} ⊣⊢ wp_pre s (wp (PROP:=PROP) s) E e Φ.
Proof. rewrite wp_unseal. apply (fixpoint_unfold (wp_pre s)). Qed.

Global Instance wp_ne s E e n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (wp (PROP:=PROP) s E e).
Proof.
  revert e. induction (lt_wf n) as [n _ IH]=> e Φ Ψ HΦ.
  rewrite !wp_unfold /wp_pre /=.
  (* FIXME: figure out a way to properly automate this proof *)
  (* FIXME: reflexivity, as being called many times by f_equiv and f_contractive
  is very slow here *)
  do 24 (f_contractive || f_equiv).
  (* FIXME : simplify this proof once we have a good definition and a
     proper instance for step_fupdN. *)
  induction num_laters_per_step as [|k IHk]; simpl; last by rewrite IHk.
  rewrite IH; [done|cbn in *; lia|]. intros v. by eapply dist_lt.
Qed.
Global Instance wp_proper s E e :
  Proper (pointwise_relation _ (≡) ==> (≡)) (wp (PROP:=PROP) s E e).
Proof.
  by intros Φ Φ' ?; apply equiv_dist=>n; apply wp_ne=>v; apply equiv_dist.
Qed.
Global Instance wp_contractive s E e n :
  TCEq (to_val e) None →
  Proper (pointwise_relation _ (dist_later n) ==> dist n) (wp (PROP:=PROP) s E e).
Proof.
  intros He Φ Ψ HΦ. rewrite !wp_unfold /wp_pre He /=.
  do 23 (f_contractive || f_equiv).
  (* FIXME : simplify this proof once we have a good definition and a
     proper instance for step_fupdN. *)
  induction num_laters_per_step as [|k IHk]; simpl; last by rewrite IHk.
  by do 4 f_equiv.
Qed.

Lemma wp_value_fupd' s E Φ v : WP of_val v @ s; E {{ Φ }} ⊣⊢ |={E}=> Φ v.
Proof. rewrite wp_unfold /wp_pre to_of_val. auto. Qed.

Lemma wp_strong_mono s1 s2 E1 E2 e Φ Ψ :
  s1 ⊑ s2 → E1 ⊆ E2 →
  WP e @ s1; E1 {{ Φ }} -∗ (∀ v, Φ v ={E2}=∗ Ψ v) -∗ WP e @ s2; E2 {{ Ψ }}.
Proof.
  iIntros (? HE) "H HΦ". iLöb as "IH" forall (e E1 E2 HE Φ Ψ).
  rewrite !wp_unfold /wp_pre /=.
  destruct (to_val e) as [v|] eqn:?.
  { iApply ("HΦ" with "[> -]"). by iApply (fupd_mask_mono E1 _). }
  iIntros (σ1 ns κ κs nt) "Hσ".
  iMod (fupd_mask_subseteq E1) as "Hclose"; first done.
  iMod ("H" with "[$]") as "[% H]".
  iModIntro. iSplit; [by destruct s1, s2|]. iIntros (e2 σ2 efs) "Step".
  iMod ("H" with "Step") as "H". iIntros "!> !>".  iMod "H". iModIntro.
  iApply (step_fupdN_wand with "[H]"); first by iApply "H".
  iIntros ">($ & H & Hefs)". iMod "Hclose" as "_". iModIntro. iSplitR "Hefs".
  - iApply ("IH" with "[//] H HΦ").
  - iApply (big_sepL_impl with "Hefs"); iIntros "!>" (k ef _).
    iIntros "H". iApply ("IH" with "[] H"); auto.
Qed.

Lemma fupd_wp s E e Φ : (|={E}=> WP e @ s; E {{ Φ }}) ⊢ WP e @ s; E {{ Φ }}.
Proof.
  rewrite wp_unfold /wp_pre. iIntros "H". destruct (to_val e) as [v|] eqn:?.
  { by iMod "H". }
  iIntros (σ1 ns κ κs nt) "Hσ1". iMod "H". by iApply "H".
Qed.
Lemma wp_fupd s E e Φ : WP e @ s; E {{ v, |={E}=> Φ v }} ⊢ WP e @ s; E {{ Φ }}.
Proof. iIntros "H". iApply (wp_strong_mono s s E with "H"); auto. Qed.

Lemma wp_atomic s E1 E2 e Φ `{!Atomic (stuckness_to_atomicity s) e} :
  (|={E1,E2}=> WP e @ s; E2 {{ v, |={E2,E1}=> Φ v }}) ⊢ WP e @ s; E1 {{ Φ }}.
Proof.
  iIntros "H". rewrite !wp_unfold /wp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { by iDestruct "H" as ">>> $". }
  iIntros (σ1 ns κ κs nt) "Hσ". iMod "H". iMod ("H" $! σ1 with "Hσ") as "[$ H]".
  iModIntro. iIntros (e2 σ2 efs Hstep).
  iApply (step_fupdN_wand with "(H [//])").
  iIntros ">(Hσ & H & Hefs)". destruct s.
  - rewrite !wp_unfold /wp_pre. destruct (to_val e2) as [v2|] eqn:He2.
    + iDestruct "H" as ">> $". by iFrame.
    + iMod ("H" $! _ _ [] with "[$]") as "[H ?]". iDestruct "H" as %(? & ? & ? & ? & ?).
      by edestruct (atomic _ _ _ _ _ Hstep).
  - destruct (atomic _ _ _ _ _ Hstep) as [v <-%of_to_val].
    rewrite wp_value_fupd'. iMod "H" as ">H".
    iModIntro. iFrame "Hσ Hefs". iApply wp_value_fupd'. by iIntros "!>".
Qed.


(** This lemma gives us access to the later credits that are generated in each step,
  assuming that we have instantiated [num_laters_per_step] with a non-trivial (e.g. linear)
  function.
  This lemma can be used to provide a "regeneration" mechanism for later credits.
  [state_interp] will have to be defined in a way that involves the required regneration
  tokens. TODO: point to an example of how this is used.

  In detail, a client can use this lemma as follows:
  * the client obtains the state interpretation [state_interp _ ns _ _],
  * it uses some ghost state wired up to the interpretation to know that
    [ns = k + m], and update the state interpretation to [state_interp _ m _ _],
  * _after_ [e] has finally stepped, we get [num_laters_per_step k] later credits
    that we can use to prove [P] in the postcondition, and we have to update
    the state interpretation from [state_interp _ (S m) _ _] to
    [state_interp _ (S ns) _ _] again. *)
(*
Lemma wp_credit_access s E e Φ P :
  TCEq (to_val e) None →
  (∀ m k, num_laters_per_step m + num_laters_per_step k ≤ num_laters_per_step (m + k)) →
  (∀ σ1 ns κs nt, state_interp σ1 ns κs nt ={E}=∗
    ∃ k m, state_interp σ1 m κs nt ∗ ⌜ns = (m + k)%nat⌝ ∗
    (∀ nt σ2 κs, £ (num_laters_per_step k) -∗ state_interp σ2 (S m) κs nt ={E}=∗
      state_interp σ2 (S ns) κs nt ∗ P)) -∗
  WP e @ s; E {{ v, P ={E}=∗ Φ v }} -∗
  WP e @ s; E {{ Φ }}.
Proof.
  rewrite !wp_unfold /wp_pre /=. iIntros (-> Htri) "Hupd Hwp".
  iIntros (σ1 ns κ κs nt) "Hσ1".
  iMod ("Hupd" with "Hσ1") as (k m) "(Hσ1 & -> & Hpost)".
  iMod ("Hwp" with "Hσ1") as "[$ Hwp]". iModIntro.
  iIntros (e2 σ2 efs Hstep) "Hc".
  iDestruct "Hc" as "[Hone Hc]".
  iPoseProof (lc_weaken with "Hc") as "Hc"; first apply Htri.
  iDestruct "Hc" as "[Hm Hk]".
  iCombine "Hone Hm" as "Hm".
  iApply (step_fupd_wand with "(Hwp [//] Hm)"). iIntros "Hwp".
  iApply (step_fupdN_le (num_laters_per_step m)); [ | done | ].
  { etrans; last apply Htri. lia. }
  iApply (step_fupdN_wand with "Hwp"). iIntros ">(SI & Hwp & $)".
  iMod ("Hpost" with "Hk SI") as "[$ HP]". iModIntro.
  iApply (wp_strong_mono with "Hwp"); [by auto..|].
  iIntros (v) "HΦ". iApply ("HΦ" with "HP").
Qed.
*)

(** In this stronger version of [wp_step_fupdN], the masks in the
   step-taking fancy update are a bit weird and somewhat difficult to
   use in practice. Hence, we prove it for the sake of completeness,
   but [wp_step_fupdN] is just a little bit weaker, suffices in
   practice and is easier to use.

   See the statement of [wp_step_fupdN] below to understand the use of
   ordinary conjunction here. *)
Lemma wp_step_fupdN_strong n s E1 E2 e P Φ :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (∀ σ ns κs nt, state_interp σ ns κs nt
       ={E1,∅}=∗ [| n ≤ S (num_laters_per_step ns) |]) ∧
  ((|={E1,E2}=> |={∅}▷=>^n |={E2,E1}=> P) ∗
    WP e @ s; E2 {{ v, P ={E1}=∗ Φ v }}) -∗
  WP e @ s; E1 {{ Φ }}.
Proof.
  destruct n as [|n].
  { iIntros (_ ?) "/= [_ [HP Hwp]]".
    iApply (wp_strong_mono with "Hwp"); [done..|].
    iIntros (v) "H". iApply ("H" with "[>HP]"). iMod "HP" as "$". }
  rewrite !wp_unfold /wp_pre /=. iIntros (-> ?) "H".
  iIntros (σ1 ns κ κs nt) "Hσ".
  destruct (decide (n ≤ num_laters_per_step ns)) as [Hn|Hn]; first last.
  { iDestruct "H" as "[Hn _]". iMod ("Hn" with "Hσ") as %?. lia. }
  iDestruct "H" as "[_ [>HP Hwp]]". iMod ("Hwp" with "[$]") as "[$ H]". iMod "HP".
  iIntros "!>" (e2 σ2 efs Hstep). iMod ("H" $! e2 σ2 efs with "[% //]") as "H".
  iIntros "!>!>". iMod "H". iMod "HP". iModIntro.
  revert n Hn. generalize (num_laters_per_step ns)=>n0 n Hn.
  iInduction n as [|n] "IH" forall (n0 Hn).
  - iApply (step_fupdN_wand with "H"). iIntros ">($ & Hwp & $)". iMod "HP".
    iModIntro. iApply (wp_strong_mono with "Hwp"); [done|set_solver|].
    iIntros (v) "HΦ". iApply ("HΦ" with "HP").
  - destruct n0 as [|n0]; [lia|]=>/=. iMod "HP". iMod "H". iIntros "!> !>".
    iMod "HP". iMod "H". iModIntro. iApply ("IH" with "[] HP H").
    auto with lia.
Qed.

Lemma wp_bind K `{!LanguageCtx K} s E e Φ :
  WP e @ s; E {{ v, WP K (of_val v) @ s; E {{ Φ }} }} ⊢ WP K e @ s; E {{ Φ }}.
Proof.
  iIntros "H". iLöb as "IH" forall (E e Φ). rewrite wp_unfold /wp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { apply of_to_val in He as <-. by iApply fupd_wp. }
  rewrite wp_unfold /wp_pre fill_not_val /=; [|done].
  iIntros (σ1 step κ κs n) "Hσ". iMod ("H" with "[$]") as "[% H]".
  iModIntro; iSplit.
  { destruct s; eauto using reducible_fill. }
  iIntros (e2 σ2 efs Hstep).
  destruct (fill_step_inv e σ1 κ e2 σ2 efs) as (e2'&->&?); auto.
  iMod ("H" $! e2' σ2 efs with "[//]") as "H". iIntros "!>!>".
  iMod "H". iModIntro. iApply (step_fupdN_wand with "H"). iIntros "H".
  iMod "H" as "($ & H & $)". iModIntro. by iApply "IH".
Qed.

Lemma wp_bind_inv K `{!LanguageCtx K} s E e Φ :
  WP K e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, WP K (of_val v) @ s; E {{ Φ }} }}.
Proof.
  iIntros "H". iLöb as "IH" forall (E e Φ). rewrite !wp_unfold /wp_pre /=.
  destruct (to_val e) as [v|] eqn:He.
  { apply of_to_val in He as <-. rewrite !wp_unfold /wp_pre. by iIntros "!>". }
  rewrite fill_not_val //.
  iIntros (σ1 ns κ κs nt) "Hσ". iMod ("H" with "[$]") as "[% H]".
  iModIntro; iSplit.
  { destruct s; eauto using reducible_fill_inv. }
  iIntros (e2 σ2 efs Hstep).
  iMod ("H" $! _ _ _ with "[]") as "H"; first eauto using fill_step.
  iIntros "!> !>". iMod "H". iModIntro. iApply (step_fupdN_wand with "H").
  iIntros "H". iMod "H" as "($ & H & $)". iModIntro. by iApply "IH".
Qed.

(** * Derived rules *)
Lemma wp_mono s E e Φ Ψ : (∀ v, Φ v ⊢ Ψ v) → WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ Ψ }}.
Proof.
  iIntros (HΦ) "H"; iApply (wp_strong_mono with "H"); auto.
  iIntros (v) "? !>". by iApply HΦ.
Qed.
Lemma wp_stuck_mono s1 s2 E e Φ :
  s1 ⊑ s2 → WP e @ s1; E {{ Φ }} ⊢ WP e @ s2; E {{ Φ }}.
Proof. iIntros (?) "H". iApply (wp_strong_mono with "H"); auto. Qed.
Lemma wp_stuck_weaken s E e Φ :
  WP e @ s; E {{ Φ }} ⊢ WP e @ E ?{{ Φ }}.
Proof. apply wp_stuck_mono. by destruct s. Qed.
Lemma wp_mask_mono s E1 E2 e Φ : E1 ⊆ E2 → WP e @ s; E1 {{ Φ }} ⊢ WP e @ s; E2 {{ Φ }}.
Proof. iIntros (?) "H"; iApply (wp_strong_mono with "H"); auto. Qed.
Global Instance wp_mono' s E e :
  Proper (pointwise_relation _ (⊢) ==> (⊢)) (wp s E e).
Proof. by intros Φ Φ' ?; apply wp_mono. Qed.
Global Instance wp_flip_mono' s E e :
  Proper (pointwise_relation _ (flip (⊢)) ==> (flip (⊢))) (wp s E e).
Proof. by intros Φ Φ' ?; apply wp_mono. Qed.

Lemma wp_value_fupd s E Φ e v : IntoVal e v → WP e @ s; E {{ Φ }} ⊣⊢ |={E}=> Φ v.
Proof. intros <-. by apply wp_value_fupd'. Qed.
Lemma wp_value' s E Φ v : Φ v ⊢ WP (of_val v) @ s; E {{ Φ }}.
Proof. rewrite wp_value_fupd'. auto. Qed.
Lemma wp_value s E Φ e v : IntoVal e v → Φ v ⊢ WP e @ s; E {{ Φ }}.
Proof. intros <-. apply wp_value'. Qed.

Lemma wp_frame_l s E e Φ R : R ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, R ∗ Φ v }}.
Proof. iIntros "[? H]". iApply (wp_strong_mono with "H"); auto with iFrame. Qed.
Lemma wp_frame_r s E e Φ R : WP e @ s; E {{ Φ }} ∗ R ⊢ WP e @ s; E {{ v, Φ v ∗ R }}.
Proof. iIntros "[H ?]". iApply (wp_strong_mono with "H"); auto with iFrame. Qed.

(** This lemma states that if we can prove that [n] laters are used in
   the current physical step, then one can perform an n-steps fancy
   update during that physical step. The resources needed to prove the
   bound on [n] are not used up: they can be reused in the proof of
   the WP or in the proof of the n-steps fancy update. In order to
   describe this unusual resource flow, we use ordinary conjunction as
   a premise. *)
Lemma wp_step_fupdN n s E1 E2 e P Φ :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (∀ σ ns κs nt, state_interp σ ns κs nt
       ={E1,∅}=∗ [| n ≤ S (num_laters_per_step ns) |]) ∧
  ((|={E1∖E2,∅}=> |={∅}▷=>^n |={∅,E1∖E2}=> P) ∗
    WP e @ s; E2 {{ v, P ={E1}=∗ Φ v }}) -∗
  WP e @ s; E1 {{ Φ }}.
Proof.
  iIntros (??) "H". iApply (wp_step_fupdN_strong with "[H]"); [done|].
  iApply (bi.and_mono_r with "H"). apply bi.sep_mono_l. iIntros "HP".
  iMod fupd_mask_subseteq_emptyset_difference as "H"; [|iMod "HP"]; [set_solver|].
  iMod "H" as "_". replace (E1 ∖ (E1 ∖ E2)) with E2; last first.
  { set_unfold=>x. destruct (decide (x ∈ E2)); naive_solver. }
  iModIntro. iApply (step_fupdN_wand with "HP"). iIntros "H".
  iApply fupd_mask_frame; [|iMod "H"; iModIntro]; [set_solver|].
  rewrite difference_empty_L (comm_L (∪)) -union_difference_L //.
  by iFrame.
Qed.
Lemma wp_step_fupd `{BiAffine PROP} s E1 E2 e P Φ :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (|={E1}[E2]▷=> P) -∗ WP e @ s; E2 {{ v, P ={E1}=∗ Φ v }} -∗ WP e @ s; E1 {{ Φ }}.
Proof.
  iIntros (??) "HR H".
  iApply (wp_step_fupdN_strong 1 _ E1 E2 with "[-]"); [done|..]. iSplit.
  - iIntros (????) "?". iMod (fupd_mask_subseteq ∅) as "?"; [set_solver+|].
    iIntros "!>".
    auto with lia.
  - iFrame "H". iMod "HR" as "$". auto.
Qed.

Section affine.
Context `{!BiAffine PROP}.
Set Default Proof Using "All".

Lemma wp_frame_step_l s E1 E2 e Φ R :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (|={E1}[E2]▷=> R) ∗ WP e @ s; E2 {{ Φ }} ⊢ WP e @ s; E1 {{ v, R ∗ Φ v }}.
Proof.
  iIntros (??) "[Hu Hwp]". iApply (wp_step_fupd with "Hu"); try done.
  iApply (wp_mono with "Hwp"). by iIntros (?) "$$".
Qed.
Lemma wp_frame_step_r s E1 E2 e Φ R :
  TCEq (to_val e) None → E2 ⊆ E1 →
  WP e @ s; E2 {{ Φ }} ∗ (|={E1}[E2]▷=> R) ⊢ WP e @ s; E1 {{ v, Φ v ∗ R }}.
Proof.
  rewrite [(WP _ @ _; _ {{ _ }} ∗ _)%I]comm; setoid_rewrite (comm _ _ R).
  apply wp_frame_step_l.
Qed.
Lemma wp_frame_step_l' s E e Φ R :
  TCEq (to_val e) None → ▷ R ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, R ∗ Φ v }}.
Proof. iIntros (?) "[??]". iApply (wp_frame_step_l s E E); try iFrame; eauto. Qed.
Lemma wp_frame_step_r' s E e Φ R :
  TCEq (to_val e) None → WP e @ s; E {{ Φ }} ∗ ▷ R ⊢ WP e @ s; E {{ v, Φ v ∗ R }}.
Proof. iIntros (?) "[??]". iApply (wp_frame_step_r s E E); try iFrame; eauto. Qed.

End affine.

Lemma wp_wand s E e Φ Ψ :
  WP e @ s; E {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ WP e @ s; E {{ Ψ }}.
Proof.
  iIntros "Hwp H". iApply (wp_strong_mono with "Hwp"); auto.
  iIntros (?) "? !>". by iApply "H".
Qed.
Lemma wp_wand_l s E e Φ Ψ :
  (∀ v, Φ v -∗ Ψ v) ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ Ψ }}.
Proof. iIntros "[H Hwp]". iApply (wp_wand with "Hwp H"). Qed.
Lemma wp_wand_r s E e Φ Ψ :
  WP e @ s; E {{ Φ }} ∗ (∀ v, Φ v -∗ Ψ v) ⊢ WP e @ s; E {{ Ψ }}.
Proof. iIntros "[Hwp H]". iApply (wp_wand with "Hwp H"). Qed.
Lemma wp_frame_wand s E e Φ R :
  R -∗ WP e @ s; E {{ v, R -∗ Φ v }} -∗ WP e @ s; E {{ Φ }}.
Proof.
  iIntros "HR HWP". iApply (wp_wand with "HWP").
  iIntros (v) "HΦ". by iApply "HΦ".
Qed.
End wp.

(** Proofmode class instances *)
Section proofmode_classes.
  Context {Λ} {PROP : bi} `{!BiFUpd PROP} `{!BiLaterContractive PROP}
          `{!irisGS_gen Λ PROP}.
  Implicit Types P Q : PROP.
  Implicit Types Φ : val Λ → PROP.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.

  Global Instance frame_wp p s E e R Φ Ψ :
    (∀ v, Frame p R (Φ v) (Ψ v)) →
    Frame p R (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Ψ }}) | 2.
  Proof. rewrite /Frame=> HR. rewrite wp_frame_l. apply wp_mono, HR. Qed.

  Global Instance is_except_0_wp s E e Φ : IsExcept0 (WP e @ s; E {{ Φ }}).
  Proof. by rewrite /IsExcept0 -{2}fupd_wp -except_0_fupd -fupd_intro. Qed.

  Global Instance elim_modal_bupd_wp `{!BiBUpd PROP} `{!BiBUpdFUpd PROP} p s E e P Φ :
    ElimModal True p false (|==> P) P (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal bi.intuitionistically_if_elim
      (bupd_fupd E) fupd_frame_r bi.wand_elim_r fupd_wp.
  Qed.

  Global Instance elim_modal_fupd_wp p s E e P Φ :
    ElimModal True p false (|={E}=> P) P (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal bi.intuitionistically_if_elim
      fupd_frame_r bi.wand_elim_r fupd_wp.
  Qed.

  Global Instance elim_modal_fupd_wp_atomic p s E1 E2 e P Φ :
    ElimModal (Atomic (stuckness_to_atomicity s) e) p false
            (|={E1,E2}=> P) P
            (WP e @ s; E1 {{ Φ }}) (WP e @ s; E2 {{ v, |={E2,E1}=> Φ v }})%I | 100.
  Proof.
    intros ?. by rewrite bi.intuitionistically_if_elim
      fupd_frame_r bi.wand_elim_r wp_atomic.
  Qed.

  Global Instance add_modal_fupd_wp s E e P Φ :
    AddModal (|={E}=> P) P (WP e @ s; E {{ Φ }}).
  Proof. by rewrite /AddModal fupd_frame_r bi.wand_elim_r fupd_wp. Qed.

  Global Instance elim_acc_wp_atomic {X} E1 E2 α β γ e s Φ :
    ElimAcc (X:=X) (Atomic (stuckness_to_atomicity s) e)
            (fupd E1 E2) (fupd E2 E1)
            α β γ (WP e @ s; E1 {{ Φ }})
            (λ x, WP e @ s; E2 {{ v, |={E2}=> β x ∗ (γ x -∗? Φ v) }})%I | 100.
  Proof.
    iIntros (?) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply (wp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.

  Global Instance elim_acc_wp_nonatomic {X} E α β γ e s Φ :
    ElimAcc (X:=X) True (fupd E E) (fupd E E)
            α β γ (WP e @ s; E {{ Φ }})
            (λ x, WP e @ s; E {{ v, |={E}=> β x ∗ (γ x -∗? Φ v) }})%I.
  Proof.
    iIntros (_) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply wp_fupd.
    iApply (wp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.
End proofmode_classes.
