(*
 * Copyright (c) 2023 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(**
A variant of WP that has input assumptions / output obligations.
*)

Require Import iris.proofmode.base.
Require Import bluerock.iris.extra.proofmode.proofmode.
Require Import iris.proofmode.classes.
Require Export bluerock.iris.extra.bi.only_provable.
Require Export bluerock.iris.extra.wp_io.iris.ghost.

Record PrePost {PROP : bi} := {
  tele_pre  : tele ;
  tele_post : tele_pre -> tele ;
  pre       : tele_pre -> PROP ;
  post      : ∀ x, tele_post x -> PROP
}.
#[global] Arguments PrePost : clear implicits.

Definition trivial_spec {PROP} : PrePost PROP := {|
  tele_pre := [tele] ;
  tele_post _ := [tele] ;
  pre :=  λ _, emp%I ;
  post := λ _ _, emp%I ;
|}.

(** This property connects two specs in a callee-caller fashion :
- the caller picks [x_o] and show the caller spec's pre-cond [pre caller x_o];
- from the caller's pre-cond, we can produce the callee's pre-cond with [x_i];
- the callee picks [y_i] and return the callee spec's post-cond
  [post callee x_i y_i];
- we can produce the caller's post-cond with [y_o].
*)
Definition callee_caller_specs_pair {PROP}
    (callee caller : PrePost PROP) : Prop :=
  ∀ x_o : tele_pre caller,
    pre caller x_o ⊢
    ∃ x_i : tele_pre callee, pre callee x_i ∗
    (∀ y_i : tele_post callee x_i,
      post callee x_i y_i -∗ ∃ y_o : tele_post caller x_o, post caller x_o y_o).

(**
Beyond the standard WP, this packages additional input and output
relys and guarantees that the input-output WP must prove (and get to assume)
when it interacts with the environment.

TODO: this fixes the specs (obligations and assumptions) for input-output WP
up front. We’d want to generalize it to store the specs in ghost state.
Then we can allow changing the protocols on the fly, for example, we'd need to
enable/disable inputs at certain time (imagin enabling/disabling interrupts).
*)
Class inout_irisGS_gen (Λ : language) (PROP : bi) `{FUpd PROP} := InOutIrisG {
  ctx_irisGS_gen : irisGS_gen Λ PROP;
  (* spec for output *)
  ctx_out_spec (κ : list (observation Λ)) : PrePost PROP ;
  (* spec for input *)
  ctx_in_spec (κ : list (observation Λ)) : PrePost PROP ;
}.
#[global] Arguments InOutIrisG {Λ PROP _}.

#[local] Existing Instance ctx_irisGS_gen.

Definition wp_pre
    {Λ} {PROP : bi} `{!FUpd PROP} `{!inout_irisGS_gen Λ PROP}
    (s : stuckness)
    (wp : coPset -d> expr Λ -d> (val Λ -d> PROP) -d> PROP) :
    coPset -d> expr Λ -d> (val Λ -d> PROP) -d> PROP := λ E e1 Φ,
  match to_val e1 with
  | Some v => |={E}=> Φ v
  | None => ∀ σ1 ns κ κs nt,
      let α_in := (ctx_in_spec κ).(pre) in let β_in := (ctx_in_spec κ).(post) in
      let α_out := (ctx_out_spec κ).(pre) in let β_out := (ctx_out_spec κ).(post) in
      state_interp σ1 ns (κ ++ κs) nt
      ={E,∅}=∗
      ∀ x_in, α_in x_in -∗
        [| if s is NotStuck then reducible e1 σ1 else True |] ∗
        ∀ e2 σ2 efs, [| prim_step e1 σ1 κ e2 σ2 efs |] -∗
          ∃.. x_out, α_out x_out ∗
          (* £ (S (num_laters_per_step ns)) *)
          |={∅}▷=>^(S $ num_laters_per_step ns)
          ∀.. y_out, β_out x_out y_out
            ={∅,E}=∗
            ∃.. y_in, β_in x_in y_in ∗
            state_interp σ2 (S ns) κs (length efs + nt) ∗
            wp E e2 Φ ∗
            [∗ list] i ↦ ef ∈ efs, wp ⊤ ef fork_post
  end%I.

#[local] Instance wp_pre_contractive
  {Λ} {PROP : bi} `{!BiFUpd PROP} `{!BiLaterContractive PROP}
  `{!inout_irisGS_gen Λ PROP} s : Contractive (wp_pre s).
Proof.
  rewrite /wp_pre /= => n wp wp' Hwp E e1 Φ.
  do 30 (f_contractive || f_equiv).
  (* FIXME : simplify this proof once we have a good definition and a
     proper instance for step_fupdN. *)
  induction num_laters_per_step as [|k IH]; simpl.
  - f_equiv. repeat (f_contractive || f_equiv); apply Hwp.
  - by rewrite -IH.
Qed.

#[local] Definition wp_def
  {Λ} {PROP : bi} `{!BiFUpd PROP} `{!BiLaterContractive PROP}
  `{!inout_irisGS_gen Λ PROP} :
  Wp PROP (expr Λ) (val Λ) stuckness :=
  λ s : stuckness, fixpoint (wp_pre s).
#[local] Definition wp_aux : seal (@wp_def). Proof. by eexists. Qed.
Definition wp' := wp_aux.(unseal).
Global Arguments wp' {Λ PROP _ _ _}.
Global Existing Instance wp'.
#[local] Lemma wp_unseal
  {Λ} {PROP : bi} `{!BiFUpd PROP} `{!BiLaterContractive PROP}
  `{!inout_irisGS_gen Λ PROP} : wp = @wp_def Λ PROP _ _ _.
Proof. rewrite -wp_aux.(seal_eq) //. Qed.

Section wp.
Context {Λ} {PROP : bi} `{!BiFUpd PROP} `{!BiLaterContractive PROP}
        `{!inout_irisGS_gen Λ PROP}.
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
  do 30 (f_contractive || f_equiv).
  (* FIXME : simplify this proof once we have a good definition and a
     proper instance for step_fupdN. *)
  induction num_laters_per_step as [|k IHk]; simpl; last by rewrite IHk.
  do 6 f_equiv.
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
  do 29 (f_contractive || f_equiv).
  (* FIXME : simplify this proof once we have a good definition and a
     proper instance for step_fupdN. *)
  induction num_laters_per_step as [|k IHk]; simpl; last by rewrite IHk.
  by do 10 f_equiv.
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
  iMod ("H" with "Hσ") as "H".
  iIntros "!>" (x_i) "Hαi".
  iDestruct ("H" with "Hαi") as "[% H]".
  iSplit; [by destruct s1, s2|].
  iIntros (e2 σ2 efs) "Step".
  iDestruct ("H" with "Step") as (x_o) "(Hαo & H)". iExists x_o. iFrame "Hαo".
  iMod "H". iIntros "!> !>". iMod "H". iModIntro.
  iApply (step_fupdN_wand with "[H]"); first by iApply "H".
  iIntros "H" (y_o) "Hβ". iMod ("H" with "Hβ") as (y_i) "(Hβi & $ & H & Hefs)".
  iMod "Hclose" as "_". iModIntro.
  iExists y_i. iFrame "Hβi". iSplitR "Hefs".
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


Lemma wp_atomic s E1 E2 e Φ
  (* only support strongly atomic *) (* `{!Atomic s e} *)
  `{!Atomic StronglyAtomic e} :
  (|={E1,E2}=> WP e @ s; E2 {{ v, |={E2,E1}=> Φ v }}) ⊢ WP e @ s; E1 {{ Φ }}.
Proof.
  iIntros "H". rewrite !wp_unfold /wp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { by iDestruct "H" as ">>> $". }
  iIntros (σ1 ns κ κs nt) "Hσ". iMod "H".
  iMod ("H" $! σ1 with "Hσ") as "H".
  iIntros "!>" (x_i) "Hαi". iDestruct ("H" with "Hαi") as "[$ H]".
  iIntros (e2 σ2 efs Hstep).
  iDestruct ("H" with "[%//]") as (x_o) "(Hαo & H)". iExists x_o. iFrame "Hαo".
  iApply (step_fupdN_wand with "H").
  iIntros "H" (y_o) "Hβo". iMod ("H" with "Hβo") as (y_i) "(Hβi & Hσ & H & Hefs)".
  iExists y_i. iFrame "Hβi".
  (*
  destruct s.
  - rewrite !wp_unfold /wp_pre. destruct (to_val e2) as [v2|] eqn:He2.
    + iDestruct "H" as ">> $". by iFrame.
    + iMod ("H" $! _ _ [] with "[$]") as "[H ?]". iDestruct "H" as %(? & ? & ? & ? & ?).
      by edestruct (atomic _ _ _ _ _ Hstep).
  - *)
    destruct (atomic _ _ _ _ _ Hstep) as [v <-%of_to_val].
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
  iDestruct "H" as "[_ [>HP Hwp]]".
  iMod ("Hwp" with "Hσ") as "H".
  iIntros "!>" (x_i) "Hαi".
  iDestruct ("H" with "Hαi") as "[$ H]".
  iIntros (e2 σ2 efs Hstep).
  iDestruct ("H" $! e2 σ2 efs with "[% //]") as (x_o) "[Hαo H]".
  iExists x_o. iFrame "Hαo".
  iMod "HP". iMod "H". iIntros "!>!>". iMod "H". iMod "HP". iModIntro.
  revert n Hn. generalize (num_laters_per_step ns)=>n0 n Hn.
  iInduction n as [|n] "IH" forall (n0 Hn).
  - iApply (step_fupdN_wand with "H"). iIntros "H" (y_o) "Hβo".
    iMod ("H" with "Hβo") as (y_i) "(Hβi & $ & Hwp & $)". iMod "HP".
    iExists y_i. iFrame "Hβi".
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
  iIntros (σ1 step κ κs n) "Hσ". iMod ("H" with "Hσ") as "H".
  iIntros "!>" (x_i) "Hαi". iDestruct ("H" with "Hαi") as "[% H]".
  iSplit.
  { destruct s; eauto using reducible_fill. }
  iIntros (e2 σ2 efs Hstep).
  destruct (fill_step_inv e σ1 κ e2 σ2 efs) as (e2'&->&?); auto.
  iDestruct ("H" $! e2' σ2 efs with "[//]") as (x_o) "[Hαo H]".
  iExists x_o. iFrame "Hαo".
  iMod "H". iIntros "!>!>".
  iMod "H". iModIntro. iApply (step_fupdN_wand with "H"). iIntros "H" (y_o) "Hβo".
  iMod ("H" with "Hβo") as (y_i) "(Hβi & $ & H & $)". iModIntro.
  iExists y_i. iFrame "Hβi". by iApply "IH".
Qed.

Lemma wp_bind_inv K `{!LanguageCtx K} s E e Φ :
  WP K e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, WP K (of_val v) @ s; E {{ Φ }} }}.
Proof.
  iIntros "H". iLöb as "IH" forall (E e Φ). rewrite !wp_unfold /wp_pre /=.
  destruct (to_val e) as [v|] eqn:He.
  { apply of_to_val in He as <-. rewrite !wp_unfold /wp_pre. by iIntros "!>". }
  rewrite fill_not_val //.
  iIntros (σ1 ns κ κs nt) "Hσ". iMod ("H" with "Hσ") as "H".
  iIntros "!>" (x_i) "Hαi". iDestruct ("H" with "Hαi") as "[% H]".
  iSplit.
  { destruct s; eauto using reducible_fill_inv. }
  iIntros (e2 σ2 efs Hstep).
  iDestruct ("H" $! _ _ _ with "[%]") as (x_o) "[Hαo H]"; first eauto using fill_step.
  iExists x_o. iFrame "Hαo".
  iMod "H". iIntros "!> !>". iMod "H". iModIntro. iApply (step_fupdN_wand with "H").
  iIntros "H" (y_o) "Hβo". iMod ("H" with "Hβo") as (y_i) "(Hβi & $ & H & $)".
  iModIntro.
  iExists y_i. iFrame "Hβi". by iApply "IH".
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

Section wp_io_mono.
Context {Λ : language} {PROP : bi} `{!BiFUpd PROP} `{!BiLaterContractive PROP}
        `{!irisGS_gen Λ PROP}.

Context (in1 out1 in2 out2 : list (observation Λ) → PrePost PROP).

Lemma wp_io_mono (s : stuckness) E (e : expr Λ) (Φ : val Λ -> PROP) :
  let ioGS1 := InOutIrisG _ out1 in1 in
  let ioGS2 := InOutIrisG _ out2 in2 in
  wp (Wp:=@wp' _ _ _ _ ioGS1) s E e Φ ⊢
  □ (∀ κ x_i2,
      pre (in2 κ) x_i2 -∗ ∃ x_i1, pre (in1 κ) x_i1 ∗
      ∀ e1 σ1 e2 σ2 efs x_o1,
        [| prim_step (l:=Λ) e1 σ1 κ e2 σ2 efs |] -∗
        pre (out1 κ) x_o1 -∗ ∃ x_o2, pre (out2 κ) x_o2 ∗
          ∀ y_o2, post (out2 κ) x_o2 y_o2 -∗ ∃ y_o1, post (out1 κ) x_o1 y_o1 ∗
            ∀ y_i1, post (in1 κ) x_i1 y_i1 -∗ ∃ y_i2, post (in2 κ) x_i2 y_i2) -∗
  wp (Wp:=@wp' _ _ _ _ ioGS2) s E e Φ.
Proof.
  iIntros (ioGS1 ioGS2) "WP #MONO".
  iLöb as "IH" forall (e Φ E).
  rewrite 2!wp_unfold /wp_pre. case_match; [done|].
  iIntros (σ1 ns κ κs nt) "SI".
  iMod ("WP" with "SI") as "WP".
  iIntros "!>" (x_i2) "Hαi2".
  iDestruct ("MONO" with "Hαi2") as (x_i1) "[Hαi1 MP]".
  iDestruct ("WP" with "Hαi1") as (RED) "WP".
  iSplitR; [done|].
  iIntros (e2 σ2 efs STEP).
  iDestruct ("WP" with "[%//]") as (x_o1) "(Hαo1 & WP)".
  iDestruct ("MP" with "[%//] Hαo1") as (x_o2) "[Hαo2 MP]".
  iExists x_o2. iFrame "Hαo2".
  iMod "WP". iIntros "!> !>". iMod "WP". iIntros "!>".
  iApply (step_fupdN_wand with "WP"). iIntros "WP".
  iIntros (y_o2) "Hβo2".
  iDestruct ("MP" with "Hβo2") as (y_o1) "[Hβo1 MP]".
  iMod ("WP" with "Hβo1") as (y_i1) "(Hβi1 & $ & WP & WPs)".
  iIntros "!>".
  iDestruct ("MP" with "Hβi1") as (y_i2) "Hβi2".
  iExists y_i2. iFrame "Hβi2". iSplitL "WP".
  - iApply ("IH" with "WP").
  - iApply (big_sepL_impl with "WPs").
    iIntros "!#" (???). iApply "IH".
Qed.
End wp_io_mono.

(** Proofmode class instances *)
Section proofmode_classes.
  Context {Λ} {PROP : bi} `{!BiFUpd PROP} `{!BiLaterContractive PROP}
          `{!inout_irisGS_gen Λ PROP}.
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

  (* only support strongly atomic *)
  Global Instance elim_modal_fupd_wp_atomic p s E1 E2 e P Φ :
    ElimModal (Atomic StronglyAtomic e) p false
            (|={E1,E2}=> P) P
            (WP e @ s; E1 {{ Φ }}) (WP e @ s; E2 {{ v, |={E2,E1}=> Φ v }})%I | 100.
  Proof.
    intros ?. by rewrite bi.intuitionistically_if_elim
      fupd_frame_r bi.wand_elim_r wp_atomic.
  Qed.

  Global Instance add_modal_fupd_wp s E e P Φ :
    AddModal (|={E}=> P) P (WP e @ s; E {{ Φ }}).
  Proof. by rewrite /AddModal fupd_frame_r bi.wand_elim_r fupd_wp. Qed.

  (* only support strongly atomic *)
  Global Instance elim_acc_wp_atomic {X} E1 E2 α β γ e s Φ :
    ElimAcc (X:=X) (Atomic StronglyAtomic e)
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


Require bluerock.iris.extra.wp_io.iris.weakestpre.

Section wp_io_elim.
Context {Λ : language} {PROP : bi} `{!BiFUpd PROP} `{!BiLaterContractive PROP}
        `{!irisGS_gen Λ PROP}.

Context (in_spec out_spec : list (observation Λ) → PrePost PROP).

Lemma wp_io_elim (s : stuckness) E (e : expr Λ) (Φ : val Λ -> PROP) :
  let ioGS := InOutIrisG _ out_spec in_spec in
  wp (Wp:=wp') s E e Φ ⊢
  □ (∀ κ, ∃ x_i, pre (in_spec κ) x_i ∗
      ∀ e1 σ1 e2 σ2 efs x_o,
        [| prim_step (l:=Λ) e1 σ1 κ e2 σ2 efs |] -∗
        pre (out_spec κ) x_o -∗ ∃ y_o, post (out_spec κ) x_o y_o ∗
          ∀ y_i, post (in_spec κ) x_i y_i -∗ emp) -∗
  wp (Wp:=iris.weakestpre.wp') s E e Φ.
Proof.
  iIntros (ioGS) "WP #ELIM".
  iLöb as "IH" forall (e Φ E).
  rewrite wp_unfold /wp_pre iris.weakestpre.wp_unfold /iris.weakestpre.wp_pre.
  case_match; [done|].
  iIntros (σ1 ns κ κs nt) "SI".
  iMod ("WP" with "SI") as "WP".
  iDestruct ("ELIM" $! κ) as (x_i) "-#[Hαi EL]".
  iDestruct ("WP" with "Hαi") as (RED) "WP".
  iIntros "!>".
  iSplitR; [done|].
  iIntros (e2 σ2 efs STEP).
  iDestruct ("WP" with "[%//]") as (x_o) "(Hαo & WP)".
  iDestruct ("EL" with "[%//] Hαo") as (y_o) "[Hβo EL]".
  iMod "WP". iIntros "!> !>". iMod "WP". iIntros "!>".
  iApply (step_fupdN_wand with "WP"). iIntros "WP".
  iMod ("WP" with "Hβo") as (y_i) "(Hβi & $ & WP & WPs)".
  iDestruct ("EL" with "Hβi") as "_".
  iIntros "!>". iSplitL "WP".
  - iApply ("IH" with "WP").
  - iApply (big_sepL_impl with "WPs").
    iIntros "!#" (???). iApply "IH".
Qed.
End wp_io_elim.
