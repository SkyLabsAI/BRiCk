(*
 * Copyright (c) 2023 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(** * Extracting refinement relation between traces from Iris adequacy.

We also have two variants, one for embedded refinement relation and one for
an refinement invariant.
- [refine_embed.trace_refinement_adequacy] extracts the refinement from the instrumented
  state interpretation.
- [refine_inv.trace_refinement_adequacy] extracts the refinement from the root invariant
  [wp_iris.refine_inv.root_inv].

Both lemmas apply Iris adequacy [wp_strong_adequacy_gen].
*)

Require Import bluerock.iris.extra.wp_io.iris.adequacy.
Require Import bluerock.iris.extra.wp_io.refinement.inv.

Require Import bluerock.iris.extra.base_logic.iprop_prop.

Module refine_embed.

Section with_lang.
  Context {cfg : Compose.config}.
  Let Λ := Compose.lts_lang cfg.

  Context {absE : Type}.
  Context (R : absE -> (Compose.event cfg) -> Prop).
  Context {absLTS : LTS absE}.

  (**
  If the client can prove
  [AuthSet.frag γ_abs {[s_init]} -∗ root.wp_embed R γ_abs MaybeStuck ⊤ e Φ]
  that is, a WPio for the concrete configuration [e] assuming the abstract
  machine state [s_init], then we can extract a trace refinement.

  The client picks the initial abstract state [s_init].
  We also require that the initial configuration has empty past trace, that is
  [σ1.1.*1 = []].

  TODOs:
  - we can generalize this for the client to pick [s_init] much earlier
  - we can generalize the initial configuration to arbitrary state and
    past trace, we only need to remember those initial state and trace.
  *)
  Theorem trace_refinement_adequacy
      Σ `{!invGpreS Σ}
      `{!AuthSet.G Σ (lts_state absLTS)} (* for abstract state *)
      e (σ1 : state Λ) n κs t2 σ2 (num_laters_per_step : nat → nat)
      (INIT_EMPTY : σ1.1.*1 = []) :
    (* WP of e *)
    (∀ `{Hinv : !invGS_gen HasNoLc Σ},
      ⊢ |={⊤}=>
          ∃ s_init, [| absLTS.(Sts._init_state) s_init |] ∗
          ∀ γ_abs, AuthSet.frag γ_abs {[s_init]} -∗
          ∃ (stateI : state Λ → nat → list (observation Λ) → nat → iProp Σ)
            (Φ : val Λ → iProp Σ)
            (fork_post : val Λ → iProp Σ)
            state_interp_mono,
          let _ : irisGS_gen Λ (iPropI Σ) :=
            IrisG stateI fork_post num_laters_per_step state_interp_mono in
          stateI σ1 0 κs 0 ∗
          root.wp_embed R γ_abs MaybeStuck top e Φ) →
    language.nsteps (Λ:=Λ) n ([e], σ1) κs (t2, σ2) →
    ∃ s_init s tr_abs,
      absLTS.(Sts._init_state) s_init ∧
      reachable absLTS s_init tr_abs s ∧
      let vis_abs := filter is_Some tr_abs in
      let vis_con := filter is_Some κs.*1 in
      (* tau's filtered *)
      Forall2 (option_Forall2 R) vis_abs vis_con.
  Proof.
    intros Hwp STEPS.
    (* Iris general adequacy *)
    apply : (wp_strong_adequacy_gen _ _ MaybeStuck _ _ _ _ _ _ _ num_laters_per_step);
      last exact STEPS.
    iIntros (Hinv).
    (* extracting user's WP proof *)
    iMod (Hwp Hinv) as (s_init INIT) "WP".
    (* setting up ghost state for refinement *)
    iMod (root.trace_refine_alloc R s_init INIT) as (γ_abs) "[F RT]".
    iDestruct ("WP" with "F") as (stateI Φ fork_post ?) "[SI WP]".
    iIntros "!>".
    iExists (root.refine_embed_stateI R γ_abs), [Φ], _, _.
    iFrame "WP".
    rewrite /root.refine_embed_stateI INIT_EMPTY. iFrame "RT SI".
    iSplitR; [done|].
    (* extracting refinement relation from [state_interp] *)
    iIntros (es' ts' Eqt2 EqLes' ?).
    iIntros "(RF & SI) ? ?".
    iApply fupd_mask_intro; [solve_ndisj|]. iIntros "Close'".
    iDestruct "RF" as (tr_abs) "(absA & %RF)".
    iDestruct "absA" as (ss) "(? & %FACT)".
    iIntros "!%".
    destruct FACT as ([s Inss] & s_init' & INIT' & REACH).
    exists s_init', s, tr_abs.
    specialize (REACH _ Inss). repeat split; [done..|].
    (**
    Here we needs σ2.1.*1 = κs.*1.
    Fortunately, [Compose.lts_lang] satisfies this property.
    When generalizing the language, we need to remember this requirement.
    *)
    apply Compose.nsteps_trace_final in STEPS.
    rewrite INIT_EMPTY app_nil_l in STEPS.
    by rewrite -STEPS.
  Qed.
End with_lang.
End refine_embed.

Module refine_inv.

Section with_lang.
  Context {cfg : Compose.config}.
  Let Λ := Compose.lts_lang cfg.

  Context {absE : Type}.
  Context (R : absE -> (Compose.event cfg) -> Prop).
  Context {absLTS : LTS absE}.

  #[local] Lemma ghost_trace_refine_inv_alloc {Σ} `{!invGS_gen hlc Σ}
      `{!AuthSet.G Σ (lts_state absLTS)}             (* for abstract state *)
      `{!mono_list.G Σ (option (Compose.event cfg))} (* for concrete trace *)
      N E
      s_init (INIT : absLTS.(Sts._init_state) s_init) :
    ⊢@{iPropI Σ}
      |={E}=> ∃ γ_con γ_abs, root.ghost_trace_refine_inv R γ_con γ_abs N ∗
        AuthSet.frag γ_abs {[s_init]} ∗
        mono_list.half γ_con [].
  Proof.
    iMod (mono_list.half_alloc []) as (γ_con) "[h1 h2]".
    iMod (root.trace_refine_alloc R s_init INIT) as (γ_abs) "[F RT]".
    iExists γ_con, γ_abs. iFrame.

    (* TODO cleanup : inlining [bluerock.iris.extra.base_logic.iprop_invariants]
      because that one is fixed to the default [invGS_gen HasLc] *)
    iMod (own_inv_alloc N E (root.ghost_trace_refine R γ_con γ_abs) with "[-]") as "#INV".
    { iNext. iExists []. by iFrame. }
    rewrite /root.ghost_trace_refine_inv inv_eq.
    iIntros "!>" (E' SubE') "!#".
    by iMod (own_inv_acc with "[$]").
  Qed.

  (**
  If the client can prove
  [AuthSet.frag γ_abs {[s_init]} -∗ root.wp_embed R γ_abs MaybeStuck ⊤ e Φ]
  that is, a WPio for the concrete configuration [e] assuming the abstract
  machine state [s_init], then we can extract a trace refinement.

  The client picks the initial abstract state [s_init].
  We also require that the initial configuration has empty past trace, that is
  [σ1.1.*1 = []].

  TODOs:
  - we can generalize this for the client to pick [s_init] much earlier
  - we can generalize the initial configuration to arbitrary state and
    past trace, we only need to remember those initial state and trace.
  *)
  Theorem trace_refinement_adequacy
      Σ `{!invGpreS Σ}
      `{!AuthSet.G Σ (lts_state absLTS)}             (* for abstract state *)
      `{!mono_list.G Σ (option (Compose.event cfg))} (* for concrete trace *)
      (N : namespace)  (* namespace for refinement invariant *)
      e (σ1 : state Λ) n κs t2 σ2 (num_laters_per_step : nat → nat)
      (INIT_EMPTY : σ1.1.*1 = []) :
    (* WP of e *)
    (∀ `{Hinv : !invGS_gen HasNoLc Σ},
      ⊢ |={⊤}=>
          ∃ s_init, [| absLTS.(Sts._init_state) s_init |] ∗
          ∀ γ_abs γ_con,
          root.ghost_trace_refine_inv R γ_con γ_abs N -∗
          AuthSet.frag γ_abs {[s_init]} -∗
          ∃ (stateI : state Λ → nat → list (observation Λ) → nat → iProp Σ)
            (Φ : val Λ → iProp Σ)
            (fork_post : val Λ → iProp Σ)
            state_interp_mono,
          let _ : irisGS_gen Λ (iPropI Σ) :=
            IrisG stateI fork_post num_laters_per_step state_interp_mono in
          stateI σ1 0 κs 0 ∗
          root.wp_inv γ_con MaybeStuck top e Φ) →
    language.nsteps (Λ:=Λ) n ([e], σ1) κs (t2, σ2) →
    ∃ s_init s tr_abs,
      absLTS.(Sts._init_state) s_init ∧
      reachable absLTS s_init tr_abs s ∧
      let vis_abs := filter is_Some tr_abs in
      let vis_con := filter is_Some κs.*1 in
      (* tau's filtered *)
      Forall2 (option_Forall2 R) vis_abs vis_con.
  Proof.
    intros Hwp STEPS.
    (* Iris general adequacy *)
    apply : (wp_strong_adequacy_gen _ _ MaybeStuck _ _ _ _ _ _ _ num_laters_per_step);
      last exact STEPS.
    iIntros (Hinv).
    (* extracting user's WP proof *)
    iMod (Hwp Hinv) as (s_init INIT) "WP".
    (* setting up ghost state for refinement *)
    iMod (ghost_trace_refine_inv_alloc N _ s_init INIT)
      as (γ_con γ_abs) "(#INV & F & H)".
    iDestruct ("WP" with "INV F") as (stateI Φ fork_post ?) "[SI WP]".
    iIntros "!>".
    iExists (root.refine_inv_stateI γ_con), [Φ], _, _.
    iFrame "WP".
    rewrite /root.refine_inv_stateI INIT_EMPTY. iFrame "H SI".
    iSplitR; [done|].
    (* extracting refinement relation from [state_interp] *)
    iIntros (es' ts' Eqt2 EqLes' ?).
    iIntros "(H & SI) ? ?".
    iInv "INV"  as (tr_con) ">[H' RF]" "CloseI".
    iApply fupd_mask_intro; [solve_ndisj|]. iIntros "Close'".
    iDestruct (mono_list.half_agree with "H' H") as %->.
    iDestruct "RF" as (tr_abs) "(absA & %RF)".
    iDestruct "absA" as (ss) "(? & %FACT)".
    iIntros "!%".
    destruct FACT as ([s Inss] & s_init' & INIT' & REACH).
    exists s_init', s, tr_abs.
    specialize (REACH _ Inss). repeat split; [done..|].
    (**
    Here we needs σ2.1.*1 = κs.*1.
    Fortunately, [Compose.lts_lang] satisfies this property.
    When generalizing the language, we need to remember this requirement.
    *)
    apply Compose.nsteps_trace_final in STEPS.
    rewrite INIT_EMPTY app_nil_l in STEPS.
    by rewrite -STEPS.
  Qed.
End with_lang.
End refine_inv.
