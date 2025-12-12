(*
 * Copyright (c) 2023 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
*)

Require Export stdpp.propset.

Require Export elpi.apps.NES.NES.

Require Export bluerock.iris.extra.bi.prop_constraints.
Require Export bluerock.iris.extra.base_logic.lib.spectra.

Require Export bluerock.iris.extra.base_logic.lib.mono_list.

Require Export bluerock.iris.extra.bi.invariants.

Require Export bluerock.iris.extra.wp_io.iris.weakestpre.
Require Export bluerock.iris.extra.wp_io.inout_weakestpre.

Require Export bluerock.iris.extra.wp_io.lang.
Require Export iris.proofmode.tactics.

(**
General invariant encoding the refinement relation [trace_refine] that
we want to relate an abstract trace and a concrete trace.

TODO: generalize this from using [Compose.config].
*)
NES.Begin root.

Section trace.
  Context {absE conE : Type}.
  Context (R : absE -> conE -> Prop).
  Context {absLTS : LTS absE}.

  Context {PROP : bi} `{!Ghostly PROP}.
  Context `{!HasUsualOwn PROP (auth_setR absLTS.(lts_state))}.

  (** * The trace refinement assertion we want for some concrete trace.
  - [γ_abs] is the ghost name for the abstract machine LTS state [absLTS].
  - [tr_con] is the current concrete trace of the concrete machine.

  This assertion owns the authoritative state of the abstract machine,
  and says that there exists an abstract trace [tr_abs] reachable from the
  (abstract machine's) initial state that is related to [tr_con].
  *)
  Definition trace_refine γ_abs (tr_con : list (option conE)) : PROP :=
    ∃ (tr_abs : list (option absE)),
    (* abstract state and trace *)
    (∃ ss,
      AuthSet.auth γ_abs ss ∗
      [| ∃ s, s ∈ ss |] ∗
      ∃ s_init, [| absLTS.(Sts._init_state) s_init |] ∗
      [| ∀ s, s ∈ ss -> reachable absLTS s_init tr_abs s |]) ∗
      (* related *)
      [|  let vis_abs := filter is_Some tr_abs in
          let vis_con := filter is_Some tr_con in
          (* tau's filtered *)
          Forall2 (option_Forall2 R) vis_abs vis_con
      |].

  Lemma trace_refine_alloc s_init (INIT : absLTS.(Sts._init_state) s_init) :
    ⊢ |==> ∃ γ, AuthSet.frag γ {[s_init]} ∗ trace_refine γ [].
  Proof.
    rewrite /trace_refine.
    iMod (AuthSet.alloc {[s_init]}) as (γ) "[F A]".
    iIntros "!>".
    iExists γ. iFrame "F".
    iExists []. iSplitL; last done.
    iExists {[s_init]}. iFrame. iIntros "!%".
    repeat split.
    { set_solver. }
    exists s_init. split; [done|].
    intros ? ->%elem_of_singleton. constructor.
  Qed.

  (**
  [trace_refine] can be put into the state interpretation and linked directly
  to the current trace of the concrete machine, see [refine_embed_stateI] below.

  Alternatively, we can put [trace_refine] in a global invariant---see
  [ghost_trace_refine] and [ghost_trace_refine_inv] next, to make it more
  explicit to the verification. In that setup, we tie the concrete physical
  trace [tr_con] to the physical state through yet another piece of ghost state
  [mono_list.half γ_con tr_con].

  We put one half into the invariant ([ghost_trace_refine_inv]) and the other
  half into the state interpretation of the concrete machine to tie it to the
  concrete trace, see [refine_inv_stateI] below.

  *)
  Definition ghost_trace_refine
      `{!HasUsualOwn PROP (mono_list.traceR (option conE))}
      γ_con γ_abs : PROP :=
    ∃ tr_con, mono_list.half γ_con tr_con ∗
    trace_refine γ_abs tr_con.

  Definition ghost_trace_refine_inv
      `{!BiFUpd PROP} `{!HasUsualOwn PROP (mono_list.traceR (option conE))}
      γ_con γ_abs (N : namespace) : PROP :=
    inv N (ghost_trace_refine γ_con γ_abs).
End trace.

Section stateI.
  Context {PROP : bi} `{!BiFUpd PROP} `{!Ghostly PROP}.

  Context {cfg : Compose.config}.
  Let Λ := Compose.lts_lang cfg.

  Context `{ORG_irisGS : !irisGS_gen Λ PROP}.

  Section with_embed.
    Context {absE : Type}.
    Context (R : absE -> (Compose.event cfg) -> Prop).
    Context {absLTS : LTS absE}.

    Context `{!HasUsualOwn PROP (auth_setR absLTS.(lts_state))}.

    (** * Embedding the refinement relation directly into the [state_interp].

    We do so by simply extending some [state_interp] coming from the verifier
    in [ORG_irisGS] with [trace_refine].
    *)
    Definition refine_embed_stateI (γ_abs : AuthSet.gname)
        (σ : state Λ) (ns : nat) (κs : list (observation Λ)) (nt : nat) : PROP :=
      trace_refine R γ_abs σ.1.*1 ∗
      state_interp σ ns κs nt.

    Program Definition refine_embed_irisGS_gen (γ_abs : AuthSet.gname)
        : irisGS_gen Λ PROP :=
      IrisG (refine_embed_stateI γ_abs) fork_post num_laters_per_step _.
    Next Obligation.
      intros. iIntros "[$ SI]". iApply (state_interp_mono with "SI").
    Qed.

    Definition wp_embed `{!BiLaterContractive PROP}
        (γ_abs : AuthSet.gname) :=
      wp (Wp:=@iris.weakestpre.wp' _ _ _ _ (refine_embed_irisGS_gen γ_abs)).
  End with_embed.

  Section with_inv.
    Context `{!HasUsualOwn PROP (mono_list.traceR (option (Compose.event cfg)))}.

    (** * Relate the concrete trace [σ.1.*1] to [ghost_trace_refine_inv].

    We do so by simply extending some [state_interp] coming from the verifier
    in [ORG_irisGS] with a half [mono_list.half γ_con σ.1.*1].
    *)
    Definition refine_inv_stateI
        γ_con (σ : state Λ) (ns : nat) (κs : list (observation Λ)) (nt : nat) : PROP :=
      mono_list.half γ_con σ.1.*1 ∗
      state_interp σ ns κs nt.

    Program Definition refine_inv_irisGS_gen γ_con
        : irisGS_gen Λ PROP :=
      IrisG (refine_inv_stateI γ_con) fork_post num_laters_per_step _.
    Next Obligation.
      intros. iIntros "[$ SI]". iApply (state_interp_mono with "SI").
    Qed.

    Definition wp_inv `{!BiLaterContractive PROP} (γ_con : mono_list.gname) :=
      wp (Wp:=@iris.weakestpre.wp' _ _ _ _ (refine_inv_irisGS_gen γ_con)).
  End with_inv.
End stateI.

NES.End root.
