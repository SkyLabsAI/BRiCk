(*
 * Copyright (c) 2023 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(** * General decomposition of a WPio for the Compose language into WPio's of
its components.

The main theorem is [wp_io_decompose].
*)
Require Export stdpp.namespaces.
Require Import bluerock.prelude.list.

Require Export bluerock.iris.extra.bi.spec.exclusive.
Require Export bluerock.iris.extra.bi.spec.frac_splittable.
Require Export bluerock.iris.extra.bi.spec.knowledge.
Require Export bluerock.iris.extra.bi.spec.nary_classes.
Require Import bluerock.iris.extra.bi.prop_constraints.
Require Import bluerock.iris.extra.bi.big_op.

Require Export bluerock.iris.extra.wp_io.inout_weakestpre.
Require Export bluerock.iris.extra.wp_io.lang.

Require Import bluerock.iris.extra.bi.observe.
Require Import bluerock.iris.extra.bi.only_provable.
Require Import bluerock.iris.extra.bi.own.

Require Export iris.proofmode.tactics.

Module wp_compose.
Section with_config.
  Context {cfg : Compose.config}.

  Let Λ := Compose.lts_lang cfg.
  Let NAMES : gset cfg.(Compose.name) := list_to_set (enum cfg.(Compose.name)).

  Notation traceR := (agreeR (leibnizO (list (observation Λ)))).

  Definition composeΣ : gFunctors := #[ GFunctor traceR ].

  Class preG Σ := mkPreG {
    traceG  : inG Σ traceR ;
  }.
  #[global] Instance subG_preG {Σ} : subG composeΣ Σ → preG Σ.
  Proof. solve_inG. Qed.

  Class gen_preG (PROP : bi) `{!Ghostly PROP} := mkGenPreG {
    gen_traceG  : HasUsualOwn PROP traceR ;
  }.

  Class G (PROP : bi) `{!Ghostly PROP} := mkG {
    gen_preG_G  : gen_preG PROP ;
    futrace_name : iprop.gname;
  }.

  Import Compose.

  Notation Λc n := (Component.lts_lang (cfg.(components) n)).

  Class ComponentG (PROP : bi) `{FUpd PROP}
      := mkComponentG {
    componentG : ∀ n : cfg.(name), inout_irisGS_gen (Λc n) PROP
  }.
  #[local] Existing Instances componentG.

  Section with_agree.
    Context {PROP} `{!Ghostly PROP}.
    Context `{composeG : !G PROP}.

    #[local] Existing Instances gen_preG_G gen_traceG.

    Definition full_trace (tr : list (observation Λ)) : PROP :=
      own futrace_name (to_agree (tr : leibnizO _)).

    #[global] Instance full_trace_persistent : Persistent1 full_trace := _.
    #[global] Instance full_trace_timeless : Timeless1 full_trace := _.
    #[global] Instance full_trace_agree : Agree1 full_trace.
    Proof.
      iIntros (??) "A1 A2".
      iDestruct (own_valid_2 with "A1 A2") as %?%to_agree_op_valid_L.
      by iIntros "!# !%".
    Qed.
  End with_agree.
  Lemma full_trace_alloc {PROP} `{!Ghostly PROP} `{!gen_preG PROP}
      (tr : list (observation Λ)) :
    ⊢ |==> ∃ (_ : G PROP), full_trace tr.
  Proof.
    set HO := gen_traceG.
    iMod (own_alloc (to_agree (tr : leibnizO _))) as (γ) "FT". { done. }
    iIntros "!>". iExists (mkG _ _ _ γ). iFrame "FT".
  Qed.

  Section with_wps.
    Context {PROP : bi} `{!BiFUpd PROP} `{!Ghostly PROP}.
    Context `{!BiLaterContractive PROP}.
    Context `{composeG : !G PROP}.
    Context `{allGs : !ComponentG PROP}.

    Definition stateI
        (σ : state Λ) (ns : nat) (tr_f : list (observation Λ)) (nt : nat)
        : PROP :=
      let '(tr_p, s) := σ in
      (* tracking composed history trace *)
      full_trace (tr_p ++ tr_f) ∗
      (* ownership of each component's [state_interp] *)
      [∗ set] n ∈ NAMES,
        ∃ ns_n nt_n, (* TODO : we may want to tie ns_n/nt_n to ns/nt *)
          let s_n     := (fin_prod.lookup s n) in
          let tr_p_n  := proj_trace tr_p n in
          let tr_f_n  := proj_trace tr_f n in
          let _ := ctx_irisGS_gen (Λ := Λc n) in
          state_interp (tr_p_n, s_n) ns_n tr_f_n nt_n
        .

    Definition compose_irisGS_gen : irisGS_gen Λ PROP :=
      IrisG stateI (λ _, False%I) (λ _, 1) (λ _ _ _ _, fupd_intro _ _).

    Definition input_spec (κ : list (observation Λ)) : PrePost PROP := {|
      tele_pre :=
        match κ with
        | [(Some e, Forward n e_n)] => tele_pre (ctx_in_spec [Some e_n])
        | [(None, Tau n)] => tele_pre (ctx_in_spec (Λ:=Λc n) [None])
        | [(None, Sync n1 n2 e1 e2)] => tele_pre (ctx_in_spec (Λ:=Λc n2) [Some e2])
        | _ => [tele]
        end ;
      tele_post :=
        match κ with
        | [(Some e, Forward n e_n)] => tele_post (ctx_in_spec [Some e_n])
        | [(None, Tau n)] => tele_post (ctx_in_spec (Λ:=Λc n) [None])
        | [(None, Sync n1 n2 e1 e2)] => tele_post (ctx_in_spec (Λ:=Λc n2) [Some e2])
        | _ => λ _, [tele]
        end ;
      pre :=
        match κ with
        | [(Some e, Forward n e_n)] =>
            (λ args, [| inj_evt n e_n = Some e |] -∗ pre (ctx_in_spec [Some e_n]) args)%I
        | [(None, Tau n)] => pre (ctx_in_spec (Λ:=Λc n) [None])
        | [(None, Sync n1 n2 e1 e2)] =>
            (λ args, [| cancel_event_asym n1 n2 e1 e2 |] -∗ pre (ctx_in_spec (Λ:=Λc n2) [Some e2]) args)%I
        | _ => λ _, emp%I
        end ;
      post :=
        match κ with
        | [(Some e, Forward n e_n)] => post (ctx_in_spec [Some e_n])
        | [(None, Tau n)] => post (ctx_in_spec (Λ:=Λc n) [None])
        | [(None, Sync n1 n2 e1 e2)] => post (ctx_in_spec (Λ:=Λc n2) [Some e2])
        | _ => λ _ _, emp%I
        end ;
    |}.

    Definition output_spec (κ : list (observation Λ)) : PrePost PROP := {|
      tele_pre :=
        match κ with
        | [(Some e, Forward n e_n)] => tele_pre (ctx_out_spec [Some e_n])
        | [(None, Tau n)] => tele_pre (ctx_out_spec (Λ:=Λc n) [None])
        | [(None, Sync n1 n2 e1 e2)] => tele_pre (ctx_out_spec (Λ:=Λc n1) [Some e1])
        | _ => [tele]
        end ;
      tele_post :=
        match κ with
        | [(Some e, Forward n e_n)] => tele_post (ctx_out_spec [Some e_n])
        | [(None, Tau n)] => tele_post (ctx_out_spec (Λ:=Λc n) [None])
        | [(None, Sync n1 n2 e1 e2)] => tele_post (ctx_out_spec (Λ:=Λc n1) [Some e1])
        | _ => λ _, [tele]
        end ;
      pre :=
        match κ with
        | [(Some e, Forward n e_n)] =>
            (λ args, [| inj_evt n e_n = Some e |] ∗ pre (ctx_out_spec [Some e_n]) args)%I
        | [(None, Tau n)] => pre (ctx_out_spec (Λ:=Λc n) [None])
        | [(None, Sync n1 n2 e1 e2)] =>
            (λ args, [| cancel_event_asym n1 n2 e1 e2 |] ∗ pre (ctx_out_spec (Λ:=Λc n1) [Some e1]) args)%I
        | _ => λ _, emp%I
        end ;
      post :=
        match κ with
        | [(Some e, Forward n e_n)] => post (ctx_out_spec [Some e_n])
        | [(None, Tau n)] => post (ctx_out_spec (Λ:=Λc n) [None])
        | [(None, Sync n1 n2 e1 e2)] => post (ctx_out_spec (Λ:=Λc n1) [Some e1])
        | _ => λ _ _, emp%I
        end ;
    |}.

    #[local] Instance compose_inout_irisGS_gen
      : inout_irisGS_gen Λ PROP := {|
        ctx_irisGS_gen  := compose_irisGS_gen ;
        ctx_out_spec    := output_spec ;
        ctx_in_spec     := input_spec ;
    |}.

    Class LogicComposeProp := mkLogComProp {
      (** This forces the components to have no extra later, so each component
      will have exactly ONE later per step. Meanwhile, we have set up the
      compose logic to have ONE EXTRA later per step.
      Therefore, when in a communication step, we have exactly TWO laters from
      the compose logic and give ONE to each component. In non-communication
      steps, we only need ONE later, so we simply throw away the other one.

      A general setup may require that the compose logic always have enough
      laters for any pair of components that have communication steps.
      *)
      all_no_extra_later :
        ∀ n : cfg.(name),
          let _ := ctx_irisGS_gen (Λ:=Λc n) in (num_laters_per_step = λ _, 0) ;

      (** We require that communicating components have matching specs. *)
      all_sync_input_output :
        ∀ (n1 n2 : cfg.(name))
          (e1 : (components cfg n1).(Component.Event))
          (e2 : (components cfg n2).(Component.Event)),
          cancel_event_asym n1 n2 e1 e2 ->
          let in_spec := ctx_in_spec (Λ:=Λc n1) [Some e1] in
          let out_spec := ctx_out_spec (Λ:=Λc n2) [Some e2] in
            callee_caller_specs_pair in_spec out_spec ;
    }.

    Let WPc
        (Φs : ∀ n : cfg.(name), (val (Λc n)) -> PROP)
        (Ns : cfg.(name) -> coPset)
        : expr Λ -> cfg.(name) -> PROP :=
      λ e n,
       (if Component.to_val _ (fin_prod.lookup e n : expr (Λc n)) is (Some v)
        then
          |={Ns n}=> Φs n v
        else
          WP (fin_prod.lookup e n : expr (Λc n)) @ (Ns n) ?{{ Φs n }})%I.

    #[local] Lemma convert_wp_wpc
        (Φs : ∀ n : cfg.(name), (val (Λc n)) -> PROP)
        (Ns : cfg.(name) -> coPset)
        (e : expr Λ) (n : cfg.(name)) :
      WP (fin_prod.lookup e n : expr (Λc n)) @ (Ns n) ?{{ Φs n }}
      ⊣⊢@{PROP} WPc Φs Ns e n.
    Proof.
      subst WPc. simpl.
      case_match eqn:Eqn; [|done].
      apply (of_to_val (Λ := Λc n)) in Eqn.
      by apply wp_value_fupd.
    Qed.

    #[local] Lemma convert_wps_wpc
        (Φs : ∀ n : cfg.(name), (val (Λc n)) -> PROP)
        (Ns : cfg.(name) -> coPset)
        (e : expr Λ) (ns : gset cfg.(name)) :
      ([∗ set] n ∈ ns,
        WP (fin_prod.lookup e n : expr (Λc n)) @ (Ns n) ?{{ Φs n }})%I
      ⊣⊢@{PROP} [∗ set] n ∈ ns, WPc Φs Ns e n.
    Proof.
      apply big_sepS_proper. intros. apply convert_wp_wpc.
    Qed.

    #[local] Lemma convert_wps_values
        (Φs : ∀ n : cfg.(name), (val (Λc n)) -> PROP)
        (Ns : cfg.(name) -> coPset)
        (e : expr Λ) (v : val Λ) (ns : gset cfg.(name)) :
      to_val e = Some v ->
      ([∗ set] n ∈ ns, WPc Φs Ns e n)%I
      ⊢@{PROP}
      |={⊤}=> ([∗ set] n ∈ ns, Φs n (fin_prod.lookup v n))%I.
    Proof.
      rewrite /= -fin_prod.fmapO_Some -big_sepS_fupd => IS.
      apply big_sepS_mono.
      intros n _. iIntros "WP". specialize (IS n).
      rewrite /WPc IS.
      by iApply (fupd_mask_mono (Ns n)).
    Qed.

    Theorem wp_io_decompose
        (logComProps : LogicComposeProp)
        (Φs : ∀ n : cfg.(name), (val (Λc n)) -> PROP)
        (Ns : cfg.(name) -> coPset)
        (DISJ : ∀ n1 n2, n1 ≠ n2 -> Ns n1 ## Ns n2)
        (e : expr Λ) :
      let Φ : val Λ -> PROP :=
        (λ v, [∗ set] n ∈ NAMES, Φs n (fin_prod.lookup v n))%I in
      ([∗ set] n ∈ NAMES,
        WP (fin_prod.lookup e n : expr (Λc n)) @ (Ns n) ?{{ Φs n }})%I
      ⊢@{PROP} WP e ?{{ Φ }}.
    Proof.
      iIntros (Φ) "WPs".
      (* simplify WPs who are already at a value *)
      iDestruct (convert_wps_wpc with "WPs") as "WPs".
      iLöb as "IH" forall (e).
      rewrite (wp_unfold (Λ:=Λ)) /wp_pre.

      (** GENERAL PROOF STEP :
      if the composed expression [e] is a value, all components are also values,
      and the obligation here is to combine the post-conditions
      of all component WPs to construct the composed post-condition.
      *)
      case_match eqn:Eqn.
      { by iApply (convert_wps_values with "WPs"). }
      iIntros ([tr_p σ1] ns κ κs nt) "SI".

      (** GENERAL PROOF STEP :
      In case we have to consider non-stuckness: because the composed expression
      [e] is not a value, there must be a component that is not a value.
      We can use the WP of that component to get that it is still reducible.
      - if the reducible step is a non-communicating step, then we can prove
        the composed machine reducible.
      - POTENTIAL PROBLEM:
        if the reducible step is a communicating step, then we will need to
        show that the communicating partner is also reducible with the matching
        communication event.
        This is problematic because reducible seems too strong:
        some configuration is only reducible conditionally on the right input event.

        So we either abandon non-stuckness, OR we need to generalize reducible
        to synchronizing event such that the proof that an output event is
        reducible also includes the proof that its matching input event is also
        reducible.
        This generalization seems to be in line with the obligations one might
        expect when making an output event.

        Intuitively, stronger reducible should imply:

        strong_reducible A e σ  :=
          ∃ κ e' σ' efs, prim_step A e.A σ.A κ e'.A σ'.A efs ∧
          match κ with
          | (Sync A B _ _) :: κ' =>
            ∃ kB' efsB, prim_step B e.B σ.B (Sync A B _ _) :: κB' e'.B σ'.B efsB
          | _ => True
          end.

        where e and σ refer to the composed machine.
        But we want a compositional definition of this concept, so that
        we can break the obligations into separate obligations
        in WP A and WP B and some shared invariant among them.
      *)

      (** GENERAL PROOF STEP :
      Case distinction on the next step [κ].
      We first start with the case where [κ ++ κs] is empty.
      *)
      set tr := (κ ++ κs).
      have Hκs : κ ++ κs = tr. { done. }
      destruct tr as [|[label_e label_src] tr].
      { (** GENERAL PROOF STEP :
        Empty future trace, we shouldn't have any special obligation.
        *)
        iApply fupd_mask_intro; [solve_ndisj|].
        iIntros "Close" (x_i) "Hαi".
        iSplit. {
          (** [reducible] for the composed language.
          We're not handling non-stuckness, so this is no obligation. *)
          done.
        }

        iIntros (e2 σ2 efs STEP). destruct STEP as (? & ? & Eqκs & _).
        (* Here we rely on the fact that a step always emits an event,
        so the trace cannot be empty. *)
        exfalso. clear -Hκs Eqκs. simplify_list_eq.
      }

      (** GENERAL PROOF STEP :
      Here we rely on the fact that a step always emits exactly an event,
      so we know the next step is gonna emit [(label_e, label_src)].
      By *peeking* into [label_src] we know the original component that emits
      this event.
      *)
      iDestruct "SI" as "(FULLTR & SIs)".
      destruct label_src as [n|n label_n|n1 n2 label1 label2].
      - (* [Tau n] step by the component [n] *)
        (* GENERAL PROOF STEP: extract the WP of [n] *)
        have EqL : n ∈ NAMES.
        { by apply elem_of_list_to_set, elem_of_enum. }
        iDestruct (big_sepS_delete _ _ _ EqL with "WPs") as "[WPn WPs]".
        rewrite -convert_wp_wpc.
        rewrite (wp_unfold (Λ:=Λc n)) /wp_pre [to_val _]/=.
        case_match eqn:Eqen.
        { (* Our peeking is sound: the component [n] is not a value, exfalso *)
          iApply fupd_mask_intro; [solve_ndisj|].
          iIntros "Close" (x_i) "Hαi".
          iSplit. { done. }
          iIntros (e2 [tr2 σ2] efs STEP). exfalso. clear -STEP Hκs Eqen.
          destruct STEP as (? & ? & -> & ? & -> & STEP).
          simplify_list_eq.
          destruct label_e as [label_e|]; first naive_solver.
          destruct STEP as [STEP|?]; last naive_solver.
          destruct STEP as (?&?&?&?&STEP&_). simplify_eq.
          apply Component.language_mixin in STEP.
          by rewrite Eqen in STEP.
        }

        (* GENERAL PROOF STEP: extract the [state_interp] of [n] *)
        iDestruct (big_sepS_delete _ _ _ EqL with "SIs") as "[SIn SIs]".
        iDestruct "SIn" as (ns_s nt_n) "SIn".
        rewrite proj_trace_cons proj_trace_singleton_tau_eq.

        (* GENERAL PROOF STEP: apply the WP of [n] *)
        iMod (fupd_mask_subseteq (Ns n)) as "Close1". { solve_ndisj. }
        iMod ("WPn" with "SIn") as "Contn".

        iIntros "!>" (x_i) "Hαi".
        iSplit. { (* not handling non-stuckness *) done. }

        iIntros (e2 [tr2 σ2] efs STEP).
        (* inversion of STEP *)
        destruct STEP as (label_e' & label_src' & -> & -> & -> & STEP).
        inversion Hκs; clear Hκs. subst label_e' label_src' κs.
        destruct label_e as [label_e|].
        { exfalso. clear -STEP. naive_solver. }
        destruct STEP as [STEP|STEP]; last first.
        { exfalso. clear -STEP. naive_solver. }
        destruct STEP as (c & en & sc' & Eqc & PSTEP & -> & STEP & ->).
        inversion Eqc; clear Eqc; subst c.
        (* end inversion *)

        iDestruct ("Contn" $! x_i with "Hαi") as (?) "Contn".
        iDestruct ("Contn" $! en
            (proj_trace (tr_p ++ [(None, Tau n)]) n, sc') []
           with "[%]") as (x_o_n) "[Hαo_n Contn]".
        { rewrite /prim_step /=. exists None.
          by rewrite /= proj_trace_app proj_trace_singleton_tau_eq. }
        iExists x_o_n. iSplitL "Hαo_n". { by iFrame. }
        rewrite (all_no_extra_later n).
        iMod "Contn" as "Contn".
        iIntros "!> !>". iMod "Contn". iIntros "!> !> !> !>".
        iIntros (y_o) "Hβo".

        iMod ("Contn" $! y_o with "Hβo") as (y_i_o) "(Hβo_n & SIn & WPn & ?)".

        iMod "Close1" as "_".
        iIntros "!>".
        iExists y_i_o. iSplitL "Hβo_n". { by iFrame. }
        (* re-establishing [state_interp]s *)
        iSplitL "FULLTR SIs SIn".
        { rewrite 2!length_nil 2!Nat.add_0_l.
          iSplitL "FULLTR". { rewrite -app_assoc. by iFrame. }
          iApply (big_sepS_delete _ _ _ EqL). iSplitL "SIn".
          - rewrite fin_prod.lookup_update_eq. iExists _, _. iFrame "SIn".
          - iApply (big_sepS_mono with "SIs").
            intros nk [Eqnk ?%not_elem_of_singleton]%elem_of_difference.
            rewrite fin_prod.lookup_update_ne; [|done].
            rewrite proj_trace_app (proj_trace_cons _ tr)
                    proj_trace_singleton_tau_ne // app_nil_l app_nil_r.
            done.
        }
        iSplitL; [|done].
        (* applying the induction hypothesis for the next step *)
        iApply "IH".
        iApply (big_sepS_delete _ _ _ EqL). iSplitL "WPn".
        + rewrite -convert_wp_wpc fin_prod.lookup_update_eq.
          by iFrame "WPn".
        + iApply (big_sepS_mono with "WPs").
          clear. intros nk [Eqnk ?%not_elem_of_singleton]%elem_of_difference.
          by rewrite -2!convert_wp_wpc fin_prod.lookup_update_ne.

      - (* [Forward n label_n] step by the component [n] *)
        (* GENERAL PROOF STEP: extract the WP of [n] *)
        have EqL : n ∈ NAMES.
        { by apply elem_of_list_to_set, elem_of_enum. }
        iDestruct (big_sepS_delete _ _ _ EqL with "WPs") as "[WPn WPs]".
        rewrite -convert_wp_wpc.
        rewrite (wp_unfold (Λ:=Λc n)) /wp_pre [to_val _]/=.
        case_match eqn:Eqen.
        { (* the component [n] is not a value, exfalso *)
          iApply fupd_mask_intro; [solve_ndisj|].
          iIntros "Close" (x_i) "Hαi".
          iSplit. { done. }
          iIntros (e2 [tr2 σ2] efs STEP). exfalso. clear -STEP Hκs Eqen.
          destruct STEP as (? & ? & -> & ? & -> & STEP).
          simplify_list_eq.
          destruct label_e as [label_e|]; last naive_solver.
          destruct STEP as (?&?&?&?&?&?&STEP&_). simplify_eq.
          apply Component.language_mixin in STEP.
          by rewrite Eqen in STEP.
        }

        (* GENERAL PROOF STEP: extract the [state_interp] of [n] *)
        iDestruct (big_sepS_delete _ _ _ EqL with "SIs") as "[SIn SIs]".
        iDestruct "SIn" as (ns_s nt_n) "SIn".
        rewrite proj_trace_cons proj_trace_singleton_forward_eq.

        (* GENERAL PROOF STEP: apply the WP of [n] *)
        iMod (fupd_mask_subseteq (Ns n)) as "Close1". { solve_ndisj. }
        iMod ("WPn" with "SIn") as "Contn".

        iIntros "!>" (x_i) "Hαi".
        iSplit. { (* not handling non-stuckness *) done. }

        iIntros (e2 [tr2 σ2] efs STEP).
        (* inversion of STEP *)
        destruct STEP as (label_e' & label_src' & -> & -> & -> & STEP).
        inversion Hκs; clear Hκs. subst label_e' label_src' κs.
        destruct label_e as [label_e|]; last first.
        { exfalso. clear -STEP. naive_solver. }
        destruct STEP as (c & en & e' & sc' & Eqel & InjE & PSTEP & -> & STEP & ->).
        have ? := forward_inj_1 _ _ Eqel. subst c.
        apply forward_inj_2 in Eqel as <-.
        (* end inversion *)

        (* consume input pre-cond resources *)
        iDestruct ("Contn" $! x_i with "(Hαi [%//])") as (?) "Contn".
        iDestruct ("Contn" $! e'
            (proj_trace (tr_p ++ [(Some label_e, Forward n label_n)]) n, sc') []
           with "[%]") as (x_o_n) "[Hαo_n Contn]".
        { rewrite /prim_step /=. exists (Some label_n).
          by rewrite /= proj_trace_app proj_trace_singleton_forward_eq. }
        iExists x_o_n. iSplitL "Hαo_n". { by iFrame. }
        rewrite (all_no_extra_later n).
        iMod "Contn" as "Contn".
        iIntros "!> !>". iMod "Contn". iIntros "!> !> !> !>".
        iIntros (y_o) "Hβo".

        iMod ("Contn" $! y_o with "Hβo") as (y_i_o) "(Hβo_n & SIn & WPn & ?)".

        iMod "Close1" as "_".
        iIntros "!>".
        (* return output post-cond resources *)
        iExists y_i_o. iSplitL "Hβo_n". { by iFrame. }

        (* re-establishing [state_interp]s *)
        iSplitL "FULLTR SIs SIn".
        { rewrite 2!length_nil 2!Nat.add_0_l.
          iSplitL "FULLTR". { rewrite -app_assoc. by iFrame. }
          iApply (big_sepS_delete _ _ _ EqL). iSplitL "SIn".
          - rewrite fin_prod.lookup_update_eq. iExists _, _. iFrame "SIn".
          - iApply (big_sepS_mono with "SIs").
            intros nk [Eqnk ?%not_elem_of_singleton]%elem_of_difference.
            rewrite fin_prod.lookup_update_ne; [|done].
            rewrite proj_trace_app (proj_trace_cons _ tr)
                    proj_trace_singleton_forward_ne // app_nil_l app_nil_r.
            done.
        }
        iSplitL; [|done].
        (* applying the induction hypothesis for the next step *)
        iApply "IH".
        iApply (big_sepS_delete _ _ _ EqL). iSplitL "WPn".
        + rewrite -convert_wp_wpc fin_prod.lookup_update_eq.
          by iFrame "WPn".
        + iApply (big_sepS_mono with "WPs").
          clear. intros nk [Eqnk ?%not_elem_of_singleton]%elem_of_difference.
          by rewrite -2!convert_wp_wpc fin_prod.lookup_update_ne.

      - (* [Sync n1 n2 label1 label2]
        communication step by [n1] (input) and [n2] (output) *)
        (* GENERAL PROOF STEP: extract the WP of [n1] *)
        have EqL1 : n1 ∈ NAMES.
        { by apply elem_of_list_to_set, elem_of_enum. }
        iDestruct (big_sepS_delete _ _ _ EqL1 with "WPs") as "[WP1 WPs]".
        rewrite -convert_wp_wpc.
        rewrite (wp_unfold (Λ:=Λc n1)) /wp_pre [to_val _]/=.
        case_match eqn:Eqen1.
        { (* Our peeking is sound: the component [n1] is not a value, exfalso *)
          iApply fupd_mask_intro; [solve_ndisj|].
          iIntros "Close" (x_i) "Hαi".
          iSplit. { done. }
          iIntros (e2 [tr2 σ2] efs STEP). exfalso. clear -STEP Hκs Eqen1.
          destruct STEP as (? & ? & -> & ? & -> & STEP).
          simplify_list_eq.
          destruct label_e as [|]; first naive_solver.
          destruct STEP as [|STEP]; first naive_solver.
          destruct STEP as (?&?&?&?&?&?&?&?&?&?&?&STEP&_). simplify_eq.
          apply Component.language_mixin in STEP.
          by rewrite Eqen1 in STEP.
        }

        (* GENERAL PROOF STEP: we know that n1 ≠ n2 *)
        case (decide (n1 = n2)) => NEQ12.
        { iApply fupd_mask_intro; [solve_ndisj|].
          iIntros "Close" (x_i) "Hαi".
          iSplit. { done. }
          iIntros (e2 [tr2 σ2] efs STEP). exfalso. subst n2. clear -STEP Hκs.
          destruct STEP as (? & ? & -> & ? & -> & STEP).
          simplify_list_eq.
          destruct label_e as [|]; first naive_solver.
          destruct STEP as [|STEP]; first naive_solver.
          destruct STEP as (?&?&?&?&?&?&?&?&?&?&?&_). simplify_eq. }

        (* GENERAL PROOF STEP: extract the WP of [n2] *)
        have EqL2 : n2 ∈ (NAMES ∖ {[n1]}).
        { apply elem_of_difference. split; last by set_solver.
          by apply elem_of_list_to_set, elem_of_enum. }
        iDestruct (big_sepS_delete _ _ _ EqL2 with "WPs") as "[WP2 WPs]".
        rewrite -convert_wp_wpc.
        rewrite (wp_unfold (Λ:=Λc n2)) /wp_pre [to_val _]/=.
        case_match eqn:Eqen2.
        { (* Our peeking is sound: the component [n2] is not a value, exfalso *)
          iApply fupd_mask_intro; [solve_ndisj|].
          iIntros "Close" (x_i) "Hαi".
          iSplit. { done. }
          iIntros (e2 [tr2 σ2] efs STEP). exfalso. clear -STEP Hκs Eqen2.
          destruct STEP as (? & ? & -> & ? & -> & STEP).
          simplify_list_eq.
          destruct label_e as [|]; first naive_solver.
          destruct STEP as [|STEP]; first naive_solver.
          destruct STEP as (?&?&?&?&?&?&?&?&?&?&?&?&?&STEP&_). simplify_eq.
          apply Component.language_mixin in STEP.
          by rewrite Eqen2 in STEP.
        }

        (* GENERAL PROOF STEP: extract the [state_interp] of [n1] and [n2] *)
        iDestruct (big_sepS_delete _ _ _ EqL1 with "SIs") as "[SI1 SIs]".
        iDestruct "SI1" as (ns1 nt1) "SI1".
        rewrite proj_trace_cons proj_trace_singleton_sync_eq1.
        iDestruct (big_sepS_delete _ _ _ EqL2 with "SIs") as "[SI2 SIs]".
        iDestruct "SI2" as (ns2 nt2) "SI2".
        rewrite proj_trace_cons proj_trace_singleton_sync_eq2;
          last done.

        iMod (fupd_mask_subseteq (Ns n2 ∪ Ns n1)) as "Close1". { solve_ndisj. }
        (* GENERAL PROOF STEP: apply the WP of [n2] (output) *)
        iDestruct ("WP2" with "SI2") as "Cont2".
        iMod (fupd_mask_frame_r with "Cont2") as "Cont2". { solve_ndisj. }
        rewrite left_id_L.
        (* GENERAL PROOF STEP: apply the WP of [n1] (input) *)
        iMod ("WP1" with "SI1") as "Cont1".

        iIntros "!>" (x_i) "Hαi".
        iSplit. { (* not handling non-stuckness *) done. }

        iIntros (e2 [tr2 σ2] efs STEP).
        (* inversion of STEP *)
        destruct STEP as (label_e' & label_src' & -> & -> & -> & STEP).
        inversion Hκs; clear Hκs. subst label_e' label_src' κs.
        destruct label_e as [|].
        { exfalso. clear -STEP. naive_solver. }
        destruct STEP as [STEP|STEP].
        { exfalso. clear -STEP. naive_solver. }
        destruct STEP as (c1 & c2 & ? & el1 & el2 & e1' & e2' & sc1' & sc2' & STEP).
        destruct STEP as (EqS & CAN & PRIM1 & STEP1 & PRIM2 & STEP2 & -> & ->).
        destruct (sync_inj_1 _ _ _ _ EqS) as []. subst c1 c2.
        apply sync_inj_2 in EqS as [-> ->].
        (* end inversion *)

        iDestruct ("Cont2" $! x_i with "(Hαi [%//])") as (?) "Cont2".

        set tr_p' := (tr_p ++ [(None, Sync n1 n2 el1 el2)]).

        iDestruct ("Cont2" $! e2' (proj_trace tr_p' n2, sc2') []
                    with "[%]") as (x_o_2) "[Hαo2 Cont2]".
        { rewrite /=. exists (Some el2).
          by rewrite /= proj_trace_app proj_trace_singleton_sync_eq2. }

        (* invoking linking transformation of resources, to turn
        output post-cond of [n2] into input pre-cond of [n1] *)
        iDestruct (all_sync_input_output _ _ _ _ CAN with "Hαo2")
          as (x_i_1) "(Hαi1 & Hαβ)".

        (* feed the input pre-cond to [n1] *)
        iDestruct ("Cont1" $! x_i_1 with "Hαi1") as (?) "Cont1".
        iDestruct ("Cont1" $! e1' (proj_trace tr_p' n1, sc1') []
                    with "[%]") as (x_o_1) "[Hαo1 Cont1]".
        { rewrite /=. exists (Some el1).
          by rewrite /= proj_trace_app proj_trace_singleton_sync_eq1. }

        iExists x_o_1. iSplitL "Hαo1". { by iFrame. }

        (* trimming laters *)
        rewrite (all_no_extra_later n1) (all_no_extra_later n2).
        iMod "Cont2". iIntros "!> !>". iMod "Cont2". iIntros "!>". iSimpl.
        iMod "Cont1". iIntros "!> !>". iMod "Cont1". iIntros "!>".

        iIntros (y_o) "Hβo".
        iMod ("Cont1" with "Hβo") as (y_i_1) "(Hβi1 & SI1 & WP1 & ?)".

        (* invoking linking transformation of resources, to turn
        input post-cond of [n1] into output post-cond of [n2] *)
        iDestruct ("Hαβ" with "Hβi1") as (y_o_2) "Hβo2".
        iDestruct ("Cont2" with "Hβo2") as "Cont2".

        iDestruct (fupd_mask_frame_r ∅ (Ns n2) (Ns n1) with "Cont2") as "Cont2".
        { solve_ndisj. }
        rewrite 2!left_id_L.
        iMod "Cont2" as (y_i_2) "(Hβi2 & SI2 & WP2 & ?)".

        iMod "Close1" as "_".
        iIntros "!>".
        (* return the output post-cond of [n2] *)
        iExists y_i_2. iSplitL "Hβi2". { by iFrame. }

        (* re-establishing [state_interp]s *)
        iSplitL "FULLTR SI1 SI2 SIs".
        { rewrite !length_nil !Nat.add_0_l.
          iSplitL "FULLTR". { rewrite -app_assoc. by iFrame. }
          iApply (big_sepS_delete _ _ _ EqL1). iSplitL "SI1".
          { rewrite fin_prod.lookup_update_ne // fin_prod.lookup_update_eq.
            iExists _, _. iFrame "SI1". }
          iApply (big_sepS_delete _ _ _ EqL2). iSplitL "SI2".
          { rewrite fin_prod.lookup_update_eq. iExists _, _. iFrame "SI2". }
          iApply (big_sepS_mono with "SIs").
          intros nk [[Eqnk ?%not_elem_of_singleton]%elem_of_difference
                      ?%not_elem_of_singleton]%elem_of_difference.
          do 2 (rewrite fin_prod.lookup_update_ne; [|done]).
          rewrite proj_trace_app (proj_trace_cons _ tr)
                  proj_trace_singleton_sync_ne // app_nil_l app_nil_r.
          done.
        }

        iSplitL; [|done].
        (* applying the induction hypothesis for the next step *)
        iApply "IH".
        iApply (big_sepS_delete _ _ _ EqL1). iSplitL "WP1".
        { rewrite -convert_wp_wpc fin_prod.lookup_update_ne //
                  fin_prod.lookup_update_eq. by iFrame "WP1". }
        iApply (big_sepS_delete _ _ _ EqL2). iSplitL "WP2".
        { rewrite -convert_wp_wpc fin_prod.lookup_update_eq. by iFrame "WP2". }

        iApply (big_sepS_mono with "WPs").
        clear.
        intros nk [[Eqnk ?%not_elem_of_singleton]%elem_of_difference
                      ?%not_elem_of_singleton]%elem_of_difference.
        rewrite -2!convert_wp_wpc.
        by do 2 (rewrite fin_prod.lookup_update_ne; [|done]).
    Qed.
  End with_wps.
End with_config.
End wp_compose.
