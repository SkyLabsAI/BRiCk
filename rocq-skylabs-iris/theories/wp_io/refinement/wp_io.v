(*
 * Copyright (c) 2023 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
*)

(** * Connecting the input-output WP of a language to the Iris WP of the
same language. Note that this lemma does not do any decomposition, and
only changes the way that IO is handled.

This instantiates the refinement relation. There are two variants here:
- [refine_embed.wp_io_run_embed] one uses the state interpretation that embeds
  the refinement relation.
- [refine_inv.wp_io_run_inv] uses the explicit root invariant.

Note the difference between the statements of the former and the latter.
The former simply says `WPio e ⊢ WPiris e`, while the latter
says `root_inv ⊢ WPio e -* WPiris e`.

PROs and CONs:

For the [refine_embed] version :
- PRO: simple setup, no need of extra ghost state, nor extra invariant
- CON: the refinement relation is only accessible through a WP,
  because the refinement inside the [state_interp]. This may not really be
  a CON, if we only care about the refinement relation once we have left
  the logic.

For the [refine_inv] version :
- CON: needs extra ghost state ([mono_list.half γ_con tr_con])
- PRO: we can access the refinement relation within the logic.


TODO: generalize this from using [Compose.config].
*)

Require Import bluerock.iris.extra.bi.atomic_commit.
Require Import bluerock.iris.extra.bi.atomic_update.

Require Import bluerock.iris.extra.wp_io.refinement.inv.

NES.Begin root.

  Section with_app.
    Context `{Ghostly PROP} `{!BiFUpd PROP}.
    Context (x : App.app).
    Import App.
    Implicit Type (γ : AuthSet.gname).

    (** A copy of the refinement framework's [committer] and [requester],
    because we need to have more choices on masks.

    TODO (FM-3811):
    In the decomposition of the framework, ownership is not atomically passed
    one app C1 to another app C2 or vice versa. The updates of the components
    are meant to be executed one after the other, that is, one must run all
    C1's updates, using all available invariants from the masks, and restablish
    the invariants again, before C2's updates can be run, which can all use
    all invariants. It does not support partially running C1, then partially
    running C2, which would allow for atomic arbitrary resources trading between
    C1 and C2 and the invariants.
    The solution to this problem is to index the [requester] and [committer] by
    a mask [E] which be picked by the clients (of the refinement framework) such
    that the masks of a pair of requester and committer are disjoint, and they
    can be run in any order.

    Below, we duplicate the definitions with the empty masks, which are
    sufficiet for the proofs in the demo. Once we apply the generalization for
    committers and requesters, the duplicated definitions can be removed.
    *)
    Definition committer γ (STEP : propset (evt x)) (Q : evt x -> PROP) : PROP :=
      AU  <{ ∃∃ sset, AuthSet.auth γ sset }>
            @ ∅, ∅
          <{ ∀∀ s e s',
              [| s ∈ sset /\ e ∈ STEP /\ x.(lts).(lts_step) s (Some e) s' |] ∗
              AuthSet.auth_exact γ s'
            , COMM Q e }>.
    Definition requester γ (STEP : propset (evt x)) (Q : evt x -> PROP) : PROP :=
      AC  << ∀ s, AuthSet.frag_exact γ s ∗
              [| (*The model is safe to step any event in [STEP].*)
                forall e, e ∈ STEP ->
                  exists s', x.(lts).(lts_step) s (Some e) s' |] >>
            @ ∅,∅
          << ∃ e, [| e ∈ STEP |] ∗
              AuthSet.frag γ {[ s' | x.(lts).(lts_step) s (Some e) s' ]}
            , COMM Q e >>.
  End with_app.

Section stateI_io.
  Context {PROP : bi} `{!BiFUpd PROP} `{!Ghostly PROP}.

  Context {cfg : Compose.config}.
  Context (absA : App.app).

  Let absE := App.evt absA.
  Let Λ := Compose.lts_lang cfg.

  Context (R : absE -> (Compose.event cfg) -> Prop).

  Definition input_spec (γ_abs : AuthSet.gname) (κ : list (observation Λ))
      : PrePost PROP := {|
    tele_pre :=
      match κ with
      | [(Some _, _)] => [tele (Q : absE -> PROP)]
      | _ => [tele]
      end ;
    tele_post _ := [tele] ;
    pre :=
      match κ with
      | [(Some e, _)] =>
          if Compose.is_input e is true then
            (* only if e is an input *)
            tele_app (λ Q,
              root.committer absA γ_abs {[ ae | R ae e ]} (λ ae, [| R ae e |] ∗ Q ae)%I
            )
          else λ _, emp%I
      | _ => λ _, emp%I
      end ;
    post :=
      match κ with
      | [(Some e, _)] =>
          λ args1 _,
            if Compose.is_input e is true then
              tele_app (TT:= [tele _]) (λ Q, ∃ ae, [| R ae e |] ∗ Q ae)%I args1
            else emp%I
      | _ => λ _ _, emp%I
      end ;
  |}.

  Definition output_spec (γ_abs : AuthSet.gname) (κ : list (observation Λ))
      : PrePost PROP := {|
    tele_pre :=
      match κ with
      | [(Some _, _)] => [tele (Q : PROP)]
      | _ => [tele]
      end ;
    tele_post _ := [tele] ;
    pre :=
      match κ with
      | [(Some e, _)] =>
          if Compose.is_input e is false then
            (* only if e is an output *)
            tele_app (λ Q, ∃ ae, [| R ae e |] ∗
              root.requester absA γ_abs {[ ae' | ae' = ae ]} (λ _, Q))%I
          else
            λ _, emp%I
      | _ => λ _, emp%I
      end ;
    post :=
      match κ with
      | [(Some e, _)] =>
          λ args1 _,
            if Compose.is_input e is false then
              tele_app (TT:= [tele _]) (λ Q, Q)%I args1
            else emp%I
      | _ => λ _ _, emp%I
      end
  |}.

  Definition inout_irisGS_gen_instance γ `{!irisGS_gen Λ PROP}
    : inout_irisGS_gen Λ PROP := {|
      ctx_irisGS_gen := _ ;
      ctx_out_spec := output_spec γ ;
      ctx_in_spec := input_spec γ ;
  |}.

  Definition wp_io γ
      `{!irisGS_gen Λ PROP} `{!BiLaterContractive PROP} :=
    wp (Wp:=@inout_weakestpre.wp' _ _ _ _ (inout_irisGS_gen_instance γ)).
End stateI_io.

Section wp_io.
  Context {PROP : bi} `{!BiFUpd PROP} `{!Ghostly PROP} `{!BiLaterContractive PROP}.

  Context {cfg : Compose.config}.
  Context (absA : App.app).

  Let absE := App.evt absA.
  Let absLTS := App.lts absA.

  Context (R : absE -> (Compose.event cfg) -> Prop).

  Let Λ := Compose.lts_lang cfg.

  Context `{ORG_irisGS : !irisGS_gen Λ PROP}.

  Lemma mk_committer γ_abs ss (ev : Compose.event cfg) :
    AuthSet.auth γ_abs ss
    ⊢ root.committer absA γ_abs {[ ae | R ae ev ]}
        (λ ae, [| R ae ev |] ∗
          ∃ s s', [| s ∈ ss ∧ lts_step (App.lts absA) s (Some ae) s' |] ∗
          AuthSet.auth_exact γ_abs s')%I.
  Proof.
    iIntros "sF".
    rewrite /root.committer.
    iAuIntro. rewrite /atomic_acc.
    iIntros "!>".
    iExists _. iFrame "sF". iSplit.
    { by iIntros "$". }
    iIntros (s e' s') "[%STEP sA]".
    destruct STEP as (Inss' & Eqe' & STEP).
    rewrite elem_of_PropSet in Eqe'.
    iIntros "!>". iSplit; [done|]. iExists _, _. by iFrame.
  Qed.

  Section with_embed.
    Context `{!BiBUpdFUpd PROP}.

    (* TODO : not handling non-stuck ness yet. *)
    Lemma wp_io_run_embed (γ_abs : AuthSet.gname) E e Φ :
      wp_io absA R γ_abs MaybeStuck E e Φ ⊢
      wp_embed R γ_abs MaybeStuck top e Φ.
    Proof using All.
      iIntros "WP".
      iLöb as "IH" forall (e).
      rewrite {2}/wp_embed {2}/wp_io.
      rewrite wp_unfold weakestpre.wp_unfold.
      rewrite /weakestpre.wp_pre /wp_pre.
      case_match. { by iMod "WP" as "$". }
      iIntros ([tr_p σ1] ns κ κs nt) "[RF SI]".
      iDestruct "RF" as (tr_abs) "[absI %RF]".

      iMod (fupd_mask_subseteq E) as "CC". { solve_ndisj. }
      iMod ("WP" with "SI") as "WP".
      iIntros "!>".
      iSplitR; [done|].
      iIntros (e2 σ2 efs STEP).

      assert (efs = [] ∧ ∃ oe, κ = [oe] ∧ σ2.1 = tr_p ++ [oe])
        as [-> [[oe os] [-> Eqtrp]]].
      { clear-STEP. destruct σ2. inversion STEP. naive_solver. }

      destruct oe as [ev|]; last first.
      { (* TAU step *)
        iDestruct ("WP" $! () with "[//]") as "[? WP]".
        iDestruct ("WP" with "[%//]") as (?) ">WP". simpl.
        iIntros "!> !>".
        iApply (step_fupdN_wand with "WP").
        iIntros "WP".
        iMod ("WP" with "[//]") as "(? & $ & WP & WPs)".
        rewrite Eqtrp fmap_app /=.
        iMod "CC" as "_".
        iIntros "!>". iSplitL "absI".
        { iExists _. iFrame "absI".
          iPureIntro. clear -RF.
          rewrite filter_app (_ : filter is_Some [_] = []).
          - by rewrite app_nil_r.
          - apply list.list_filter_empty_iff. by constructor. }
        iSplit; [|done].
        iApply ("IH" with "WP"). }

      iDestruct "absI" as (ss) "(aF & %INS & %s_init & %INIT & %REACH)".
      destruct (Compose.is_input ev) eqn:Eqin.
      - (* INPUT step *)
        iDestruct (mk_committer _ _ ev with "aF") as "aF".
        iDestruct ("WP" with "[aF]") as "[? WP]".
        { instantiate (1:=[tele_arg _]). rewrite /= Eqin /= /absE /=.
          iExact "aF". }
        iDestruct ("WP" with "[%//]") as (?)"[? >WP]".
        iIntros "!> !>".
        iApply (step_fupdN_wand with "WP").
        iIntros "WP".
        rewrite /= Eqin.
        iMod ("WP" with "[//]") as "(Post & $ & WP & WPs)".
        iDestruct "Post" as (ae Rae s s' [Ins aeSTEP]) "aF".
        iMod "CC" as "_".
        rewrite Eqtrp fmap_app /=.

        iIntros "!>". iSplitL "aF".
        { iExists (tr_abs ++ [Some ae]).
          iSplitL.
          - iExists {[s']}. rewrite /AuthSet.auth_exact. iFrame "aF".
            iPureIntro. repeat split.
            + clear. set_solver.
            + exists s_init. split; [done|].
              intros ? <-%elem_of_singleton. by econstructor; eauto.
          - iPureIntro.
            rewrite 2!filter_app.
            apply Forall2_app; [done|].
            clear -Rae.
            do 2 (rewrite filter_cons_True; last done).
            rewrite 2!filter_nil. constructor; [|done].
            by constructor. }
        iSplit; [|done].
        iApply ("IH" with "WP").

      - (* OUTPUT step *)
        iDestruct ("WP" with "[]") as "[? WP]".
        { instantiate (1:= [tele_arg (λ _, emp)%I]). by rewrite /= Eqin. }
        iDestruct ("WP" with "[%//]") as (Q) "[AC >WP]".
        iIntros "!> !>".
        iApply (step_fupdN_wand with "WP").
        iIntros "WP".
        rewrite /= Eqin.
        iDestruct "AC" as (ae Rae) "AC".
        iMod "AC" as (s) "([sF %Ine] & Close)".
        iDestruct (AuthSet.frag_exact_auth_sub with "sF aF") as %Inss.
        destruct (Ine ae) as [s' STEPs].
        { by apply elem_of_PropSet. }
        set ss' := {[ s' | lts_step (App.lts absA) s (Some ae) s' ]}.
        iMod (AuthSet.frag_auth_upd _ ss' with "sF aF") as "[sF aF]".
        iMod ("Close" $! ae with "[$sF]") as "Q".
        { iPureIntro. clear. set_solver. }
        iMod ("WP" with "Q") as "(? & sI & WP & WPs)".
        iMod "CC" as "_".

        iIntros "!>". iSplitL "aF sI".
        { iFrame "sI". iExists (tr_abs ++ [(Some ae)]).
          iSplitL.
          - iExists ss'. iFrame "aF". iPureIntro. repeat split.
            + exists s'. by apply elem_of_PropSet.
            + exists s_init. split; [done|].
              intros ?. rewrite elem_of_PropSet. intros ?. by econstructor; eauto.
          - iPureIntro.
            rewrite Eqtrp fmap_app 2!filter_app.
            apply Forall2_app; [done|].
            clear -Rae.
            do 2 (rewrite filter_cons_True; last done).
            rewrite 2!filter_nil. constructor; [|done].
            by constructor. }
        iSplit; [|done].
        iApply ("IH" with "WP").
    Qed.
  End with_embed.

(* (* TODO fix masks with [root_inv_committer] *)
  Section with_inv.
    Context `{!BiBUpdFUpd PROP}.
    Context `{!HasUsualOwn PROP (mono_list.traceR (option $ Compose.event cfg))}.

    Definition root_inv γ_con γ_abs :PROP :=
      root.ghost_trace_refine_inv R γ_con γ_abs (@refinement_ns start_refinement).

    Lemma root_inv_committer γ_con γ_abs ev tr_con :
      root_inv γ_con γ_abs
      ⊢ mono_list.half γ_con tr_con -∗
          root.committer absA γ_abs {[ ae | R ae ev ]}
            (λ ae, [| R ae ev |] ∗ mono_list.half γ_con (tr_con ++ [Some ev])).
    Proof using All.
      iIntros "#INV Tr".
      rewrite /root.committer.
      iAuIntro. rewrite /atomic_acc.
      iInv "INV" as (tr_con') "[>Tr' RF]" "CloseI".
      iDestruct (mono_list.half_agree with "Tr' Tr") as %->.

      iDestruct "RF" as (tr_abs) "[absA RF]".
      iDestruct "absA" as (ss) "(>absA & INS & REACH)".

      iApply fupd_mask_intro. { solve_ndisj. }
      iIntros "Close1".
      iExists _. iFrame "absA". iSplit.
      { iIntros "absA". iFrame "Tr".
        iMod "Close1" as "_".
        iMod ("CloseI" with "[-]") as "?"; last done.
        iNext. iExists _. iFrame. iExists _. iSplit; [|done].
        iExists _. by iFrame. }

      iIntros (s ae s') "[%STEP absA]".
      destruct STEP as (Inss & Rae & STEP).
      rewrite propset.elem_of_PropSet in Rae.
      iMod "Close1" as "_".
      iMod (mono_list.half_update with "Tr Tr'") as "[$ Tr']". { by eexists. }
      iMod ("CloseI" with "[-]") as "_".
      { iNext.
        iDestruct "INS" as %INS.
        iDestruct "REACH" as %(s_init & INIT & REACH).
        iDestruct "RF" as %RF.
        iExists _. iFrame. iExists _. iSplitL.
        - iExists _. rewrite /AuthSet.auth_exact. iFrame.
          iPureIntro. repeat split.
          + clear. set_solver.
          + exists s_init. split; [done|].
            intros ? <-%elem_of_singleton. by econstructor; eauto.
        - iPureIntro.
          rewrite 2!filter_app.
          apply Forall2_app; [done|].
          do 2 (rewrite filter_cons_True; last done).
          rewrite 2!filter_nil. constructor; [|done].
          by constructor. }
      done.
    Qed.

    (* TODO : not handling non-stuckness yet. *)
    Lemma wp_io_run_inv γ_con γ_abs E e Φ :
      root_inv γ_con γ_abs ⊢
      wp_io absA R γ_abs MaybeStuck E e Φ -∗
      wp_inv γ_con MaybeStuck top e Φ.
    Proof using All.
      iIntros "#INV WP".
      iLöb as "IH" forall (e).
      rewrite {2}/wp_inv {2}/wp_io.
      rewrite wp_unfold weakestpre.wp_unfold.
      rewrite /weakestpre.wp_pre /wp_pre.
      case_match. { by iMod "WP" as "$". }
      iIntros ([tr_p σ1] ns κ κs nt) "[ha1 SI]".

      iMod (fupd_mask_subseteq E) as "CC". { solve_ndisj. }
      iMod ("WP" with "SI") as "WP".
      iIntros "!>".
      iSplitR; [done|].
      iIntros (e2 σ2 efs STEP).

      assert (efs = [] ∧ ∃ oe, κ = [oe] ∧ σ2.1 = tr_p ++ [oe])
        as [-> [[oe os] [-> Eqtrp]]].
      { clear-STEP. destruct σ2. inversion STEP. naive_solver. }

      destruct oe as [ev|]; last first.
      { (* TAU step *)
        iDestruct ("WP" $! () with "[//]") as "[? WP]".
        iDestruct ("WP" with "[%//]") as (?) ">WP". simpl.
        iIntros "!> !>".
        iApply (step_fupdN_wand with "WP").
        iIntros "WP".
        iMod ("WP" with "[//]") as "(? & $ & WP & WPs)".
        rewrite Eqtrp fmap_app /=.
        iMod "CC" as "_".
        iInv "INV" as (tr_con) "[>ha2 RF]".
        iDestruct (mono_list.half_agree with "ha1 ha2") as %<-.
        iMod (mono_list.half_update with "ha1 ha2") as "[$ ha2]".
        { by eexists. }
        iIntros "!>". iSplitL "RF ha2".
        { iNext. iExists _. iFrame.
          (* TODO make a lemma *)
          iDestruct "RF" as (?) "[RF %RF]".
          iExists _. iFrame. iPureIntro. clear -RF.
          rewrite filter_app (_ : filter is_Some [_] = []).
          - by rewrite app_nil_r.
          - apply list.list_filter_empty_iff. by constructor. }

        iIntros "!>".
        iSplit; [|done].
        iApply ("IH" with "WP"). }

      destruct (Compose.is_input ev) eqn:Eqin.
      - (* INPUT step *)
        iDestruct (root_inv_committer _ _ ev with "INV ha1") as "COM".
        iDestruct ("WP" with "[COM]") as "[? WP]".
        { instantiate (1:=[tele_arg (_)]). rewrite /= Eqin /=. iExact "COM". }
        iDestruct ("WP" with "[%//]") as (?)"[? >WP]".
        iIntros "!> !>".
        iApply (step_fupdN_wand with "WP").
        iIntros "WP".
        iMod ("WP" with "[//]") as (?) "(Post & $ & WP & WPs)".
        rewrite /= Eqin Eqtrp fmap_app /=.
        iMod "CC" as "_".
        iMod "Post" as (ae Rae) "$".
        iIntros "!>".
        iSplit; [|done].
        iApply ("IH" with "WP").

      - (* OUTPUT step *)
        iDestruct ("WP" with "[]") as "[? WP]".
        { instantiate (1:= [tele_arg (λ _, emp)%I]). by rewrite /= Eqin. }
        iDestruct ("WP" with "[%//]") as (?) "[AC >WP]".
        iIntros "!> !>".
        iApply (step_fupdN_wand with "WP").
        iIntros "WP".
        iMod ("WP" with "[//]") as (?) "(? & $ & WP & WPs)". rewrite /= Eqin.
        iMod "CC" as "_".

        rewrite Eqtrp.
        iInv "INV" as (tr_con) "[>ha2 RF]" "CloseI".
        iDestruct (mono_list.half_agree with "ha1 ha2") as %<-.
        iMod (mono_list.half_update with "ha1 ha2") as "[$ ha2]".
        { rewrite fmap_app. by eexists. }
        iDestruct "RF" as (tr_abs) "[RF FRF]".
        iDestruct "RF" as (ss) "(>aF & REACH)".
        iDestruct "AC" as (ae Rae) "AC".
        iMod "AC" as (s) "([sF %Ine] & Close)".
        iDestruct (AuthSet.frag_exact_auth_sub with "sF aF") as %Inss.
        destruct (Ine ae) as [s' STEPs].
        { apply elem_of_PropSet. by exists (). }
        set ss' := {[ s' | lts_step (App.lts absA) s (Some ae) s' ]}.
        iMod (AuthSet.frag_auth_upd _ ss' with "sF aF") as "[sF aF]".
        iMod ("Close" $! ae with "[$sF]") as "?".
        { iPureIntro. clear. set_solver. }

        iMod ("CloseI" with "[aF ha2 REACH FRF]") as "?".
        { iNext. iExists _. iFrame.
          iExists (tr_abs ++ [(Some ae)]).
          iDestruct "REACH" as %(INS & s_init & INIT & REACH).
          iDestruct "FRF" as %RF.
          iSplitL.
          - iExists ss'. iFrame "aF". iPureIntro. repeat split.
            + exists s'. by apply elem_of_PropSet.
            + exists s_init. split; [done|].
              intros ?. rewrite elem_of_PropSet. intros ?. by econstructor; eauto.
          - iPureIntro.
            rewrite fmap_app 2!filter_app.
            apply Forall2_app; [done|].
            clear -Rae.
            do 2 (rewrite filter_cons_True; last done).
            rewrite 2!filter_nil. constructor; [|done].
            by constructor. }
        iIntros "!>".
        iSplit; [|done].
        iApply ("IH" with "WP").
    Qed.
  End with_inv.
*)
End wp_io.

NES.End root.
