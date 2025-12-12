(*
 * Copyright (C) 2020-2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(*** The Spectra Framework *)
(**
- v1 developed by Gregory Malecha and Jonas Kastberg Hinrichsen.
- v2 developed by Gordon Stewart.
- further development by Abhishek Anand, Paolo G. Giarrusso, Yoichi Hirai,
  Hoang-Hai Dang.

See the documentation in spectra.md for more details.
*)

Require Import stdpp.namespaces.
Require Import bluerock.prelude.base.
Require Export bluerock.prelude.sts.
Require Import bluerock.prelude.finite.
Require Import bluerock.prelude.sets.
Require Export bluerock.prelude.propset.
Require Import bluerock.prelude.fin_sets.
Require Import bluerock.prelude.bytestring.
Require Import bluerock.prelude.tactics.proper.

Require Import bluerock.iris.extra.bi.prelude.
Require Import bluerock.iris.extra.bi.observe.
Require Import bluerock.iris.extra.bi.big_op.
Require Import bluerock.iris.extra.bi.atomic_commit.
Require Import bluerock.iris.extra.bi.atomic_update_properties.
Require Import bluerock.iris.extra.bi.spec.knowledge.
Require Import bluerock.iris.extra.bi.prop_constraints.
Require Import bluerock.iris.extra.bi.invariants.

Require Export bluerock.iris.extra.base_logic.lib.auth_set.
Require Import bluerock.iris.extra.proofmode.fancy_updates.
Require Import bluerock.iris.extra.proofmode.proofmode.

Import ChargeNotation.

(* Belongs to stdpp to support [cbn], same as we did for [gset]. *)
#[local] Arguments coPset_difference : simpl never.
#[local] Arguments stdpp.base.difference : simpl nomatch.

Definition refinement_rootNS := nroot.@@"refinement".

(*** Refinement Namespace *)
(** This class manages the namespaces used by decompose invariants. *)
Class refinement :=
  { refinement_root : list bs
    (* ^| The current root. *)

  ; refinement_mkns (ss : list bs) := refinement_rootNS .@ss
  ; refinement_ns : namespace := refinement_mkns refinement_root
  ; refinement_cur : coPset := ↑refinement_ns
    (* ^| The current refinement namespace has form:
            nroot.@@"refinement".@refinement_root.
          At lower levels, the root is extended by list append rather
          then [ndot]. This ensures that lower levels have disjoint namespaces
          from the current root.*)

  ; refinement_up : coPset
    (* ^| All the namespaces above the current point. *)
  ; refinement_up_sub : refinement_up ⊆ ↑ refinement_rootNS

  ; refinement_disj :
      forall ss : list bs,
        ↑(refinement_mkns (refinement_root++ss)) ## refinement_up }.
    (* ^| [refinement_up] is disjoint from all list-app extensions of
          the root. *)

(** [refinement] is instantiatable. *)
#[program] Definition start_refinement : refinement :=
  {| refinement_root := []
   ; refinement_up := ∅ |}.
Next Obligation. set_solver. Qed.
Next Obligation. set_solver. Qed.

(** Go down a level (indexed by bytestring [arg]): *)
#[program] Definition go_down (arg : bs) (cur : refinement) : refinement :=
  {| refinement_root := @refinement_root cur ++ [arg]
   ; refinement_up := @refinement_cur cur ∪ @refinement_up cur
     (* ^| [refinement_up] is the union of the current level and those above. *)
   ; refinement_disj := _ |}.
Next Obligation.
  move => _ cur. have ? := @refinement_up_sub cur. solve_ndisj.
Qed.
Next Obligation.
  move => arg cur ns; rewrite disjoint_union_r.
  split; last first. { rewrite -app_assoc. apply: refinement_disj. }
  rewrite /refinement_cur/refinement_ns.
  apply: ndot_ne_disjoint.
  by elim: refinement_root => // x l' IH [].
Qed.
Section with_refinement.
  Context {R : refinement}.
  Lemma refinement_cur_up_disj : refinement_cur ## refinement_up.
  Proof. move: (@refinement_disj R); move/(_ []); rewrite app_nil_r => //. Qed.

  Lemma up_go_left bs :
    @refinement_up (go_down bs R) = refinement_cur ∪ refinement_up.
  Proof. by []. Qed.
End with_refinement.

Module masks.
  (**
  A consistent choice of masks.
  When proving requesters, clients can use their own invariants with mask [E : coPset],
  such that [E ⊆ O \ ↑refinement_rootNS] and [I ⊆ O \ ↑refinement_rootNS \ E].
  *)
  Record t : Set := {
    O : coPset; (** [O]uter mask *)
    I : coPset; (** [I]nner mask *)
    order : I ⊆ O;
    RinO : ↑refinement_rootNS ⊆ O;
  }.

  Program Definition default := {|
    O := ⊤ ;
    I := ∅ ;
  |}.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  #[global] Instance t_inh : Inhabited t.
  Proof. exact (populate default). Qed.

  Module hints.
    #[export] Hint Resolve order RinO : ndisj.
  End hints.
End masks.
Import masks.hints.
Implicit Type (m : masks.t).

(*** Apps *)
Module App.
  (** [App]s bundle an LTS with its event type.
  [AuthSet.inG ...] asserts that Σ has an auth set over the type of the LTS. *)
  Module Σ.
    Class app {Σ : gFunctors} := mk {
      evt : Type;
      lts : LTS evt;
      #[global] inG :: inG Σ (auth_setR lts.(lts_state));
    }.
    #[global] Arguments app : clear implicits.
    #[global] Arguments mk {_} evt lts {_} : assert.
    #[global] Arguments evt {_} _ : assert.
    #[global] Arguments lts {_} _ : assert.
    #[global] Arguments inG {_} _ : assert.
  End Σ.

  (** BI-general version of Σ.app *)
  Class app `{Ghostly PROP} := mk {
    evt : Type;
    lts : LTS evt;
    #[global] inG :: HasUsualOwn PROP (auth_setR lts.(lts_state));
  }.
  #[global] Arguments mk {_ _} evt lts {_} : assert.
  #[global] Arguments evt {_ _} _ : assert.
  #[global] Arguments lts {_ _} _ : assert.
  #[global] Arguments inG {_ _} _ : assert.
End App.

(*** Steps *)
Module Step.
  (*[NOTE: tau_safe] is vacuous if [sset] is empty. The toplevel
    invariant holding the whole system-state auth should record that
    [sset] is nonempty.  Nonemptiness of [sset] is preserved by
    [updater]. Nonemptiness is established initially by starting the
    system in a state related to the initial state of the whole-system
    model [AuthSet.auth_exact γ {[ wholesystem_init ]}]. *)
  Notation tau_safe lts sset :=
    (forall s, s ∈ sset -> exists s', lts.(lts_step) s None s').

  Section with_app.
    Import App.

    Context `{Ghostly PROP} `{!BiFUpd PROP}.
    Context (x : App.app) (E : coPset).
    Implicit Type (γ : AuthSet.gname).

    #[local] Set Default Proof Using "All".

    (* This avoids duplicate reasoning to establish a property [learn],
    typically about the final state: once to prove the atomic_pre, then in the
    proof of the public postcondition.
    You can learn [learn] during the atomic_pre proof and you get to use it in
    the proof of the public postcondition. Use the lemma
    [requester_learn_implies] with an appropriate [learn] before proving a [requester]. *)
    Definition gen_requester_learn m γ (STEP : propset (evt x))
        (learn : lts_state (lts x) -> evt x -> lts_state (lts x) -> Prop)
        (Q : evt x -> PROP) : PROP :=
      AC  << ∀ sset, AuthSet.frag γ sset **
                  [| ∃ s, s ∈ sset |] **
                  [| (*The model is safe to step any event in [STEP].*)
                    forall s e, s ∈ sset -> e ∈ STEP ->
                    exists s', x.(lts).(lts_step) s (Some e) s' /\ learn s e s' |] >>
            @ m.(masks.O) ∖ E, m.(masks.I)
          << ∃ e, [| e ∈ STEP |] **
                  AuthSet.frag γ {[ s' | exists s, s ∈ sset /\ x.(lts).(lts_step) s (Some e) s' /\ learn s e s' ]}
          , COMM Q e >>.

    (** This is the AC a requester /proves/ in order to perform its
        own [STEP] action. *)
    Definition gen_requester m γ (STEP : propset (evt x)) (Q : evt x -> PROP) : PROP :=
      gen_requester_learn m γ STEP (λ _ _ _, True) Q.

    (** This is the AC a committer /assumes/ in order to perform a
        [STEP] action. *)
    Definition gen_committer m γ (STEP : propset (evt x)) (Q : evt x -> PROP) : PROP :=
      AU  <{ ∃∃ sset, AuthSet.auth γ sset }>
           @ m.(masks.O), m.(masks.O) ∖ E
          <{ ∀∀ sset' e,
              [| e ∈ STEP |] **
              [| ∃ s, s ∈ sset' |] **
              [| ∀ s', s' ∈ sset' -> ∃ s, s ∈ sset /\ x.(lts).(lts_step) s (Some e) s' |] **
              AuthSet.auth γ sset',
             COMM Q e }>.

    Definition alt_gen_committer m γ (STEP : propset (evt x)) (Q : evt x -> PROP) : PROP :=
      ∀ sset0, AuthSet.frag γ sset0
        ={m.(masks.O), m.(masks.O) ∖ E}=∗
        ∃ sset, [| sset0 ⊆ sset |] **
        ∀ sset' e,
          [| e ∈ STEP |] **
          [| ∃ s, s ∈ sset' |] **
          [| ∀ s', s' ∈ sset' -> ∃ s, s ∈ sset /\ x.(lts).(lts_step) s (Some e) s' |]
          ={m.(masks.O) ∖ E, m.(masks.O)}=∗
          AuthSet.frag γ sset' ** Q e.

    (** This is the AC a requester /proves/ in order to perform its
        own [STEP] action.
    TODO: requester := requester_learn γ STEP (λ _ _ _, True) Q.
    *)
    Definition requester γ (STEP : propset (evt x)) (Q : evt x -> PROP) : PROP :=
      AC  << ∀ s, AuthSet.frag_exact γ s **
                  [| (*The model is safe to step any event in [STEP].*)
                    forall e, e ∈ STEP ->
                    exists s', x.(lts).(lts_step) s (Some e) s' |] >>
            @ ⊤ ∖ E,∅
          << ∃ e, [| e ∈ STEP |] **
                AuthSet.frag γ {[ s' | x.(lts).(lts_step) s (Some e) s' ]}
          , COMM Q e >>.

    (* This avoids duplicate reasoning to establish a property [learn],
    typically about the final state: once to prove the atomic_pre,
    then in the proof of the public postcondition.
    You can learn [learn] during the atomic_pre proof and you get to use it
    in the proof of the public postcondition.
    Use the lemma [requester_learn_implies] with an appropriate [learn] before proving a [requester]  *)
    Definition requester_learn γ (STEP : propset (evt x))
        (learn : lts_state (lts x) -> evt x -> lts_state (lts x) -> Prop)
        (Q : evt x -> PROP) : PROP :=
      AC  << ∀ s, AuthSet.frag_exact γ s **
                  [| (*The model is safe to step any event in [STEP].*)
                    forall e, e ∈ STEP ->
                    exists s', x.(lts).(lts_step) s (Some e) s' /\ learn s e s' |] >>
            @ ⊤ ∖ E,∅
          << ∃ e, [| e ∈ STEP |] ** Exists s',
                  [| x.(lts).(lts_step) s (Some e) s' |] ** [| learn s e s' |] **
                  AuthSet.frag γ {[ s' ]}
          , COMM Q e >>.

    (** This is the AC a committer /assumes/ in order to perform a
        [STEP] action. *)
    Definition committer γ (STEP : propset (evt x)) (Q : evt x -> PROP) : PROP :=
      AU  <{ ∃∃ sset, AuthSet.auth γ sset }>
           @ ⊤, ⊤ ∖ E
          <{ ∀∀ s e s',
              [| s ∈ sset /\ e ∈ STEP /\ x.(lts).(lts_step) s (Some e) s' |] **
              AuthSet.auth_exact γ s',
             COMM Q e }>.

    (** Updaters grant the right to make silent (tau) steps. They're justified
        by opening the decompose invariants of the framework. *)
    Definition updater_def γ : PROP :=
      □ ∀ (sset : propset x.(lts).(lts_state))
          (_ : exists s, s ∈ sset)
          (_ : tau_safe x.(lts) sset),
          (AuthSet.frag γ sset ={E}=∗
            AuthSet.frag γ {[ s' | exists s, s ∈ sset /\ x.(lts).(lts_step) s None s' ]}).

    (* Iris-style sealing *)
    #[local] Definition updater_aux : seal (@updater_def). Proof. by eexists. Qed.
    Definition updater := updater_aux.(unseal).
    Definition updater_unseal : @updater = _ := updater_aux.(seal_eq).

    #[global] Instance updater_persistent γ : Persistent (updater γ).
    Proof. rewrite updater_unseal. apply _. Qed.
    #[global] Instance updater_affine γ : Affine (updater γ).
    Proof. rewrite updater_unseal. apply _. Qed.

    (** We have the following relations:

          GRL ---------> GR ---------> GC
          ^             ^              |
          |             |              ∨
          RL ----------> R  ---------> C

      + C  : committer
      + GC : gen_committer
      + GRL: gen_requester_learn
      + RL : requester_learn
      + GR : gen_requester
      + R  : requester
    *)

    Lemma requester_learn_implies `{!BiBUpdFUpd PROP} P γ STEP Q :
      requester_learn γ STEP P Q |-- requester γ STEP Q.
    Proof.
      iIntros "ac".
      iAcIntro; rewrite /requester /requester_learn /commit_acc /=.
      iMod "ac" as (t) "((F & %HI) & W) /="; iModIntro.
      iExists t. iFrame "F".
      iSplitR. { iIntros "!%". naive_solver. }
      iIntros "%ev [%Hin F]".
      destruct (HI _ Hin) as [s'].
      iMod (AuthSet.frag_upd _ {[s']} with "F") as "?"; [set_solver|].
      iApply "W"; eauto.
      iFrame. eauto.
    Qed.

    Lemma requester_learn_gen_requester_learn `{!BiBUpdFUpd PROP} P γ STEP Q :
      requester_learn γ STEP P Q |-- gen_requester_learn masks.default γ STEP P Q.
    Proof.
      iIntros "ac".
      iAcIntro; rewrite /requester_learn /gen_requester_learn /commit_acc /=.
      iMod "ac" as (s0) "((F & %HI) & W) /="; iModIntro.
      iExists {[s0]}. rewrite /AuthSet.frag_exact. iFrame "F".
      iSplitR. { iIntros "!%". set_solver. }
      iIntros "%ev [%Hin F]".
      destruct (HI _ Hin) as [s'].
      iMod (AuthSet.frag_upd _ {[s']} with "F") as "?"; [set_solver|].
      iApply "W"; eauto.
      iFrame. eauto.
    Qed.

    Lemma gen_requester_learn_mono m γ STEP `{!BiBUpdFUpd PROP} :
      Proper  ((pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (impl))))
                   ==> pointwise_relation _ (⊢) ==> (⊢))
              (gen_requester_learn m γ STEP ).
    Proof.
      rewrite /gen_requester_learn => P1 P2 HP Q1 Q2 HQ.
      iIntros "ac".
      iAcIntro; rewrite /gen_requester /gen_requester_learn /commit_acc /=.
      iMod "ac" as (t) "((F & %HI) & W) /="; iModIntro.
      destruct HI as (IN0 & HI).
      iExists t. iFrame (IN0) "F".
      iSplitR. { iIntros "!%". f_equiv_tidy. naive_solver. }
      iIntros "%ev [%Hin F]".
      iApply HQ.
      iApply ("W" with "[>-]"). iFrame (Hin).
      iMod (AuthSet.frag_upd with "F") as "$"; last done. f_equiv_tidy. set_solver.
    Qed.

    Lemma gen_requester_learn_gen_requester `{!BiBUpdFUpd PROP} P m γ STEP Q :
      gen_requester_learn m γ STEP P Q |-- gen_requester m γ STEP Q.
    Proof. by apply: gen_requester_learn_mono. Qed.

    Lemma requester_gen_requester γ STEP Q :
      requester γ STEP Q |-- gen_requester masks.default γ STEP Q.
    Proof.
      iIntros "ac".
      iAcIntro; rewrite /gen_requester /requester /commit_acc /=.
      iMod "ac" as (s0) "((F & %HI) & W) /="; iModIntro.
      iExists {[s0]}. rewrite /AuthSet.frag_exact. iFrame "F".
      iSplitR. { iIntros "!%". set_solver. }
      iIntros "%ev [%Hin F]".
      iApply "W". iFrame (Hin).
      rewrite (_:
        {[ s' | (∃ s : lts_state (lts x), s ∈ {[s0]} ∧ lts_step (lts x) s (Some ev) s' ∧ True)%type ]}
        ≡ {[ s' | lts_step (lts x) s0 (Some ev) s' ]});
        first by iFrame.
      set_solver.
    Qed.

    Lemma gen_committer_committer γ STEP Q :
      gen_committer masks.default γ STEP Q |-- committer γ STEP Q.
    Proof.
      iIntros "AU".
      rewrite /gen_committer /committer.
      iAuIntro; rewrite /atomic_acc/=.
      iMod "AU" as (sset) "[A Close]".
      iExists sset. iFrame "A".
      iIntros "!>". iSplit.
      { (* abort *)
        iDestruct "Close" as "[Close _]". by iApply "Close". }
      iDestruct "Close" as "[_ Close]".
      iIntros (s e s') "[%HI A]".
      iApply "Close".
      rewrite /AuthSet.auth_exact. iFrame "A".
      iIntros "!%". set_solver.
    Qed.

    (* [gen_committer] is stronger than [alt_gen_committer] in that
    [gen_committer] allows peeking.
    Meanwhile, the reverse direction needs to know the refinement invariant. *)
    Lemma gen_committer_alt_gen_committer `{!BiBUpdFUpd PROP} m γ STEP Q :
      gen_committer m γ STEP Q |-- alt_gen_committer m γ STEP Q.
    Proof.
      iIntros "AU".
      rewrite /gen_committer /alt_gen_committer.
      iIntros (sset0) "F".
      iMod "AU" as (sset) "[A [_ Close]]".
      iDestruct (observe_2 [| sset0 ⊆ sset |] with "F A") as "%sub".
      iIntros "!>". iExists sset. iSplit; first done.
      iIntros (sset' e) "H".
      iMod (AuthSet.frag_auth_upd with "F A") as "[$ A]".
      iMod ("Close" $! sset' e with "[$A $H]") as "$".
      done.
    Qed.

    #[global] Instance committer_proper γ :
      Proper ((≡) ==> pointwise_relation _ (≡) ==> (≡)) (committer γ).
    Proof.
      rewrite /committer => S1 S2 HS Q1 Q2 HQ.
      (* TODO AUTO: [solve_proper_tidy] calls [solve_proper_prepare] twice hence unfolds sealing wrappers. *)
      f_equiv; solve_proper_tidy.
    Qed.

    #[global] Instance requester_proper γ :
      Proper ((≡) ==> pointwise_relation _ (≡) ==> (≡)) (requester γ).
    Proof.
      rewrite /requester => S1 S2 HS Q1 Q2 HQ.
      repeat f_equiv_tidy; trivial.
      apply iff_forall => i. by rewrite HS.
    Qed.

    #[global] Instance gen_committer_proper m γ :
      Proper ((≡) ==> pointwise_relation _ (≡) ==> (≡)) (gen_committer m γ).
    Proof.
      rewrite /gen_committer => S1 S2 HS Q1 Q2 HQ.
      (* TODO AUTO: [solve_proper_tidy] calls [solve_proper_prepare] twice hence unfolds sealing wrappers. *)
      f_equiv; solve_proper_tidy.
    Qed.

    #[global] Instance gen_requester_learn_proper m γ :
      Proper  ((≡) ==> (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (≡))))
                   ==> pointwise_relation _ (≡) ==> (≡))
              (gen_requester_learn m γ).
    Proof.
      rewrite /gen_requester_learn => S1 S2 HS P1 P2 HP Q1 Q2 HQ.
      do 3 f_equiv_tidy; try trivial.
      - repeat f_equiv_tidy. set_solver.
      - f_equiv; first by rewrite HS.
        f_equiv. set_solver.
    Qed.
    #[global] Instance gen_requester_proper m γ :
      Proper ((≡) ==> pointwise_relation _ (≡) ==> (≡)) (gen_requester m γ).
    Proof. rewrite /gen_requester. solve_proper. Qed.

    (** Stronger than the "obvious" statement thanks to the extra [e ∈ STEP]
    assumption in the hypothesis. *)
    Lemma requester_proper_strong γ (STEP : propset (App.evt x)) :
      Proper ((fun f g => forall e, e ∈ STEP -> f e ≡ g e) ==> (≡))
            (requester γ STEP).
    Proof.
      rewrite /requester => Q1 Q2 HQ.
      rewrite atomic_commit_eq /atomic_commit_def /commit_acc /=.
      do 6 f_equiv.
      rewrite -!bi.wand_curry; apply /bi.equiv_wand_iff_l. iIntros (?).
      iApply bi.equiv_wand_iff. do 2 f_equiv; exact: HQ.
    Qed.

    (** Stronger than the "obvious" statement thanks to the extra [e ∈ STEP]
    assumption in the hypothesis. *)
    Lemma committer_proper_strong γ (STEP : propset (App.evt x)) :
      Proper ((fun f g => forall e, e ∈ STEP -> f e ≡ g e) ==> (≡))
            (committer γ STEP).
    Proof.
      rewrite /committer => Q1 Q2 HQ.
      rewrite atomic.atomic_update_unseal /atomic.atomic_update_def.
      rewrite /atomic_update_pre /atomic_acc /=.
      do 14 f_equiv.
      rewrite -!bi.wand_curry; apply /bi.equiv_wand_iff_l; iIntros ([? []]).
      iApply bi.equiv_wand_iff. do 2 f_equiv; exact: HQ.
    Qed.

    Lemma gen_requester_learn_proper_strong m γ (STEP : propset (App.evt x)) :
      Proper ((pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (≡))))
              ==> (fun f g => forall e, e ∈ STEP -> f e ≡ g e) ==> (≡))
            (gen_requester_learn m γ STEP).
    Proof.
      rewrite /gen_requester_learn => P1 P2 HP Q1 Q2 HQ.
      rewrite atomic_commit_eq /atomic_commit_def /commit_acc /=.
      do 6 f_equiv.
      - f_equiv. f_equiv_tidy. set_solver.
      - rewrite -!bi.wand_curry; apply /bi.equiv_wand_iff_l. iIntros (?).
        iApply bi.equiv_wand_iff. f_equiv.
        + f_equiv. f_equiv_tidy. set_solver.
        + f_equiv. exact: HQ.
    Qed.

    Lemma gen_requester_proper_strong m γ (STEP : propset (App.evt x)) :
      Proper ((fun f g => forall e, e ∈ STEP -> f e ≡ g e) ==> (≡))
            (gen_requester m γ STEP).
    Proof. by apply gen_requester_learn_proper_strong. Qed.

    (** Stronger than the "obvious" statement thanks to the extra [e ∈ STEP]
    assumption in the hypothesis. *)
    Lemma gen_committer_proper_strong m γ (STEP : propset (App.evt x)) :
      Proper ((fun f g => forall e, e ∈ STEP -> f e ≡ g e) ==> (≡))
            (gen_committer m γ STEP).
    Proof.
      rewrite /gen_committer => Q1 Q2 HQ.
      rewrite atomic.atomic_update_unseal /atomic.atomic_update_def.
      rewrite /atomic_update_pre /atomic_acc /=.
      do 12 f_equiv.
      rewrite -!bi.wand_curry; apply /bi.equiv_wand_iff_l. iIntros (?).
      iApply bi.equiv_wand_iff. do 4 f_equiv; exact: HQ.
    Qed.

    #[global] Instance alt_gen_committer_proper m γ :
      Proper ((≡) ==> pointwise_relation _ (≡) ==> (≡)) (alt_gen_committer m γ).
    Proof. rewrite /alt_gen_committer. solve_proper. Qed.

    (** Stronger than the "obvious" statement thanks to the extra [e ∈ STEP]
    assumption in the hypothesis. *)
    Lemma alt_gen_committer_proper_strong m γ (STEP : propset (App.evt x)) :
      Proper ((fun f g => forall e, e ∈ STEP -> f e ≡ g e) ==> (≡))
            (alt_gen_committer m γ STEP).
    Proof.
      rewrite /alt_gen_committer => Q1 Q2 HQ.
      do 11 f_equiv.
      rewrite -!bi.wand_curry; apply /bi.equiv_wand_iff_l. iIntros (?).
      iApply bi.equiv_wand_iff. do 4 f_equiv; exact: HQ.
    Qed.

    Lemma committer_post_mono g STEP Q1 Q2 :
      committer g STEP Q1 -∗
      (∀ e, Q1 e -∗ Q2 e) -∗
      committer g STEP Q2.
    Proof.
      iIntros "C W". iApply (aupd_ppost_wand with "C"). iIntros (????). iApply "W".
    Qed.

    Lemma gen_committer_post_mono m g STEP Q1 Q2 :
      gen_committer m g STEP Q1 -∗
      (∀ e, Q1 e -∗ Q2 e) -∗
      gen_committer m g STEP Q2.
    Proof.
      iIntros "C W". iApply (aupd_ppost_wand with "C"). iIntros (???). iApply "W".
    Qed.
  End with_app.

  #[global] Notation properC := committer_proper_strong.

  #[global] Hint Opaque
    requester committer updater
    gen_requester gen_committer
  : br_opacity.
End Step.

(*** Satisfiability
  
  We provide a simple invariant to demonstrate that Spectra is satisfiable.
  The definition of [root_inv] below bundles the authoritative state of
  the LTS but does **not** connect it to the physical state of the system,
  which is necessary to use Spectra to prove an actual refinement.
  
  In order to connect to the physical state, the WP of the physical system
  must expose the visible events that it takes (which can be exposed as a trace).
  Using this trace we can construct a true root invariant by bundling the physical
  trace into the root invariant anc connecting it to the trace [evts] in [root_inv].
  With this, unpacking this invariant allows us to prove the standard
  termination-insensitive refinement property characterized by trace equivalence
  up to stuttering.
 *)
Section with_app.
  Import App.

  Context `{Ghostly PROP} `{!BiFUpd PROP} `{!BiBUpdFUpd PROP}.
  Context `{root : !App.app, E : coPset}.

  Definition root_inv ns γroot :=
    inv ns $
      Exists root_set init_st,
        AuthSet.auth γroot root_set **
        [| ∃ s, s ∈ root_set |] **
        [| root.(lts).(Sts._init_state) init_st |] **
        [| ∀ s, s ∈ root_set ->
           ∃ evts, reachable root.(lts) init_st evts s |].

  (** why is [inh] needed even though [root_inv] already asserts something stronger?
      opening the invariant results in a later. to move the later inside using [bi.later_exist],
      we need that the type is inhabited.
  *)
  Lemma alloc_updater ns γroot {inh: Inhabited (root.(lts).(Sts._state))}:
    root_inv ns γroot |-- Step.updater root (↑ns) γroot.
  Proof using All.
    iIntros "#inv". rewrite Step.updater_unseal.
    iIntros "!#" (sset nonempty safe) "frag".
    case: nonempty => s nonempty; case: (safe s nonempty) => s' step.
    iInv "inv" as (sset' inits) "(>auth & FACTS)" "Close".
    iDestruct (observe_2 [| sset ⊆ sset' |] with "frag auth") as "%sub".
    set (sset'' := {[ s' | exists s, s ∈ sset /\ root.(lts).(lts_step) s None s' ]}).
    have nonempty'' : exists s, s ∈ sset''.
    { exists s'. rewrite /sset'' elem_of_PropSet. exists s. by split. }
    iMod (AuthSet.frag_auth_upd γroot sset'' with "frag auth") as "($ & auth')".
    iApply ("Close" with "[auth' FACTS]").
    { iExists sset''. iModIntro. iFrame.
      iDestruct "FACTS" as %(? & ? & reach).
      have reach'' :
        forall s, s ∈ sset'' ->
        exists evts, reachable root.(lts) inits evts s.
      { rewrite /sset'' => s0. rewrite elem_of_PropSet. case => sx []Hin Hstep.
        apply sub in Hin. case: (reach _ Hin) => evts Hreach.
        exists (evts ++ [None]). by econstructor. }
      by iExists inits. }
  Qed.
End with_app.

Import Sts.
(*** App Composition *)
Module ComposeN.

  Module Σ.
    (** [G Σ fam] bundles the requirements that Σ contains all CMRAs
    all constituent LTSes as well as the composed LTS. *)
    Class G {Σ : gFunctors} (fam : Compose.config) := {
      #[global] comp_inG ::
        ∀ n : Compose.name fam,
          inG Σ (auth_setR (_state (_sts (Compose.sts_name _  n)))) ;
      #[global] whole_inG :: inG Σ (auth_setR (Compose.State fam)) ;
    }.
    #[global] Arguments G : clear implicits.

    (** This also bundles the Compose.config itself *)
    Class compose {Σ : gFunctors} := mk {
      fam : Compose.config;
      #[global] allGs :: G Σ fam;

      app := {| App.Σ.lts := Compose.compose_lts fam  |} ;
    }.
    #[global] Arguments compose : clear implicits.
  End Σ.

  (* BI-general version of Σ.G *)
  Class G `{Ghostly PROP} (fam : Compose.config) := {
    #[global] inGs ::
      ∀ n : Compose.name fam,
        HasUsualOwn PROP (auth_setR (_state (_sts (Compose.sts_name _  n)))) ;
    #[global] inG :: HasUsualOwn PROP (auth_setR (Compose.State fam))
  }.
  (* BI-general version of Σ.compose *)
  Class compose `{Ghostly PROP} := mk {
    fam : Compose.config;
    #[global] ings :: G fam;

    app := {| App.lts := Compose.compose_lts fam |} ;
  }.
  #[global] Arguments compose {_ _}.

  Definition nsName {fam : Compose.config} (n : Compose.name fam) :=
    match list_find (λ e : Compose.name fam, n = e) (enum (Compose.name fam)) with
    | Some (index, _) => BS.of_N_decimal (N.of_nat index)
    | None => ("")%bs
    end.
End ComposeN.

Section updl.
  Import EqNotations.
  Context `{Finite Nm} {nl : Nm}.
  Context {P : Nm -> Type} (slr_set : ∀ x : Nm, P x) (sl : P nl).
  Definition updl (n : Nm) : P n :=
    match decide (nl = n) return P n with
    | left peq =>  rew peq in sl
    | right _ => slr_set n
    end.

  Lemma updll : updl nl = sl.
  Proof.
    rewrite /updl.
    case_decide as E; last done.
    by rewrite (proof_irrel E eq_refl).
  Qed.
End updl.

Section updlr.
  Context `{Finite Nm} {nl : Nm} {nr : Nm}.
  Import EqNotations.

  Definition updlr {P : Nm -> Type}
      (slr_set : ∀ x : Nm, P x) (sl : P nl) (sr : P nr) (n : Nm) : P n:=
    updl (updl slr_set sr) sl n.

  Lemma updlrl {P : Nm -> Type} (slr_set : ∀ x : Nm, P x) (sl : P nl) (sr : P nr) :
    updlr slr_set sl sr nl = sl.
  Proof. apply updll. Qed.

  Section neq.
    Hypothesis (neq : nl <> nr).

    Lemma updlo {P : Nm -> Type} (slr_set : ∀ x : Nm, P x) (sl : P nl):
      updl slr_set sl nr = slr_set nr.
    Proof using neq. rewrite /updl. case_decide; done. Qed.

    Lemma updlrr {P : Nm -> Type} (slr_set : ∀ x : Nm, P x) (sl : P nl) (sr : P nr):
      updlr slr_set sl sr nr = sr.
    Proof using neq. by rewrite /updlr updlo updll. Qed.
  End neq.
End updlr.

Section updlro.
  Context `{Finite Nm} {nl : Nm} {nr : Nm}.
  Lemma updlro {P: Nm -> Type}
      (slr_set : ∀ x : Nm, P x) (sl : P nl) (sr : P nr) (n : Nm) :
    n <> nl -> n <> nr ->
    updlr slr_set sl sr n = slr_set n.
  Proof. intros Hl hr. by rewrite /updlr !updlo. Qed.
End updlro.

Import App.
Import ComposeN.

Section with_lts.
  Context `{Ghostly PROP} `{!BiFUpd PROP} `{!BiBUpdFUpd PROP}.
  Context `{!ComposeN.compose}.
  #[local] Notation T := (Compose.State ComposeN.fam).
  #[local] Notation Nm := (Compose.name ComposeN.fam).

  Notation dual_evts a b :=  (Compose.cancel_evt fam _ _ a b).

  Definition external_event_sets
      (n : Nm) (STEP : propset (Label (Compose.sts_name _ n)))
      (STEPup : propset (Compose.external_event ComposeN.fam)) : Prop :=
    (∀ e, e ∈ STEP -> ∃ eup, eup ∈ STEPup /\ Compose.inj_evt fam _ e = Some eup) /\
    (∀ eup, eup ∈ STEPup -> ∃ e, e ∈ STEP /\ Compose.inj_evt fam _ e = Some eup).

  Definition appn (n: Nm): App.app :=
    {| evt := Label (Compose.sts_name fam n); lts := Compose.sts_name fam n; App.inG := inGs n |}.

  (*** Transports *)

  Section with_refinement.
    Context {R : refinement}.

    Definition gen_transports γ : PROP :=
      □ ∀ (nl nr : Nm) (diff : nl <> nr)
          (STEPl : propset (Label (Compose.sts_name _ nl)))
          (STEPr : propset (Label (Compose.sts_name _ nr)))
          (dual : Compose.dual_sets ComposeN.fam STEPl STEPr) Q m,
            Step.gen_requester (appn nl) refinement_cur m (γ nl) STEPl Q -∗
            Step.gen_committer (appn nr) refinement_cur m (γ nr) STEPr
              (fun e2 => Exists e1, [| e1 ∈ STEPl /\ dual_evts e1 e2 |] ** Q e1).

    #[global] Instance gen_transports_knowledge : Knowledge1 gen_transports.
    Proof. solve_knowledge. Qed.

    Definition external_requests γ γup : PROP :=
      □ ∀ (n : Nm)
        (STEP : propset (Label (Compose.sts_name _ n)))
        (STEPup : propset (Compose.external_event ComposeN.fam))
        (EXT : external_event_sets n STEP STEPup)
        Q m,
        Step.gen_requester (appn n) (refinement_cur ∪ refinement_up) m (γ n) STEP Q -∗
        Step.gen_requester app refinement_up m γup STEPup
          (λ eup, ∃ e, [| e ∈ STEP |] ** [| Compose.inj_evt fam _ e = Some eup |] ** Q e).

    #[global] Instance external_requests_knowledge : Knowledge2 external_requests.
    Proof. solve_knowledge. Qed.

    Definition external_commits γ γup : PROP :=
      □ ∀ (n : Nm)
        (STEP : propset (Label (Compose.sts_name _ n)))
        (STEPup : propset (Compose.external_event ComposeN.fam))
        (EXT : external_event_sets n STEP STEPup)
        Q m,
        Step.gen_committer app refinement_up m γup STEPup Q -∗
        Step.gen_committer (appn n) (refinement_cur ∪ refinement_up) m (γ n) STEP
          (λ e, ∃ eup, [| eup ∈ STEPup |] ** [| Compose.inj_evt fam _ e = Some eup |] ** Q eup).

    #[global] Instance external_commits_knowledge : Knowledge2 external_commits.
    Proof. solve_knowledge. Qed.
  End with_refinement.

  (*** Decomposition Invariant *)

  Let all_names := (enum Nm).

  Definition decomp_aux sets (γ: Nm -> _) γup : PROP :=
    ([∗list] n ∈ all_names, AuthSet.auth (γ n) (sets n)) **
    AuthSet.frag γup (π_set sets) **
    [| exists s, s ∈ (π_set sets) |].

  Definition Decomp_def (γ: Nm -> _) γup : PROP := Exists sets, decomp_aux sets γ γup.

  Definition Decompose (ns : namespace) γ (γup : AuthSet.gname) : PROP :=
    inv ns (Decomp_def γ γup).

  Lemma alloc_decomp_aux γup sets (_ : exists s, s ∈ π_set sets) :
    AuthSet.frag γup (π_set sets)
    |-- |={∅}=>
    ∃ (γ : Nm -> AuthSet.gname),
      ([∗list] n ∈ all_names, AuthSet.frag (γ n) (sets n)) **
      decomp_aux sets γ γup.
  Proof using All.
    rewrite /Decompose /Decomp_def /decomp_aux.
    have nd : NoDup all_names := NoDup_enum Nm.
    induction all_names.
    { iIntros "/= ? !>". iExists (fun _ => γup). by iFrame. }
    apply NoDup_cons in nd as [? ND].
    specialize (IHl ND).
    rewrite {1}IHl /=.
    iMod 1 as (f) "(H1 & H2 & $ & %Hex)". iFrame (Hex).
    iMod (AuthSet.alloc (T:=(Compose.sts_name ComposeN.fam a).(lts_state)) (sets a))
      as (γa) "(? & ?)".
    iModIntro.
    iExists (fun (n:Nm) => if decide (n=a) then γa else f n).
    rewrite decide_True //. iFrame.
    iCombine "H1 H2" as "H".
    rewrite -!big_sepL_sep.
    iApply (big_sepL_mono with "H").
    intros ? ? Hin%elem_of_list_lookup_2.
    rewrite decide_False; [done|congruence].
  Qed.

  (*** Internal Lemmas *)
  Section comp.
    Instance: Inhabited (∀ x : Nm, propset (Compose.sts_name fam x)) :=
      populate (fun _ => ∅).

    Context {nl : Nm}.
    Let left := appn nl.

    Context `{!Timeless (emp%I : PROP)}.

    #[local] Arguments eq_rect_r /.
    #[local] Opaque lts_step.
    #[local] Transparent decomp_aux.

    (* Turning a subcomponent's requester into the parent's requester that
    makes an event externally visible outside the parent component.
    This allows a request to bubble up. *)
    Lemma gen_requester_visible
        (STEP : propset (Label (Compose.sts_name _ nl)))
        (STEPup : propset (evt app))
        ns (E : coPset) m (_ : ↑ns ## E) (_ : ↑ns ⊆ masks.O m)
        (up_events :
          (∀ l, l ∈ STEP -> ∃ lup, lup ∈ STEPup /\ Compose.inj_evt fam _ l = Some lup) /\
          (∀ lup, lup ∈ STEPup -> ∃ l, l ∈ STEP /\ Compose.inj_evt fam _ l = Some lup))
        γ γup (Q : evt left -> PROP) :
      (* Decompose invariant: *)
      Decompose ns γ γup -∗
      (* Subcomponent Requester *)
      Step.gen_requester left (↑ns ∪ E) m (γ nl) STEP Q -∗
      (* Whole component Requester *)
      Step.gen_requester app E m γup STEPup
        (λ eup, ∃ e, [| e ∈ STEP |] ** [| Compose.inj_evt fam _ e = Some eup |] ** Q e).
    Proof using All.
      iIntros "#inv REQ".
      rewrite /Step.gen_requester /Decompose /Decomp_def/decomp_aux.
      iAcIntro; rewrite /commit_acc/=.
      iInv "inv" as (slr_set) "(>A & >Fup & >%NEup)" "Close".
      iMod "REQ" as (ssl) "((Fl & %NEl & %STEPl) & Q)".
      rewrite (big_sepL_difference_singleton nl); [|apply elem_of_enum|apply NoDup_enum].
      iDestruct "A" as "[Al A]".
      iDestruct (observe_2 [| ssl ⊆ slr_set nl |] with "Fl Al")
        as "%s1_in_set".

      set sset := π_set (updl slr_set ssl).
      assert (NEsset : ∃ s, s ∈ sset).
      { destruct NEup as [s INs]. destruct NEl as [sl Insl]. exists (updl s sl).
        rewrite /sset /updl /= elem_of_PropSet.
        intros d. case_decide; set_solver. }
      iMod (AuthSet.frag_upd γup sset with "Fup") as "Fup".
      { clear -s1_in_set. intros s0.
        rewrite /π_set/= !elem_of_PropSet.
        intros INn n. move : (INn n).
        rewrite /updl. repeat case_decide; subst; simpl; set_solver. }
      iIntros "!>".
      iExists sset. iFrame (NEsset) "Fup".

      destruct up_events as [UP1 UP2].
      iSplitR.
      { iIntros "!%" (s e Inss Ine).
        destruct (UP2 _ Ine) as (el & Inel & Injel).
        destruct (STEPl (s nl) el) as [sl' [stepL _]]; [|done|].
        { move : (Inss nl). by rewrite updll. }
        exists (updl s sl'). split; [|done]. exists nl. split.
        - (* TODO lemma *) rewrite /updl.
          intros n'. rewrite elem_of_list_singleton => NEq. by case_decide.
        - exists el. split; [done|]. by rewrite updll. }

      iIntros (e) "[%INe Fup]".

      destruct (UP2 _ INe) as (el & Inel & Injel).
      set ssl' := {[ s' | (∃ s, s ∈ ssl ∧ lts_step (Compose.sts_name fam nl) s (Some el) s' ∧ True)%type ]}.
      iMod (AuthSet.frag_auth_upd _ ssl' with "Fl Al") as "[Fl Al]".

      iMod ("Q" with "[$Fl //]") as "Q".
      iMod ("Close" with "[> A Fup Al]") as "_"; last first.
      { iIntros "!>". iExists el. by iFrame. }
      set sset' := updl slr_set ssl'.
      iMod (AuthSet.frag_upd γup (π_set sset') with "Fup") as "Fup".
      { intros s. rewrite !elem_of_PropSet.
        intros Ins.
        move : (Ins nl). rewrite /sset' updll elem_of_PropSet.
        intros (sl & Insl & stepL & _).
        exists (updl s sl). split.
        - apply elem_of_PropSet. intros d.
          case (decide (d = nl)) => Eqnl.
          + subst d. by rewrite !updll.
          + move : (Ins d). by rewrite /sset' !updlo //.
        - split; [|done]. exists nl. split.
          + (* TODO lemma *) rewrite /updl.
            intros n'. rewrite elem_of_list_singleton => NEq. by case_decide.
          + exists el. split; [done|]. by rewrite updll. }

      iIntros "!> !>". iExists _. iFrame "Fup".
      iSplitL; last first.
      { iIntros "!%".
        destruct NEup as [s INs]. destruct NEl as [sl Insl].
        destruct (STEPl sl el) as [sl' stepL]; [done..|].
        exists (updl s sl').
        apply elem_of_PropSet => d.
        case (decide (d = nl)) => Eqd.
        - subst d. rewrite /sset' !updll.
          apply elem_of_PropSet. by eexists.
        - rewrite /sset' !updlo //. set_solver+INs. }

      rewrite (big_sepL_difference_singleton nl _ all_names); [|apply elem_of_enum|apply NoDup_enum].
      iSplitL "Al".
      { rewrite /sset' updll. by iFrame "Al". }
      iApply (big_sepL_mono with "A").
      intros i n [INn EqL]%elem_of_list_lookup_2%elem_of_list_difference.
      rewrite elem_of_list_singleton in EqL.
      by rewrite /sset' updlo.
    Qed.

    (* Turning a parent's committer into a subcomponent's committer that
    makes an event externally visible outside the parent component.
    This allows a commiter to flow down. *)
    Lemma gen_committer_visible
        (STEP : propset (Label (Compose.sts_name _ nl)))
        (STEPup : propset (evt app))
        ns (E : coPset) m (_ : ↑ns ## E) (_ : ↑ns ⊆ masks.O m)
        (up_events :
          (∀ l, l ∈ STEP -> ∃ lup, lup ∈ STEPup /\ Compose.inj_evt fam _ l = Some lup) /\
          (∀ lup, lup ∈ STEPup -> ∃ l, l ∈ STEP /\ Compose.inj_evt fam _ l = Some lup))
        γ γup
        (Q : evt app -> PROP) :
      (* Decompose invariant: *)
      Decompose ns γ γup -∗
      (* Parent committer *)
      Step.gen_committer app E m γup STEPup Q -∗
      (* Child committer *)
      Step.gen_committer left (↑ns ∪ E) m (γ nl) STEP
        (λ e, ∃ eup, [| eup ∈ STEPup |] ** [| Compose.inj_evt fam _ e = Some eup |] ** Q eup).
    Proof using All.
      iIntros "#inv COM".
      rewrite /Step.gen_committer /Decompose /Decomp_def/decomp_aux.
      iAuIntro; rewrite /atomic_acc.
      iMod "COM" as (slr_frag) "[Aup Close]".
      iInv "inv" as (slr_set) "(>A & >Fup & >%NEup)" "CloseI".
      rewrite (big_sepL_difference_singleton nl); [|apply elem_of_enum|apply NoDup_enum].
      iDestruct "A" as "[Al A]".
      rewrite difference_difference_l_L union_comm_L.
      iDestruct (observe_2 [| (π_set slr_set) ⊆ slr_frag |] with "Fup Aup")
        as "%SUBsup".
      iIntros "!>".
      iExists _. iFrame "Al". iSplit.
      { (* abort *)
        iIntros "Al".
        iMod ("CloseI" with "[A Fup Al]").
        { iIntros "!>". iExists _. iFrame (NEup) "Fup".
          rewrite (big_sepL_difference_singleton nl _ all_names);
            [|apply elem_of_enum|apply NoDup_enum].
          iFrame. }
        iDestruct "Close" as "[Close _]".
        by iApply ("Close" with "Aup"). }
      (* commit *)
      iIntros (ssl' el) "(%Inel & %NEl' & %stepL' & Al)".
      iDestruct "Close" as "[_ Close]".

      set sset' := updl slr_set ssl'.
      iMod (AuthSet.frag_auth_upd _ (π_set sset') with "Fup Aup") as "[Fup Aup]".

      destruct up_events as [UP1 UP2].
      destruct (UP1 _ Inel) as (eup & Ineup & Injel).
      assert (NE' : ∃ s, s ∈ (π_set sset')).
      { destruct NEl' as [sl' Insl'].
        destruct NEup as [s Ins].
        exists (updl s sl').
        apply elem_of_PropSet.
        intros d. case (decide (d = nl)) => Eqd.
        - subst d. by rewrite /sset' !updll.
        - rewrite /sset' !updlo //. set_solver +Ins. }

      iMod ("CloseI" with "[A Fup Al]").
      { iIntros "!>". iFrame (NE') "Fup".
        rewrite (big_sepL_difference_singleton nl _ all_names);
          [|apply elem_of_enum|apply NoDup_enum].
        iSplitL "Al". { rewrite /sset' updll. iFrame "Al". }
        iApply (big_sepL_mono with "A") .
        intros i n [INn EqL]%elem_of_list_lookup_2%elem_of_list_difference.
        rewrite elem_of_list_singleton in EqL.
        by rewrite /sset' updlo. }
      iMod ("Close" $! (π_set sset') eup with "[$Aup]") as "Q".
      { iIntros "!%"; repeat split; [done..|].
        iIntros (s' Ins').
        destruct (stepL' (s' nl)) as (sl & Insl & stepL).
        { move : (Ins' nl). by rewrite /sset' updll. }
        exists (updl s' sl). split.
        - apply SUBsup.
          apply elem_of_PropSet. intros d.
          case (decide (d = nl)) => Eqd.
          + subst d. by rewrite /sset' !updll.
          + move : (Ins' d). rewrite /sset' !updlo //.
        - exists nl. split.
          + (* TODO lemma *) rewrite /updl.
            intros n'. rewrite elem_of_list_singleton => NEq. by case_decide.
          + exists el. split; [done|]. by rewrite updll. }
      iIntros "!>". iExists eup. by iFrame "Q %".
    Qed.

    (* Transporting a requester to a canceling committer. *)
    Lemma gen_transport1l
        {nr: Nm}
        (STEPl : propset (Label (Compose.sts_name _ nl)))
        (STEPr : propset (Label (Compose.sts_name _ nr)))
        (neq : nl <> nr)
        ns (E : coPset) m (_ : ↑ns ## E) (_ : ↑ns ⊆ masks.O m) (_ : E ⊆ masks.O m)
        (dual : Compose.dual_sets ComposeN.fam STEPl STEPr) γ γup Q :
      let right := appn nr in
      (* Decompose invariant: *)
      Decompose ns γ γup -∗
      Step.updater ComposeN.app E γup -∗
      (* Requester AC: *)
      Step.gen_requester left (↑ns) m (γ nl) STEPl Q -∗
      (* Committer AU: *)
      Step.gen_committer right (↑ns) m (γ nr) STEPr
        (fun e2 => Exists e1, [| e1 ∈ STEPl /\ dual_evts e1 e2 |] ** Q e1).
    Proof using All.
      iIntros (right) "#inv #updater REQ".
      rewrite /Step.gen_committer /Step.gen_requester /Decompose /Decomp_def/decomp_aux.
      iAuIntro; rewrite /atomic_acc/=.
      iInv "inv" as (slr_set) "(>aleftr & >up & >%nonempty)" "Close"; iModIntro.
      iExists (slr_set nr).
      pose proof (elem_of_enum nr).
      pose proof (elem_of_enum nl).
      rewrite -> big_sepL_difference_two with (x:= nl) (y:=nr); [|by eauto using NoDup_enum..].
      iDestruct "aleftr" as "[authl [$ authlist]]"; iSplit.
      { iIntros "authr". iFrame "REQ".
        iApply ("Close" with "[authlist authr up authl]").
        iFrame.
        rewrite (big_sepL_difference_two _ all_names nl nr);
          [|by eauto using NoDup_enum..].
        by iFrame.
      }
      iIntros (ssr' er) "(%evt & [(%sr' & %sr'_in_set) [%step_right authrf]])".
      (* the right side has already transitioned *)
      case: dual => duall dualr.
      case: (dualr er evt) => el []elin ?.
      iMod "REQ" as (ssl) "((fragl & %step_left) & Q)".
      destruct step_left as [NEl step_left].
      iDestruct (observe_2 [| ssl ⊆ slr_set nl |] with "fragl authl")
        as "%s1_in_set".
      set ssl' := {[ s' | (∃ s : Compose.sts_name fam nl, s ∈ ssl ∧ lts_step (Compose.sts_name fam nl) s (Some el) s' ∧ True)%type ]}.
      iMod (AuthSet.frag_auth_upd (γ nl) ssl' with "fragl authl") as "(fraglf & authlf)".
      iMod ("Q" $! el with "[$fraglf //]") as "M".

      set ssr := {[ s | s ∈ slr_set nr ∧ ∃ s', s' ∈ ssr' /\ lts_step (Compose.sts_name fam nr) s (Some er) s' ]}.
      set sset := π_set (updlr slr_set ssl ssr).
      iMod (AuthSet.frag_upd γup sset with "up") as "up"; eauto.
      { clear -s1_in_set. intros s0.
        rewrite /π_set/= !elem_of_PropSet.
        intros INn n. move : (INn n).
        rewrite /updlr /updl.
        repeat case_decide; subst; simpl; set_solver. }

      destruct nonempty as [s0 NEs].
      destruct NEl as [sl0 NEl].
      destruct (step_right _ sr'_in_set) as (sr0 & NEr1 & NEr2).
      (* rewrite /π_set elem_of_PropSet in nonempty. *)
      have NONEMPTY_aux : updlr s0 sl0 sr0 ∈ sset.
      {
        rewrite /sset !elem_of_PropSet /updlr /updl. intros d.
        repeat case_decide; subst; simpl; eauto; set_solver. }
      have NONEMPTY: exists s0, s0 ∈ (sset : propset _). {
        eexists. apply NONEMPTY_aux. }
      have SAFE: Step.tau_safe (ComposeN.app).(lts) sset.
      {
        move=> sc /elem_of_PropSet Hin /=.
        have Hl := Hin nl. rewrite updlrl in Hl.
        destruct (step_left (sc nl) el) as [sll [STEPl' _]]; [done..|].

        have Hr := Hin nr.
        rewrite updlrr in Hr; last done.
        rewrite elem_of_PropSet in Hr.
        destruct Hr as (Hr & srr & Hr' & STEPr').
        exists (updlr sc sll srr).
        right.
        exists nl, nr, el, er.
        rewrite updlrl updlrr //.
        split_and!; auto.
        intros nn Hn.
        rewrite updlro; [done|..].
        all: set_solver + Hn. }

      rewrite Step.updater_unseal.
      iMod ("updater" $! _ NONEMPTY SAFE with "up") as "up".
      set slrf := updlr slr_set ssl' ssr'.
      simpl in slrf.
      iMod (AuthSet.frag_upd γup (π_set slrf) with "up") as "up".
      { intros scf. rewrite !elem_of_PropSet. intros Hin.
        have Hl := Hin nl. rewrite /slrf updlrl in Hl.
        rewrite elem_of_PropSet in Hl.
        destruct Hl as (sl1 & INsl1 & STEPl1 & _).

        have Hr := Hin nr. rewrite /slrf updlrr in Hr; last done.
        destruct (step_right _ Hr) as (sr1 & Insr1 & STEPr1).

        exists (updlr scf sl1 sr1). split.
        { rewrite /sset !elem_of_PropSet /updlr /updl.
          intros d. repeat case_decide; subst; simpl; try done.
          - apply elem_of_PropSet. naive_solver.
          - specialize (Hin d).
            rewrite /slrf updlro in Hin; auto. }

        simpl. right.
        exists nl, nr, el, er. simpl.
        rewrite updlrl updlrr //.
        split_and!; auto.
        intros nn Hn.
        rewrite updlro; [done|..].
        all: set_solver + Hn. }

      iExists el. iFrame.
      iEval (rewrite (comm_L union E) (difference_union_L _ E)).
      iMod ("Close" with "[authlf authrf up authlist]") as "_"; last done.
      iModIntro; iExists slrf.
      rewrite /AuthSet.auth_exact.
      iEval (rewrite -> big_sepL_difference_two with (x:= nl) (y:=nr); [|by eauto using NoDup_enum..]).
      rewrite /slrf updlrl updlrr //=.
      #[local] Opaque lts_step.
      rewrite big_sepL_mono_elem; [iFrame|]; last first.
      {
        intros ? Hin.
        rewrite -> elem_of_list_difference in Hin.
        rewrite updlro; try reflexivity; set_solver+ Hin.
      }
      iIntros "!%".

      destruct (step_left sl0 el) as [sl' STEPl']; [done..|].
      exists (updlr s0 sl' sr').
      rewrite !elem_of_PropSet /updlr /updl.
      intros d.
      repeat case_decide; subst; simpl; auto.
      - apply elem_of_PropSet. naive_solver.
      - set_solver.
    Qed.

    Lemma alt_gen_transport1l
        {nr: Nm}
        (STEPl : propset (Label (Compose.sts_name _ nl)))
        (STEPr : propset (Label (Compose.sts_name _ nr)))
        (neq : nl <> nr)
        ns (E : coPset) m (_ : ↑ns ## E) (_ : ↑ns ⊆ masks.O m) (_ : E ⊆ masks.O m)
        (dual : Compose.dual_sets ComposeN.fam STEPl STEPr) γ γup Q :
      let right := appn nr in
      (* Decompose invariant: *)
      Decompose ns γ γup -∗
      Step.updater ComposeN.app E γup -∗
      (* Requester AC: *)
      Step.gen_requester left (↑ns) m (γ nl) STEPl Q -∗
      (* Committer AU: *)
      Step.alt_gen_committer right (↑ns) m (γ nr) STEPr
        (fun e2 => Exists e1, [| e1 ∈ STEPl /\ dual_evts e1 e2 |] ** Q e1).
    Proof using All.
      iIntros (right) "#inv #updater REQ".
      iApply Step.gen_committer_alt_gen_committer.
      by iApply (gen_transport1l with "inv updater REQ").
    Qed.

    Lemma transport1l
        {nr: Nm}
        (STEPl : propset (Label (Compose.sts_name _ nl)))
        (STEPr : propset (Label (Compose.sts_name _ nr)))
        (neq : nl <> nr)
        ns (E : coPset) (_ : ↑ns ## E)
        (dual : Compose.dual_sets ComposeN.fam STEPl STEPr) γ γup Q :
      let right := appn nr in
      (*Decompose invariant:*)
      Decompose ns γ  γup -∗
        Step.updater ComposeN.app E γup -∗
        (*Requester AC:*)
        Step.requester left (↑ns) (γ nl) STEPl Q -∗
        (*Committer AU:*)
        Step.committer right (↑ns) (γ nr) STEPr
        (fun e2 => Exists e1, [| e1 ∈ STEPl /\ dual_evts e1 e2 |] ** Q e1).
    Proof using All.
      iIntros (right) "#inv #updater ac1". (* rename ac1 to requester *)
      iApply Step.gen_committer_committer.
      iApply (gen_transport1l with "inv updater"); [done..|].
      by iApply Step.requester_gen_requester.
    Qed.

    #[local] Lemma left_updater ns E (_ : ↑ns ## E) γ γup :
      Decompose ns γ γup -∗
      Step.updater ComposeN.app E γup -∗
      Step.updater left (↑ns ∪ E) (γ nl).
    Proof using All.
      iIntros "#inv #upd". rewrite 2!Step.updater_unseal.
      iIntros "!#" (setl nonemptyl safe) "fragl".
      iInv "inv" as (setlr) "(>aleftr & >up & >%nonempty)" "Close".
      rewrite union_minus_l_L difference_disjoint_L //.
      pose proof (finite.elem_of_enum nl).
      rewrite -> big_sepL_difference_singleton with (x:= nl); [|by eauto using NoDup_enum..].
      iDestruct "aleftr" as "[authl authlist]".

      iDestruct (observe_2 [| setl ⊆ setlr nl |] with "fragl authl")
        as "%sl_in_set".
      set (setle := (π_set (updl setlr setl))).
      iMod (AuthSet.frag_upd γup setle with "up") as "fragup".
      {
        intros ss.
        rewrite {}/setle /π_set /updl !elem_of_PropSet /=.
        move=> /[swap] d /(_ d).
        case_decide; simplify_eq/=; set_solver+ sl_in_set.
      }
      case: nonemptyl => slne nonemptyl.
      have NONEMPTY: exists s, s ∈ setle.
      { case: nonempty => snonempty nonempty.
        exists (updl snonempty slne).
        unfold setle, π_set, updl.
        revert nonempty.
        rewrite !elem_of_PropSet /=.
        intros ? d.
        case_decide; simplify_eq => //=.
      }
      have SAFE: Step.tau_safe (ComposeN.app).(lts) setle.
      {
        intros sc Hin%elem_of_PropSet.
        pose proof (Hin nl) as Hinl.
        rewrite updll in Hinl.
        destruct (safe (sc nl)) as [slf stepl]; auto;[].
        exists (updl sc slf).
        #[local] Transparent lts_step.
        simpl. left. exists nl.
        split;[ | rewrite updll; assumption].
        intros ? Hneq.
        rewrite updlo; set_solver+ Hneq.
      }

      iMod ("upd" $! setle NONEMPTY SAFE
        with "fragup") as "fragup".
      set (setlf := {[ slf | exists s1, s1 ∈ setl /\
                             lts_step (lts left) s1 None slf ]}).

      iMod (AuthSet.frag_auth_upd (γ nl) setlf with "fragl authl")
        as "(fragl & authl)".
      iMod (AuthSet.frag_upd γup (π_set (updl setlr setlf))
        with "fragup") as "fragup".
      { intros sc. rewrite /π_set /setlf /= !elem_of_PropSet /=.
        intros Hin.
        pose proof (Hin nl) as Hinl.
        rewrite updll elem_of_PropSet in Hinl.
        destruct Hinl as [sll Hinl].
        exists (updl sc sll).
        #[local] Transparent lts_step.
        split.
        {
          rewrite /setle /π_set /updl !elem_of_PropSet /=.
          intros d.
          specialize (Hin d).
          case_decide; [ | ].
          {
            subst. simpl.
            tauto.
          }
          {
            rewrite updlo in Hin; auto.
          }
        }
        left.
        exists nl.
        rewrite updll.
        split; [ | tauto].
        intros nn Hneq.
        rewrite updlo; set_solver+ Hneq.
      }
      iFrame.

      iMod ("Close" with "[authl fragup authlist]") as "_"; last by iModIntro.
      { iExists (updl setlr setlf).
        iFrame. iModIntro.
        #[local] Opaque lts_step.
        rewrite (big_sepL_difference_singleton nl _ all_names); [|by eauto using NoDup_enum..].
        rewrite !updll. iFrame. iSplitL.
        {
          iApply (big_sepL_mono_elem with "[$]").
          intros ? Hin.
          rewrite elem_of_list_difference in Hin.
          rewrite updlo; try reflexivity. set_solver+ Hin.
        }
        iPureIntro.
        destruct NONEMPTY as [sne NONEMPTY].
        destruct (safe slne) as [slf stepl]; auto;[].
        exists (updl sne slf).
        unfold setle in *.
        rewrite /π_set /setlf /updl !elem_of_PropSet /setlf /=.
        intros d. case_decide; subst; simpl.
        {
          rewrite !elem_of_PropSet /=. eauto.
        }
        rewrite /π_set elem_of_PropSet in NONEMPTY.
        specialize (NONEMPTY d).
        rewrite updlo in NONEMPTY; auto.
      }
    Qed.
  End comp.

    (** Decompose invariant is sufficient *)
  Section refine_inv.
    Context `{!Timeless (emp%I : PROP)}.
    Context {R : refinement}.

    Lemma refine_inv_gen_transports γ γup :
      Decompose refinement_ns γ γup -∗
      Step.updater ComposeN.app refinement_up γup -∗
      gen_transports γ.
    Proof using All.
      rewrite /gen_transports.
      iIntros "#INV #UPD !#" (nl nr NE STEPl STEPr DUAL Q m).
      iApply gen_transport1l; [done|..|done|done].
      - apply refinement_cur_up_disj.
      - solve_ndisj.
      - etrans; [apply refinement_up_sub|]. solve_ndisj.
      - done.
    Qed.

    Lemma refine_inv_requests γ γup :
      Decompose refinement_ns γ γup -∗
      external_requests γ γup.
    Proof using All.
      rewrite /external_requests.
      iIntros "#INV !#" (n STEPl STEPup UP Q m).
      iApply gen_requester_visible ; auto.
      - apply refinement_cur_up_disj.
      - solve_ndisj.
    Qed.

    Lemma refine_inv_commits γ γup :
      Decompose refinement_ns γ γup -∗
      external_commits γ γup.
    Proof using All.
      rewrite /external_commits.
      iIntros "#INV !#" (n STEPl STEPup UP Q m).
      iApply gen_committer_visible ; auto.
      - apply refinement_cur_up_disj.
      - solve_ndisj.
    Qed.

    (*** Decomposition

    This requires allocation of the decompose invariant, and the allocation
    lemmas are not bi-polymorphic.
    Here we assume a bi-specific [inv_alloc].
    *)
    Section with_inv_alloc.
      Hypothesis inv_alloc :
        ∀ γ γup (N : namespace) (E : coPset),
          ▷ Decomp_def γ γup ⊢ |={E}=> inv N (Decomp_def γ γup).

      Lemma alloc_decompose_bi ns γup sets (_ : exists s, s ∈ π_set sets) :
        AuthSet.frag γup (π_set sets) ={∅}=∗
        Exists (γ:Nm → AuthSet.gname),
          ([∗list] n ∈ all_names, AuthSet.frag (γ n) (sets n)) **
          Decompose ns γ γup.
      Proof using Type* inv_alloc.
        simpl in *.
        rewrite alloc_decomp_aux; [|done].
        iIntros ">(%γ & S & R)".
        iMod (inv_alloc _ _ ns ∅ with "[$R //]") as "Inv".
        iIntros "!>". iExists γ. by iFrame "S Inv".
      Qed.

      (** * Top-level theorem

      The following top-level theorem shows how to spawn apps in γ
      from a composed app γup. *)
      Lemma gen_decompose_bi
          γup sets (nonempty : exists s, s ∈ π_set sets) :
        (* Assume that the composed app is in state (π_set sets) ... *)
        AuthSet.frag γup (π_set sets) -∗
        (* ... and updater for the composed app (the composed app can take
          tau steps). *)
        Step.updater ComposeN.app refinement_up γup ={∅}=∗
        ∃ γ : Nm → AuthSet.gname,
          ([∗ list] n ∈ all_names,
              (* frag tokens for each constituent LTS *)
              AuthSet.frag (γ n) (sets n)
              (* and updater so it can make tau steps. *)
              ** Step.updater (appn n) (@refinement_up (go_down (ComposeN.nsName n) R)) (γ n))
          (* and proofs for making communication steps *)
          (* internal communication steps:
            a proof that for all sets of dual events [STEPr] and [STEPc],
            requester ACs for [STEPr] imply committer AUs for [STEPc]. *)
          ** gen_transports γ
          (* external communication requests:
            a proof that an external request from a constituent LTS can be turned into
            an external request by the composed LTS. *)
          ** external_requests γ γup
          (* external communication commits:
            a proof that an external commit of the composed LTS can be turned into
            an external commit of the receiving constituent LTS. *)
          ** external_commits γ γup.
      Proof using Type* inv_alloc.
        iIntros "aup #upd".
        iMod (alloc_decompose_bi refinement_ns γup sets nonempty with "aup")
          as (γ) "(fr & #Inv)".
        iModIntro. iExists γ. rewrite big_sepL_sep. iFrame "fr". iSplitL.
        {
          iInduction all_names as [|x xs] "IHl"; simpl; [done|].
          iFrame "IHl".
          iApply (left_updater with "Inv upd").
          apply refinement_cur_up_disj.
        }
        iDestruct (refine_inv_gen_transports with "Inv upd") as "$".
        iDestruct (refine_inv_requests with "Inv") as "$".
        iDestruct (refine_inv_commits with "Inv") as "$".
      Qed.

    End with_inv_alloc.
  End refine_inv.
End with_lts.
#[global] Hint Opaque
  gen_transports external_requests external_commits
: br_opacity typeclass_instances.

#[global] Arguments gen_transports {_ _ _} comp {_} _ : rename.


(** * Singleton and Constructor Requesters/Committers *)

Lemma updater_singleton `{Ghostly PROP} `{!BiFUpd PROP} `{!BiBUpdFUpd PROP}
    `{app : !App.app} E1 E2 γ (s1 s2 : App.lts app) :
  E1 ⊆ E2 →
  lts_step (App.lts app) s1 None s2 →
  Step.updater app E1 γ ⊢
  AuthSet.frag (T := App.lts app) γ {[ s1 ]} ={E2}=∗
  AuthSet.frag (T := App.lts app) γ {[ s2 ]} .
Proof.
  iIntros (HE Hstep) "#U R". rewrite Step.updater_unseal.
  iMod ("U" with "[%] [%] R") as "R"; [set_solver..|].
  iMod (AuthSet.frag_upd with "R") as "$"; [|done].
  set_solver.
Qed.

Section with_app.
  Context `{Ghostly PROP} `{!BiFUpd PROP}.
  Context `{app : !App.app, R : !refinement}.

  (*Specializes [Step.requester] to events [e] built by [Ctor]*)
  Definition ctor_requester (γ : AuthSet.gname)
      {A} (Ctor : A -> app.(App.evt)) (Q : A -> PROP) :=
    Step.requester app refinement_cur γ {[ e | exists x, e = Ctor x ]}
                   (fun e => Exists x, [| e = Ctor x |] ** Q x).

  Definition singleton_requester (γ : AuthSet.gname)
      (evt : app.(App.evt)) (Q : PROP) :=
    ctor_requester γ (fun _ : unit => evt) (fun _ => Q).

  Definition ctor_committer (γ : AuthSet.gname)
      {A} (Ctor : A -> app.(App.evt)) (Q : A -> PROP) :=
    Step.committer app refinement_cur γ {[ e | exists x, e = Ctor x ]}
                   (fun e => Exists x, [| e = Ctor x |] ** Q x).

  Definition singleton_committer (γ : AuthSet.gname)
      (evt : app.(App.evt)) (Q : PROP) :=
    ctor_committer γ (fun _ : unit => evt) (fun _ => Q).

  (* General in masks *)
  Definition gen_ctor_requester m (γ : AuthSet.gname)
      {A} (Ctor : A -> app.(App.evt)) (Q : A -> PROP) :=
    Step.gen_requester app refinement_cur m γ {[ e | exists x, e = Ctor x ]}
                   (fun e => Exists x, [| e = Ctor x |] ** Q x).

  Definition gen_singleton_requester m (γ : AuthSet.gname)
      (evt : app.(App.evt)) (Q : PROP) :=
    gen_ctor_requester m γ (fun _ : unit => evt) (fun _ => Q).

  Definition gen_ctor_committer m (γ : AuthSet.gname)
      {A} (Ctor : A -> app.(App.evt)) (Q : A -> PROP) :=
    Step.alt_gen_committer app refinement_cur m γ {[ e | exists x, e = Ctor x ]}
                   (fun e => Exists x, [| e = Ctor x |] ** Q x).

  Definition gen_singleton_committer m (γ : AuthSet.gname)
      (evt : app.(App.evt)) (Q : PROP) :=
    gen_ctor_committer m γ (fun _ : unit => evt) (fun _ => Q).


  Lemma ctor_requester_wand :
    forall {A} γ (K : A -> App.evt app) (Q Q' : A -> PROP),
      (Forall a, Q a -* Q' a)
      |-- ctor_requester γ K Q -* ctor_requester γ K Q'.
  Proof.
    iIntros (A γ K Q Q') "HQ I"; unfold ctor_requester, Step.requester.
    rewrite atomic_commit.atomic_commit_ppost_wand; iApply "I".
    iIntros (_ x) "H"; iDestruct "H" as (a) "[%HK Q]".
    iExists a; iFrame "%".
    by iApply "HQ".
  Qed.

  Lemma singleton_requester_wand :
    forall γ x (Q Q' : PROP),
      (Q -* Q')
      |-- singleton_requester γ x Q -* singleton_requester γ x Q'.
  Proof.
    iIntros (γ x Q Q') "HQ"; rewrite /singleton_requester.
    iApply ctor_requester_wand; by iIntros (_).
  Qed.

  #[local] Lemma simpl_cont {A} (Q : PROP) (evt e : A)  :
    e ∈@{propset A} {[evt]} →
    (∃ _ : (), [| e = evt |] ∗ Q) ⊣⊢ Q.
  Proof.
    move => /elem_of_singleton ->.
    by rewrite bi.exist_unit only_provable_True ?(left_id emp bi_sep).
  Qed.

  Lemma singleton_requester_equiv {evt} γ Q :
    singleton_requester γ evt Q ⊣⊢
    Step.requester app refinement_cur γ {[ evt ]} (fun _ => Q).
  Proof.
    rewrite /singleton_requester/ctor_requester propset_singleton_equiv_unit.
    exact /Step.requester_proper_strong /simpl_cont.
  Qed.

  Lemma singleton_requester_intro {evt} γ (Q : PROP) :
    AC << ∀ s : App.lts app, ∃ s' : App.lts app,
          [| lts_step (App.lts app) s (Some evt) s' |] ∗
          AuthSet.frag_exact γ s >> @ ⊤ ∖ refinement_cur, ∅
      << AuthSet.frag γ {[ s' | lts_step (App.lts app) s (Some evt) s' ]}, COMM Q >>
    ⊢ singleton_requester γ evt Q.
  Proof.
    iIntros "H". rewrite singleton_requester_equiv /Step.requester.
    iAcIntro; rewrite /commit_acc/=.
    iMod "H" as (s) "/= [(%s' & %Hstep & F) Fc]"; iModIntro.
    iExists s; iFrame "F".
    iSplitR.
    { iIntros "!%" (e ->%elem_of_singleton); by eexists. }
    iIntros (e) "[%Hin F]". move: Hin => /elem_of_singleton ->.
    iApply ("Fc" with "F").
  Qed.

  Lemma singleton_committer_equiv {evt} γ Q :
    singleton_committer γ evt Q ⊣⊢
    Step.committer app refinement_cur γ {[ evt ]} (fun _ => Q).
  Proof.
    rewrite /singleton_committer/ctor_committer propset_singleton_equiv_unit.
    exact /Step.committer_proper_strong /simpl_cont.
  Qed.

  (* Consider using [transport_singleton] instead *)
  Lemma singleton_committer_intro {evt} γ (Q : PROP) :
    AU <{
      ∃∃ sset : propset (App.lts app), AuthSet.auth γ sset
    }> @ ⊤, ⊤ ∖ refinement_cur <{
      ∀∀ (s : App.lts app) (s' : App.lts app),
      [| s ∈ sset ∧ lts_step (App.lts app) s (Some evt) s' |] ∗
        AuthSet.auth_exact γ s', COMM Q }>
    ⊢ singleton_committer γ evt Q.
  Proof.
    iIntros "H". rewrite singleton_committer_equiv /Step.committer.
    iAuIntro; rewrite /atomic_acc/=.
    iMod "H" as (sset) "/= [A Ac]"; iModIntro.
    iExists sset; iFrame "A".
    iApply (bi.and_parallel with "Ac"); iSplit; first iIntros "$".
    iIntros "Ac" (s e s'). iDestruct 1 as ((? & ->%elem_of_singleton & ?)) "A".
    iApply ("Ac" $! s s' with "[$A //]").
  Qed.

  Lemma gen_singleton_requester_equiv {evt} m γ Q :
    gen_singleton_requester m γ evt Q ⊣⊢
    Step.gen_requester app refinement_cur m γ {[ evt ]} (fun _ => Q).
  Proof.
    rewrite /gen_singleton_requester/gen_ctor_requester propset_singleton_equiv_unit.
    exact /Step.gen_requester_proper_strong /simpl_cont.
  Qed.

  Lemma gen_singleton_committer_equiv {evt} m γ Q :
    gen_singleton_committer m γ evt Q ⊣⊢
    Step.alt_gen_committer app refinement_cur m γ {[ evt ]} (fun _ => Q).
  Proof.
    rewrite /gen_singleton_committer/gen_ctor_committer propset_singleton_equiv_unit.
    exact /Step.alt_gen_committer_proper_strong /simpl_cont.
  Qed.

  Lemma gen_singleton_requester_intro {evt} m γ (Q : PROP) :
    AC << ∀ s : App.lts app, ∃ s' : App.lts app,
          [| lts_step (App.lts app) s (Some evt) s' |] ∗
          AuthSet.frag_exact γ s >> @ masks.O m ∖ refinement_cur, masks.I m
      << AuthSet.frag γ {[ s' | lts_step (App.lts app) s (Some evt) s' ]}, COMM Q >>
    ⊢ gen_singleton_requester m γ evt Q.
  Proof.
    iIntros "H". rewrite gen_singleton_requester_equiv /Step.gen_requester/Step.gen_requester_learn.
    iAcIntro; rewrite /commit_acc/=.
    iMod "H" as (s) "/= [(%s' & %Hstep & F) Fc]"; iModIntro.
    rewrite /AuthSet.frag_exact.
    iExists {[s]}; iFrame "F".
    iSplitR.
    { iIntros "!%". split.
      - exists s. set_solver.
      - intros s0 e ->%elem_of_singleton ->%elem_of_singleton. by eexists. }
    iIntros (e) "[%Hin F]". move: Hin => /elem_of_singleton ->.
    iApply ("Fc" with "[F]").
    iApply (AuthSet.frag_proper with "F"). set_solver.
  Qed.

  Fixpoint ctor_requesters_seq (γ : AuthSet.gname) {X A I}
      (Ctor : forall (index : I) (input : X), app.(App.evt)) (* e.g. MemRead *)
      (f : forall (so_far : A) (index : I) (input : X), A)
      (stepQ : forall (so_far : A) (index : I) (input : X), PROP) (* expectation after each step *)
      (finalQ : A -> PROP) (* expectation after all *)
      (indexes : list I) (acc : A) : PROP :=
    match indexes with
    | [] => finalQ acc
    | hd :: indexes' =>
        ctor_requester γ (Ctor hd)
          (fun input : X =>
            stepQ acc hd input **
            ctor_requesters_seq γ Ctor f stepQ finalQ indexes' (f acc hd input))
    end.
  #[global] Hint Opaque ctor_requesters_seq : br_opacity.

  Fixpoint singleton_requesters_seq (γ : AuthSet.gname) {A I}
      (Singleton : forall (index : I), app.(App.evt)) (* e.g. MemWrite *)
      (f : forall (so_far : A) (index : I), A)
      (stepQ : forall (so_far : A) (index : I), PROP) (* expectation after each step *)
      (finalQ : A -> PROP) (* expectation after all *)
      (indexes : list I) (acc : A) : PROP :=
    match indexes with
    | [] => finalQ acc
    | hd :: indexes' =>
        singleton_requester γ (Singleton hd)
        (stepQ acc hd **
         singleton_requesters_seq γ Singleton f stepQ finalQ indexes' (f acc hd))
    end.
  #[global] Hint Opaque singleton_requesters_seq : br_opacity.

End with_app.

#[global] Hint Opaque ctor_requester : br_opacity.
#[global] Hint Opaque singleton_requester : br_opacity.
#[global] Hint Opaque ctor_committer : br_opacity.
#[global] Hint Opaque singleton_committer : br_opacity.

Section singleton_with_ref.
  Context `{Ghostly PROP} `{!BiFUpd PROP} `{!BiBUpdFUpd PROP}.
  Context `{R : !refinement}.

  Lemma gen_transport_singleton comp γ nl nr m Q
      (STEPl : Label (Compose.sts_name _ nl)) (STEPr : Label (Compose.sts_name _ nr)) :
    nl <> nr ->
    Compose.cancel_evt ComposeN.fam nl nr STEPl STEPr ->
    gen_transports comp γ ⊢
    gen_singleton_requester (app := appn nl) m (γ nl) STEPl Q -∗
    gen_singleton_committer (app := appn nr) m (γ nr) STEPr Q.
  Proof using All.
    iIntros (Hdiff Hcancel) "#T R".
    rewrite gen_singleton_requester_equiv gen_singleton_committer_equiv.
    iApply Step.gen_committer_alt_gen_committer.
    iApply Step.gen_committer_proper_strong; first last. {
      rewrite /gen_transports.
      iApply ("T" $! nl nr Hdiff with "[%] R").
      exact /Compose.dual_sets_singletons.
    }
    move=> _ /elem_of_singleton -> /=.
    iSplit. { iIntros "$ !% /=". set_solver. } iDestruct 1 as (? ?) "$".
  Qed.
End singleton_with_ref.
