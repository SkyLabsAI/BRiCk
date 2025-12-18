(*
 * Copyright (C) 2020 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import stdpp.propset.
Require Import skylabs.prelude.base.
Require Import skylabs.prelude.finite.
Require Import skylabs.prelude.functions.
Require Import skylabs.prelude.lens.

Import LensNotations.
#[local] Open Scope lens_scope.

(** Labeled transition systems *)

Module Sts.
  (* Labeled transition systems. *)
  Record sts {Label : Type} : Type := {
    (** State type *)
    _state      :> Type
    (** Initial state predicate *)
  ; _init_state : _state -> Prop

    (** Step relation of the LTS
    [None] means [Tau]. *)
  ; _step       : _state -> option Label -> _state -> Prop
  }.
  #[global] Arguments sts _ : clear implicits.

  (** Reflexive, transitive closure of steps *)
  Fixpoint step_star {L} (STS : sts L)
      (s : STS.(_state)) (ls : list (option L)) (s' : STS.(_state)) : Prop :=
    match ls with
    | ol :: ls' => exists s'', STS.(_step) s ol s'' /\ step_star STS s'' ls' s'
    | [] => s = s'
    end.

  (** Reflexive transitive closure of internal steps *)
  Definition step_star_tau {L} (STS : sts L)
      (s s' : STS.(_state)) : Prop :=
    exists n : nat, step_star STS s (replicate n None) s'.

  (** Composition of closures *)
  Lemma step_star_comp L (STS : sts L) s s' s'' lbls lbls' :
    step_star STS s lbls s' ->
    step_star STS s' lbls' s'' ->
    step_star STS s (lbls ++ lbls') s''.
  Proof.
    move: s s' s''.
    induction lbls as [|?? IH] =>[s s' s'' /= ->//|s s' s''].
    move=>[s3 [Hss3 Hs3s']] Hs's''.
    rewrite -app_comm_cons //=.
    by exists s3; split; last apply: IH.
  Qed.

  Lemma step_star_tau_comp L (STS : sts L) s s' s'' :
    step_star_tau STS s s' ->
    step_star_tau STS s' s'' ->
    step_star_tau STS s s''.
  Proof.
    move=>[n Hs] [n' Hs'].
    by exists (n + n'); rewrite replicate_add; apply: step_star_comp.
  Qed.

  (** Reflexive transitive closure of external steps

  We model the closure as interleaving of external steps
  with finitely many (possibly 0) internal tau steps
  *)
  Fixpoint step_star_ext {L} (STS : sts L)
      (s : STS.(_state)) (ls : list L) (s' : STS.(_state)) : Prop :=
    match ls with
    | l :: ls' => exists s'' s''', step_star_tau STS s s'' /\
                  STS.(_step) s'' (Some l) s''' /\ step_star_ext STS s''' ls' s'
    | [] => step_star_tau STS s s'
    end.

  Section map.
    (*
    [L] is the type of *internal* events
    [L'] is the type of *external* events *)
    Context {L L' : Type} (f : L -> L' -> Prop).

    Variable (STS : sts L).

    Variant Map_step (s : STS.(_state)) : option L' -> STS -> Prop :=
    | MAP_tau {s'}
              (_ : _step STS s None s')
      : Map_step s None s'
    | MAP_action {s' l l'}
                 (_ : STS.(_step) s (Some l) s')
                 (_ : f l l')
      : Map_step s (Some l') s'.

    (** * Mapping event types
    This allows you to translate events in one [t] to another [t]
    *)
    Definition map  : sts L' :=
      {| _init_state := STS.(_init_state)
       ; _step := Map_step |}.

  End map.

  Section hide.
    (** [P e] holds on events [e] that should not connect to the outside
    world, i.e. they must match internal to this system or they are
    not enabled.
    *)
    Context {L : Type} (P : L -> Prop).

    Variant Hide_step (l : L) : L -> Prop :=
    | HIDE (_ : ~P l)
      : Hide_step l l.

    (** * Hiding internal events
    To prevent "Internal" events from escaping, you can do the following

    [[
    hide (fun x => match x with
                    | Internal _ => False
                    | _ => True
                    end) st
    ]]
    *)
    Definition hide : sts L -> sts L := map Hide_step.
  End hide.

  Section par.
    Context {e : Type} (dual : e -> e -> Prop).

    Variable (L R : sts e).

    Variant Par_step : L * R -> option e -> L * R -> Prop :=
    | PAR_comm {l l' r r' eL eR}
              (_ : _step L l (Some eL) l')
              (_ : _step R r (Some eR) r')
              (_ : dual eL eR)
      : Par_step (l,r) None (l',r')
    | PAR_left {l l' r e}
              (_ : _step L l e l')
      : Par_step (l,r) e (l',r)
    | PAR_right {l r r' e}
              (_ : _step R r e r')
      : Par_step (l,r) e (l,r')
    .

    (** * Binary parallel composition
    this allows you to compose two [t]s with possible communication
    between them.

    [dual e1 e2] holds when [e1] and [e2] cancel producing a [Tau]
    transition for the composed system.
    *)
    Definition par : sts e :=
      {| _init_state '(l,r) := L.(_init_state) l /\ R.(_init_state) r
       ; _step := Par_step |}.

  End par.

  (** bundled state transition systems. *)
  Record t := {
    Label : Type
  ; _sts :> sts Label
  }.
  #[global] Arguments Build_t {_} _.
  Definition State (x : t) := x.(_sts).(_state).
  Definition init_state (x : t) : State x -> Prop := x.(_sts).(_init_state).
  Definition step (x : t) : State x -> option x.(Label) -> State x -> Prop :=
    x.(_sts).(_step).

  (* Let these simplify as if they were projections. *)
  #[global] Arguments State !_ /.
  #[global] Arguments init_state !_ /.
  #[global] Arguments step !_ /.
End Sts.

Module Compose.
  (* The configuration for a composition *)
  Record config := {
    (* logical name of each component *)
    name : Set;
    #[global] name_eq_dec :: EqDecision name;
    #[global] name_finite :: Finite name;

    (* external event type of the composition *)
    external_event : Set;

    (* LTS of each component *)
    sts_name : name -> Sts.t;

    (* LTSes communicate through canceling events
    n1 initiates the communication, and n2 receives it. *)
    cancel_evt_asym : ∀ (n1 n2 : name),
      Sts.Label (sts_name n1) -> Sts.Label (sts_name n2) -> Prop;

    cancel_evt (n1 n2 : name)
        (l1 : Sts.Label (sts_name n1)) (l2 : Sts.Label (sts_name n2)) :=
      cancel_evt_asym n1 n2 l1 l2 \/ cancel_evt_asym n2 n1 l2 l1;

    (* A component's event can be external *)
    inj_evt : ∀ (n : name), Sts.Label (sts_name n) -> option external_event;

  }.

  Section Compose.
    Context (sf : config).
    Implicit Types (n : name sf).

    Definition State : Type := ∀ n, Sts.State (sts_name sf n).

    Definition init_state (s: State) : Prop := ∀ n, Sts.init_state _ (s n).

    Definition eq_except (n : list _) (s s' : State) :=
      ∀ n', n' ∉ n -> s n' = s' n'.

    #[global] Instance eq_except_equiv ns : Equivalence (Compose.eq_except ns).
    Proof.
      split; red => //.
      { move=> x y E n Hni. by rewrite (E _). }
      { move=> x y z E1 E2 n Hni. by rewrite (E1 _) ?(E2 _). }
    Qed.

    Lemma eq_except_weaken {l1 l2 s1 s2} : l1 ⊆ l2 ->
      Compose.eq_except l1 s1 s2 -> Compose.eq_except l2 s1 s2.
    Proof.
      move=> Hsub /[swap] n /(_ n) /[swap] Hni2. apply => Hi1.
      apply Hni2, Hsub, Hi1.
    Qed.

    Lemma eq_except_insert {n ns s1 s2} {cs : Sts.State (Compose.sts_name sf n)} :
      Compose.eq_except (n :: ns) s1 s2 ->
      (if bool_decide (n ∈ ns) then True else (s1 n = cs)) ->
      Compose.eq_except ns s1 (dep_fn_insert n cs s2).
    Proof.
      move=> + Hin n' Hni; move=> /(_ n') Heq.
      destruct (decide (n = n')) as [->|Hne]. {
        by rewrite bool_decide_eq_false_2 // dep_fn_insert_eq in Hin |- *.
      }
      rewrite dep_fn_insert_ne //. apply Heq. set_solver.
    Qed.

    Lemma eq_except_insert_in {n ns s1 s2} {cs : Sts.State (Compose.sts_name sf n)} :
      Compose.eq_except (n :: ns) s1 s2 ->
      n ∈ ns ->
      Compose.eq_except ns s1 (dep_fn_insert n cs s2).
    Proof.
      move=> Heq Hin.
      apply (eq_except_insert Heq).
      by rewrite bool_decide_eq_true_2.
    Qed.

    Definition compose_lts : Sts.sts (external_event sf) := {|
      Sts._state := State;
      Sts._init_state := init_state;
      (* a step of the composition is either:
      - an externally visible step which comes from some constituent component n
      - a tau step, which is either
        + a tau step of some constituent component n
        + an internal communication step between two components na and nb *)
      Sts._step (s : State) (e : option (external_event sf)) (s' : State) :=
        match e with
        | Some ext_e =>
            ∃ n : name sf,
            eq_except [n] s s' ∧ (* only differ in component n *)
            ∃ evt_x : Sts.Label (sts_name sf n),
            (* evt_x is externally ext_e *)
            inj_evt sf n evt_x = Some ext_e ∧
            Sts.step (sts_name sf n) (s n) (Some evt_x) (s' n)
        | None =>
          (* either a tau step of n *)
          (∃ n : name sf, eq_except [n] s s' ∧
            Sts.step (sts_name sf n) (s n) None (s' n))
          ∨
          (* or a communication step between na and nb *)
          (∃ (na nb : name sf)
            (la : Sts.Label (sts_name sf na))
            (lb : Sts.Label (sts_name sf nb)),
            na ≠ nb ∧ (* communication requires two *distinct* parties *)
            Sts.step (sts_name sf na) (s na) (Some la) (s' na) ∧
            eq_except [na;nb] s s' ∧
            Sts.step (sts_name sf nb) (s nb) (Some lb) (s' nb) ∧
            cancel_evt sf na nb la lb)
        end
    |}.

    Definition make : Sts.t := Sts.Build_t compose_lts.

  End Compose.

  #[global] Arguments State !_ /.

  (* Lens to project state of the component n *)
  Definition _fam_sts (fam : Compose.config) (n : Compose.name fam) :
      Compose.State fam -l> Sts.State (Compose.sts_name fam n) :=
    lens.of_get_set (fun st => st n) (fun st ip => dep_fn_insert n ip st).

  (* Lifting cancel_evt to sets *)
  Definition dual_sets (sf : Compose.config) {n1 n2 : Compose.name sf}
        (STEP1 : propset (Sts.Label (Compose.sts_name _ n1)))
        (STEP2 : propset (Sts.Label (Compose.sts_name _ n2))) :=
    (∀ e1, e1 ∈ STEP1 -> ∃ e2, e2 ∈ STEP2 ∧ Compose.cancel_evt sf _ _ e1 e2) ∧
    (∀ e2, e2 ∈ STEP2 -> ∃ e1, e1 ∈ STEP1 ∧ Compose.cancel_evt sf _ _ e1 e2).

  Section Compose.
    Context (sf: config).
    Implicit Types (n : name sf).

    Lemma dual_sets_singletons {n1 n2}
        (s1 : Sts.Label (Compose.sts_name _ n1))
        (s2 : Sts.Label (Compose.sts_name _ n2)) :
      dual_sets sf {[s1]} {[s2]} ↔ Compose.cancel_evt sf _ _ s1 s2.
    Proof. rewrite /dual_sets. set_solver. Qed.

    #[global] Instance dual_sets_proper {n1 n2} :
      Proper (equiv ==> equiv ==> iff) (dual_sets sf (n1 := n1) (n2 := n2)).
    Proof using Type*. rewrite /dual_sets. intros ??? ???. set_solver. Qed.

    Lemma step_star_tau_lift
      (n__comp : Compose.name sf)
      (st : Compose.State sf)
      (st__comp' : Sts.State (Compose.sts_name sf n__comp)) :
          Sts.step_star_tau _ (st n__comp) st__comp'
          ->  Sts.step_star_tau (compose_lts sf) st
               (st &: _fam_sts _ n__comp .= st__comp').
    Proof.
      move=>[n]. elim: n st st__comp' => [|n IHn] st st__comp'.
      - by move=> /= <-; exists 0; rewrite dep_fn_insert_set_view_fun.
      - move=> /= [s' [Hs']].
        have := Refine (IHn (dep_fn_insert n__comp s' st) st__comp').
        rewrite dep_fn_insert_view_set => H {}/H /=.
        rewrite dep_fn_insert_set_set_fun.
        move=>[n' Hstep_star'].
        exists (S n'), (dep_fn_insert n__comp s' st).
        split; last done.
        left; exists n__comp.
        split; last by rewrite dep_fn_insert_view_set.
        exact /Compose.eq_except_insert_in /elem_of_list_singleton.
    Qed.

    Lemma step_star_ext_lift_single
      (n__comp n__cncl : Compose.name sf)
      (st : Compose.State sf)
      (st__comp' : Sts.State (Compose.sts_name sf n__comp))
      (lbl : Sts.Label (Compose.sts_name sf n__comp))
      (st__cncl' : Sts.State (Compose.sts_name sf n__cncl))
      (lbl' : Sts.Label (Compose.sts_name sf n__cncl)) :
      n__comp <> n__cncl
      -> Sts.step_star_ext _ (st n__comp) [lbl] st__comp'
      -> cancel_evt sf n__comp n__cncl lbl lbl'
      -> Sts.step (sts_name sf n__cncl) (st n__cncl) (Some lbl') st__cncl'
      -> Sts.step_star_tau (compose_lts sf) st
          (st &: _fam_sts _ n__comp .= st__comp'
              &: _fam_sts _ n__cncl .= st__cncl').
    Proof.
      move=>Hne.
      move=>[st'' [st''' [Hsteps_tau [Hstep Hsteps]]]] Hcncl Hstep'.
      apply: Sts.step_star_tau_comp; first
        by apply: step_star_tau_lift.
      rewrite -(dep_fn_insert_view_set st n__comp st''') in Hsteps.

      elim (step_star_tau_lift n__comp
              (dep_fn_insert n__comp st'''
                (dep_fn_insert n__cncl st__cncl' st)) st__comp');
        last by move: Hsteps; rewrite !dep_fn_insert_view_set.
      move=>n'.
      rewrite /= dep_fn_insert_set_set_fun.
      rewrite /= (dep_fn_insert_exchange_fun _ n__comp n__cncl) //= =>?.
      eexists (S n'), _; split; last by eassumption.
      right; exists n__comp, n__cncl, lbl, lbl'.
      split; first done.
      split; first by rewrite !dep_fn_insert_view_set.
      split.
      - rewrite /eq_except=>n.
        move=>/not_elem_of_cons [Hne' /not_elem_of_cons [Hne'' ?]].
        by rewrite !dep_fn_insert_view_set_ne //.
      - split; last done.
        by rewrite !(dep_fn_insert_view_set_ne _ n__comp n__cncl) //
             dep_fn_insert_view_set.
    Qed.
  End Compose.
End Compose.

#[global] Notation LTS := Sts.sts.
#[global] Notation lts_state := Sts._state.
#[global] Notation lts_step := Sts._step.
#[global] Notation lts_init_state := Sts._init_state.

(* TODO: unify [reachable] and [Sts.step_star]
The following lemma should hold:
Lemma reachable_step_star {l} (lts : LTS l) s es s' :
  reachable lts s es s' <-> Sts.step_star lts s es s'.

The difference is that [reachable] recurses on the tail (es ++ [e]), while
[Sts.step_star] recurses on the head (e :: es).
*)
Inductive reachable {Label : Type} (lts : LTS Label) (s : lts.(lts_state))
  : list (option Label) -> lts.(lts_state) -> Prop :=
| ReachableDone : reachable lts s nil s
| ReachableStep {e es s' s''} (_ : reachable lts s es s') (_ : lts.(lts_step) s' e s'')
  : reachable lts s (es ++ [e]) s''.

Lemma reachable_nil {Label : Type} (lts : Sts.sts Label) s s' :
  reachable lts s [] s' <-> s = s'.
Proof.
  split; intros STEP.
  - inversion STEP as [|???? REACH ? EqH]; [done|].
    by apply app_nil in EqH as [].
  - subst; by constructor.
Qed.
Lemma reachable_singleton {Label : Type} (lts : LTS Label) s e s' :
  reachable lts s [e] s' <-> lts.(lts_step) s e s'.
Proof.
  split; intros STEP.
  - inversion STEP as [|???? REACH ? EqH].
    destruct es; simplify_list_eq.
    + apply reachable_nil in REACH. by subst.
    + match goal with
      | H : _ ++ _ = [] |- _ => by apply app_nil in H as []
      end.
  - eapply (@ReachableStep _ _ _ _ []); [|done]. constructor.
Qed.
