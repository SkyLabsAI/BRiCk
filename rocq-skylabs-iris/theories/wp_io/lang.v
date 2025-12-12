(*
 * Copyright (c) 2023 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Export iris.program_logic.language.
Require Import iris.algebra.cmra.

Require Import bluerock.prelude.base.
Require Import bluerock.prelude.option.

Require Export bluerock.prelude.name.
Require Export bluerock.prelude.finite_prod.
Require Export bluerock.prelude.sts.

Module Component.

Record t : Type := mkComponent {
  LTS : Sts.t;
  State := (Sts.State LTS);
  Event := (Sts.Label LTS);
  Trace := list (option Event) ;
  step  := LTS.(Sts._sts).(Sts._step);
  (*
  a visible event is either input (initiated by someone else) or
  output (initiated by this component)
  *)
  is_input : Event → bool;
  (* Expression language attached to the LTS *)
  Expr : Type;
  Val : Type;
  of_val : Val → Expr;
  to_val : Expr → option Val;
  prim_step : Expr → State → list (option Event) → Expr → State → list Expr → Prop;
  language_mixin : LanguageMixin of_val to_val prim_step;
}.

(**
An Iris language for an LTS with an attached expression language.
- Delaying picking an expression language avoids fixing the expression/value
types which can restrict behaviors.
- For example, if the language is never meant to terminate, the value type
can be empty, and post-conditions are always False.
 *)
Program Definition lts_lang (C : t) : language := {|
  language.expr := C.(Expr) ;
  language.val := C.(Val) ;
  (** putting the trace into the state *)
  language.state := C.(Trace) * C.(State) ;
  language.observation := option C.(Event) ;
  language.of_val := C.(of_val);
  language.to_val := C.(to_val);
  language.prim_step :=
    λ e s κs e' s' efs,
      (** [label_e] is the event of the step.
      We relate it to κs as a simple way to maintain a connection
      between [C.(prim_step)] and [C.(step)].
      *)
      ∃ label_e, κs = [label_e] ∧
      s'.1 = s.1 ++ κs ∧ (* the state tracks history trace *)
      (** the expression language may fork threads---all threads globally
      share the trace and the LTS state. *)
      C.(prim_step) e s.2 κs e' s'.2 efs ∧
      C.(step) s.2 (label_e) s'.2 ;
|}.

Next Obligation.
  intros [Hlts ????? EXPR VAL ? ? STEP LANG]. rewrite /of_val /to_val /=.
  constructor; try apply LANG.
  intros e [tr σ] ? e' [tr' σ'] efs (? & -> & ? & Hstep & ?). revert Hstep. apply LANG.
Qed.
End Component.

(**
This one is similar to [bluerock.prelude.sts.Compose.compose_lts],
except that it uses [finite_prod] to create the composed types.
TODO: unify them.
*)
Module Compose.

  Import Component.
  (* The configuration for a composition *)
  Record config := {
    name : Set ;
    #[global] name_Names :: Names name ;
    components : name -> Component.t;

    (* a visible event is either input or output *)
    event : Set;
    is_input : event → bool;
    inj_evt (c : name) : (components c).(Event) -> option event;
    (* forwarded events are also either input or output *)
    inj_evt_input (c : name) (ce : (components c).(Event)) (e : event) :
      inj_evt c ce = Some e ->
      (components c).(Component.is_input) ce = is_input e ;

    (* canceling events : input-output pair.
    Note that the input event is first. *)
    cancel_event_asym (c1 c2 : name) :
      (components c1).(Event) -> (components c2).(Event) -> Prop;
    cancel_event_asym_inout (c1 c2 : name) e1 e2 :
      cancel_event_asym c1 c2 e1 e2 ->
        (components c1).(Component.is_input) e1 = true ∧
        (components c2).(Component.is_input) e2 = false ;
    cancel_event_asym_not_forwarded (c1 c2 : name) e1 e2 :
      cancel_event_asym c1 c2 e1 e2 ->
        inj_evt c1 e1 = None ∧ inj_evt c2 e2 = None ;
    cancel_event c1 c2 e1 e2 :=
      cancel_event_asym c1 c2 e1 e2 \/ cancel_event_asym c2 c1 e2 e1;
  }.

  #[global] Arguments is_input {cfg} : rename.
  #[global] Arguments inj_evt {cfg} : rename.
  #[global] Arguments inj_evt_input {cfg} : rename.
  #[global] Arguments cancel_event_asym {cfg} : rename.
  #[global] Arguments cancel_event_asym_inout {cfg} : rename.
  #[global] Arguments cancel_event {cfg} : rename.

  Implicit Type (cfg : config).

  Definition Exprs  cfg := fin_prod.to_list (Expr ∘ components cfg).
  Definition Vals   cfg := fin_prod.to_list (Val ∘ components cfg).
  Definition States cfg := fin_prod.to_list (State ∘ components cfg).

  Variant EventSource {cfg : config} :=
    | Tau (c : cfg.(name))
    | Forward (c : cfg.(name)) (e : (components cfg c).(Component.Event))
    | Sync (c1 c2 : cfg.(name))
           (e1 : (components cfg c1).(Component.Event))
           (e2 : (components cfg c2).(Component.Event)).
  Arguments EventSource : clear implicits.

  #[global] Instance tau_inj {cfg : config} : Inj (=) (=) (@Tau cfg).
  Proof. intros ??. by inversion 1. Qed.

  (* we'd want [Inj2 (=) (=) (=) Forward], but dependent types... *)
  Lemma forward_inj_1 {cfg : config} (c1 c2 : cfg.(name))
    {e1 : (components cfg c1).(Component.Event)}
    {e2 : (components cfg c2).(Component.Event)} :
    Forward c1 e1 = Forward c2 e2 -> c1 = c2.
  Proof. by inversion 1. Qed.
  #[global] Instance forward_inj_2 {cfg : config} (c : cfg.(name)) :
    Inj (=) (=) (@Forward cfg c).
  Proof. intros ???. by simplify_eq. Qed.

  Lemma sync_inj_1 {cfg : config} (c11 c12 c21 c22 : cfg.(name))
    {e11 : (components cfg c11).(Component.Event)}
    {e12 : (components cfg c12).(Component.Event)}
    {e21 : (components cfg c21).(Component.Event)}
    {e22 : (components cfg c22).(Component.Event)} :
    Sync c11 c12 e11 e12 = Sync c21 c22 e21 e22 -> c11 = c21 ∧ c12 = c22.
  Proof. by inversion 1. Qed.
  #[global] Instance sync_inj_2 {cfg : config} (c1 c2 : cfg.(name)) :
    Inj2 (=) (=) (=) (@Sync cfg c1 c2).
  Proof. intros ???? ?. by simplify_eq. Qed.

  Definition Obs cfg    := ((option (event cfg)) * (EventSource cfg))%type.
  Definition Trace cfg  := list (Obs cfg).

  Program Definition lts_lang (cfg : config) : language := {|
    language.expr         := Exprs cfg ;
    language.val          := Vals cfg ;
    language.state        := (Trace cfg) * (States cfg) ;
    language.observation  := Obs cfg ;
    language.of_val       := fin_prod.fmap (λ n, of_val (components cfg n));
    language.to_val       := fin_prod.fmapO (λ n, to_val (components cfg n));
    language.prim_step    :=
      λ es s κs es' s' efs,
      (** [label_e] is the event of the step. *)
      ∃ label_e src_e, κs = [(label_e, src_e)] ∧
      let '(tr, ss) := s in let '(tr', ss') := s' in
      tr' = tr ++ [(label_e, src_e)] ∧
      (** no fork: we use finite product of expressions, and not threadpool *)
      efs = [] ∧
      match label_e with
      | Some e =>
          (** Some component c makes an [el] step that is visible outside as [e] *)
          ∃ (c : cfg.(name)), let C := components cfg c in
          ∃ (el : C.(Event)) e'' s'',
          src_e = Forward c el ∧
          inj_evt c el = Some e ∧
          let sc := fin_prod.lookup ss c in
          C.(prim_step) (fin_prod.lookup es c) sc [Some el] e'' s'' [] ∧
          es' = fin_prod.update (A:=Expr ∘ components cfg) c e'' es ∧
          C.(step) sc (Some el) s'' ∧
          ss' = fin_prod.update (A:=State ∘ components cfg) c s'' ss
      | None =>
          ( (* Some component [c] makes a tau step. *)
            ∃ (c : cfg.(name)), let C := components cfg c in
            ∃ e'' sc',
            src_e = Tau c ∧
            let sc := fin_prod.lookup ss c in
            C.(prim_step) (fin_prod.lookup es c) sc [None] e'' sc' [] ∧
            es' = fin_prod.update (A:=Expr ∘ components cfg) c e'' es ∧
            C.(step) sc None sc' ∧
            ss' = fin_prod.update (A:=State ∘ components cfg) c sc' ss
          ) ∨
          ( (* Some distinct components c1 and c2 synchronized. *)
            ∃ (c1 c2 : cfg.(name)), c1 ≠ c2 ∧
            let C1 := components cfg c1 in let C2 := components cfg c2 in
            ∃ (el1 : C1.(Event)) (el2 : C2.(Event)) e1' e2' sc1' sc2',
            src_e = Sync c1 c2 el1 el2 ∧
            cancel_event_asym c1 c2 el1 el2 ∧
            let sc1 := fin_prod.lookup ss c1 in
            let sc2 := fin_prod.lookup ss c2 in
            C1.(prim_step) (fin_prod.lookup es c1) sc1 [Some el1] e1' sc1' [] ∧
            C1.(step) sc1 (Some el1) sc1' ∧
            C2.(prim_step) (fin_prod.lookup es c2) sc2 [Some el2] e2' sc2' [] ∧
            C2.(step) sc2 (Some el2) sc2' ∧
            es' =
              fin_prod.update (A:=Expr ∘ components cfg) c2 e2'
                (fin_prod.update (A:=Expr ∘ components cfg) c1 e1' es) ∧
            ss' =
              fin_prod.update (A:=State ∘ components cfg) c2 sc2'
                (fin_prod.update (A:=State ∘ components cfg) c1 sc1' ss)
          )
      end ;
  |}.
  Next Obligation.
    intros cfg. constructor; simpl.
    - intros v. apply fin_prod.fmapO_Some.
      intros n. rewrite fin_prod.lookup_fmap. apply Component.language_mixin.
    - intros e v. rewrite /= -fin_prod.fmapO_Some => IS.
      apply fin_prod.lookup_ext => n.
      rewrite fin_prod.lookup_fmap. apply Component.language_mixin, IS.
    - intros es [tr σ] κs es' [tr' σ'] efs (e & ? & -> & ? & ? & STEP).
      apply fin_prod.fmapO_None.
      destruct e as [e|]; [|destruct STEP as [STEP|STEP]].
      + destruct STEP as (c & el & e'' & s'' & ? & ? & PRIM & ?).
        exists c. revert PRIM. apply Component.language_mixin.
      + destruct STEP as (c & e'' & s'' & ? & PRIM & ?).
        exists c. revert PRIM. apply Component.language_mixin.
      + destruct STEP as (c1 & c2 & ? & el1 & el2 & e1' & e2' & STEP).
        destruct STEP as (sc1' & sc2' & ? & ? & PRIM1 & ?).
        exists c1. revert PRIM1. apply Component.language_mixin.
  Qed.

  (* if [c' = c], convert [e'] (which is a [c'] event) to a [c] event. *)
  Definition is_my_event {cfg : config}
      (c c' : cfg.(name)) (e' : (components cfg c').(Component.Event)) :
      option (components cfg c).(Component.Event) :=
    if (decide (c' = c)) is left Heq then
      eq_rect c' (λ n, option (components cfg n).(Component.Event)) (Some e') c Heq
    else None.

  (* extract the trace of component [c] from the composed trace [tr]. *)
  Definition proj_trace {cfg : config} (tr : Trace cfg) (c : cfg.(name)) :
      (components cfg c).(Component.Trace) :=
    omap
      (λ e : Obs cfg,
        match e.2 with
        | Tau c1 =>
            (* is this a Tau of c ? *)
            (if (decide (c1 = c)) then Some None else None)
        | Forward c1 e1 =>
            (* is this a visiable event of c ? *)
            if is_my_event c c1 e1 is Some e_c then Some (Some e_c) else None
        | Sync c1 c2 e1 e2 =>
            (* is this a visiable event of c ? *)
            if is_my_event c c1 e1 is Some e_c then
              Some (Some e_c)
            else
              if is_my_event c c2 e2 is Some e_c then
                Some (Some e_c)
              else None
        end)
      tr.

  Lemma nsteps_trace_final {cfg} n es σ1 κs t2 σ2 :
    language.nsteps (Λ:=lts_lang cfg) n (es, σ1) κs (t2, σ2) ->
    σ2.1.*1 = σ1.1.*1 ++ κs.*1.
  Proof.
    revert n es σ1. induction κs as [|e κs IH]; intros n es [tr1 σ1] STEP.
    - rewrite fmap_nil app_nil_r /=.
      inversion STEP as [|?????? STEP']; simplify_eq; first done.
      destruct STEP' as [????????? (?&?&?&?)]. simplify_list_eq.
    - rewrite fmap_cons.
      inversion STEP as [|?????? STEP' STEPS]; simplify_eq.
      destruct STEP' as [??? σ3 ????? (?&?&?&EqS)].
      destruct σ3.
      simplify_list_eq. destruct EqS as (?&?&_).
      apply IH in STEPS. by simplify_list_eq.
  Qed.

  Lemma proj_trace_nil {cfg} (c : cfg.(name)) :
    proj_trace [] c = [].
  Proof. by rewrite /proj_trace /=. Qed.

  Lemma proj_trace_cons {cfg} e (tr : Trace cfg) (c : cfg.(name)) :
    proj_trace (e :: tr) c = (proj_trace [e] c) ++ (proj_trace tr c).
  Proof. apply (omap_app _ [_]). Qed.

  Lemma proj_trace_app {cfg} (tr1 tr2 : Trace cfg) (c : cfg.(name)) :
    proj_trace (tr1 ++ tr2) c = (proj_trace tr1 c) ++ (proj_trace tr2 c).
  Proof. apply omap_app. Qed.

  Lemma proj_trace_singleton_tau_ne {cfg} e (c1 c2 : cfg.(name)) (NEq: c1 ≠ c2) :
    proj_trace [(e, Tau c1)] c2 = [].
  Proof.
    (* TODO need omap general lemmas for list *)
    rewrite /proj_trace /= decide_False //.
  Qed.

  Lemma proj_trace_singleton_tau_eq {cfg} e (c : cfg.(name)) :
    proj_trace [(e, Tau c)] c = [None].
  Proof.
    (* TODO need omap general lemmas for list *)
    rewrite /proj_trace /= decide_True //.
  Qed.

  Lemma proj_trace_singleton_forward_ne {cfg} e (c1 c2 : cfg.(name)) e1 (NEq: c1 ≠ c2) :
    proj_trace [(e, Forward c1 e1)] c2 = [].
  Proof.
    (* TODO need omap general lemmas for list *)
    rewrite /proj_trace /= /is_my_event.
    case (decide (c1 = c2)); done.
  Qed.

  Lemma proj_trace_singleton_forward_eq {cfg} e (c : cfg.(name)) e1 :
    proj_trace [(e, Forward c e1)] c = [Some e1].
  Proof.
    (* TODO need omap general lemmas for list *)
    by rewrite /proj_trace /= /is_my_event decide_True_pi /=.
  Qed.

  Lemma proj_trace_singleton_sync_ne {cfg} e (c c1 c2 : cfg.(name)) e1 e2
    (NEq1 : c ≠ c1) (NEq2 : c ≠ c2) :
    proj_trace [(e, Sync c1 c2 e1 e2)] c = [].
  Proof.
    (* TODO need omap general lemmas for list *)
    rewrite /proj_trace /= /is_my_event.
    case (decide (c1 = c)); [done|].
    case (decide (c2 = c)); done.
  Qed.

  Lemma proj_trace_singleton_sync_eq1 {cfg} e (c1 c2 : cfg.(name)) e1 e2 :
    proj_trace [(e, Sync c1 c2 e1 e2)] c1 = [Some e1].
  Proof.
    (* TODO need omap general lemmas for list *)
    by rewrite /proj_trace /= /is_my_event decide_True_pi /=.
  Qed.

  Lemma proj_trace_singleton_sync_eq2 {cfg} e (c1 c2 : cfg.(name)) e1 e2 :
    c1 ≠ c2 →
    proj_trace [(e, Sync c1 c2 e1 e2)] c2 = [Some e2].
  Proof.
    intros.
    (* TODO need omap general lemmas for list *)
    rewrite /proj_trace /= /is_my_event.
    case (decide (c1 = c2)) => ?; [done|].
    by rewrite decide_True_pi /=.
  Qed.
End Compose.
