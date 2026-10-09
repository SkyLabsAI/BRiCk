(*
 * Copyright (c) 2022 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.iris.extra.proofmode.proofmode.
Require Import skylabs.prelude.named_binder.
Require Import skylabs.iris.extra.algebra.telescopes.
Require Import skylabs.iris.extra.bi.telescopes.
Require Import skylabs.lang.cpp.logic.entailsN.
Require Import skylabs.lang.cpp.specs.classy.

Lemma ex_eq {PROP : bi} {T} (a : T) (P : T -> PROP) :
  (∃ x : T, [| a = x |] ∗ P x) ⊣⊢ P a.
Proof.
  intros. split'.
  - iIntros "A"; iDestruct "A" as (?) "[-> $]".
  - iIntros "A"; iExists _; iSplitR; [ | iAssumption ].
    iPureIntro; eauto.
Qed.

Lemma ex_eq' {PROP : bi} {T} (a : T) (P : T -> PROP) :
  (∃ x : T, [| x = a |] ∗ P x) ⊣⊢ P a.
Proof.
  intros. split'.
  - iIntros "A"; iDestruct "A" as (?) "[-> $]".
  - iIntros "A"; iExists _; iSplitR; [ | iAssumption ].
    iPureIntro; eauto.
Qed.


Section with_prop.
  Context {PROP : bi} {ARG : Type} {RESULT : Type}.

  (** The canonical type of function specifications.
      These are written in weakest pre-condition style which leads to a
      natural shallow encoding.

      Note that this file goes through some length to maintain backwards
      compatibility with previous definitions.

      Universes:
      The universe constraints here are very important note that the universe
      of the entire type is [bi.u0] which is the universe of the logic. Since
      the logic is able to quantify over itself, e.g. [forall X : PROP, x], we are
      free to quantify over specifications without any universe issues. Deeper
      embeddings of this type do not enjoy this property and can introduce
      universe subtle universe issues that can be very difficult to debug.
   *)
  Record WpSpec : Type@{universes.Logic} :=
    { (* The first three arguments are accumulators that are interpreted away
         by the [wp_specD] function below.
         - [acc_arg] is the *reversed* list of arguments that we have seen already
           We accumulate the list of arguments so that we can assert a *single*
           equality on all of the arguments.
         - [acc_pre] is the reversed list of separating conjunctions that have been
           added to the pre-condition. These are maintained so that they can be
           placed in the right order and after the equality on the arguments.
         - [acc_post] is the separating conjunction of propositions that have
           been added to the post condition.
         All of these use a deep embedding of a monoid to avoid introducing trivial
         assertions such as [emp].
       *)
      spec_internal : forall (acc_arg : list ARG) (acc_pre : list PROP)
                        (acc_post : list (RESULT -> PROP))
                        (acc_post_except : list (RESULT -> PROP)),
        list ARG -> (RESULT -> PROP) -> (RESULT -> PROP) -> PROP
    ; spec_internal_frame : forall args' P Q Q__except args K__normal K__normal' K__except K__except',
        (∀ r, K__normal r -∗ K__normal' r) ∧
        (∀ r, K__except r -∗ K__except' r)
        ⊢ spec_internal args' P Q Q__except args K__normal K__except -∗ spec_internal args' P Q Q__except args K__normal' K__except'
      (* the following three fields formally capture the meaning of the accumulators
       *)
    ; arg_ok : forall acc_args acc_pre acc_post acc_post_except A args K K__except,
            spec_internal (acc_args ++ [A]) acc_pre acc_post acc_post_except args K K__except
        ⊣⊢ (∃ aa, [| args = A :: aa |] ∗ spec_internal acc_args acc_pre acc_post acc_post_except aa K K__except)
    ; pre_ok : forall acc_args acc_pre acc_post acc_post_except P args K K__except,
            spec_internal acc_args (P :: acc_pre) acc_post acc_post_except args K K__except
        ⊣⊢ P ∗ spec_internal acc_args acc_pre acc_post acc_post_except args K K__except
    ; post_ok : forall acc_args acc_pre acc_post acc_post_except P args K K__except,
            spec_internal acc_args acc_pre (acc_post ++ [P]) acc_post_except args K K__except
        ⊣⊢ spec_internal acc_args acc_pre acc_post acc_post_except args (fun x => P x -∗ K x) K__except
    ; post_except_ok : forall acc_args acc_pre acc_post acc_post_except P args K K__except,
            spec_internal acc_args acc_pre acc_post (acc_post_except ++ [P]) args K K__except
        ⊣⊢ spec_internal acc_args acc_pre acc_post acc_post_except args K (fun x => P x -∗ K__except x)
    }.

  Lemma spec_internal_proper wp (K K' : _ → PROP) (K__except K__except' : _ → PROP) (a : list _) w x y z :
      (forall x, K x ⊣⊢ K' x) ->
      (forall x, K__except x ⊣⊢ K__except' x) ->
      wp.(spec_internal) w x y z a K K__except ⊣⊢ wp.(spec_internal) w x y z a K' K__except'.
  Proof.
    move => HK HK__except; split'.
    - iIntros "X"; iRevert "X"; iApply spec_internal_frame.
      by iSplit; iIntros (?) "?"; rewrite (HK,HK__except).
    - iIntros "X"; iRevert "X"; iApply spec_internal_frame.
      by iSplit; iIntros (?) "?"; rewrite (HK,HK__except).
  Qed.

  Lemma args_ok : forall wp A acc_args acc_pre acc_post acc_post_except args K K__except,
           wp.(spec_internal) (acc_args ++ A) acc_pre acc_post acc_post_except args K K__except
      ⊣⊢ (∃ aa, [| args = rev A ++ aa |] ∗ (wp.(spec_internal) acc_args acc_pre acc_post acc_post_except aa K K__except)).
  Proof.
    induction A; simpl; intros.
    - rewrite ex_eq. rewrite app_nil_r. done.
    - have ->:(acc_args ++ a :: A = (acc_args ++ [a]) ++ A); first by rewrite -assoc.
      rewrite IHA. setoid_rewrite arg_ok.
      split'.
      + iIntros "A"; iDestruct "A" as (aa) "[-> A]"; iDestruct "A" as (aa0) "[-> A]".
        iExists _; iSplitR; first by iPureIntro; rewrite -assoc; eauto.
        eauto.
      + iIntros "A"; iDestruct "A" as (aa) "[-> A]".
        rewrite -assoc.
        iExists _; iSplitR; first by iPureIntro; eauto.
        iExists _; iSplitR; first by iPureIntro; eauto.
        eauto.
  Qed.

  Lemma pres_ok : forall wp acc_args acc_pre acc_post acc_post_except P args K K__except,
          wp.(spec_internal) acc_args (P ++ acc_pre) acc_post acc_post_except args K K__except
      ⊣⊢ ([∗] P) ∗ wp.(spec_internal) acc_args acc_pre acc_post acc_post_except args K K__except.
  Proof.
    intros.
    induction P; simpl.
    - by rewrite left_id.
    - by rewrite pre_ok -assoc IHP.
  Qed.

  Lemma posts_ok : forall wp P acc_args acc_pre acc_post acc_post_except args K K__except,
          wp.(spec_internal) acc_args acc_pre (acc_post ++ P) acc_post_except args K K__except
      ⊣⊢ wp.(spec_internal) acc_args acc_pre acc_post acc_post_except args (fun x => ([∗list] p ∈ P, p x) -∗ K x) K__except.
  Proof.
    induction P; simpl; intros.
    - rewrite app_nil_r. apply spec_internal_proper;
        intros; by rewrite ?bi.emp_wand.
    - have ->: (acc_post ++ a :: P = (acc_post ++ [a]) ++ P).
      { by rewrite -assoc. }
      rewrite IHP.
      rewrite post_ok.
      apply spec_internal_proper;
        intro;
        by rewrite ?bi.wand_curry.
  Qed.

  Lemma posts_except_ok : forall wp P acc_args acc_pre acc_post acc_post_except args K K__except,
          wp.(spec_internal) acc_args acc_pre acc_post (acc_post_except ++ P) args K K__except
      ⊣⊢ wp.(spec_internal) acc_args acc_pre acc_post acc_post_except args K (fun x => ([∗list] p ∈ P, p x) -∗ K__except x).
  Proof.
    induction P; simpl; intros.
    - rewrite app_nil_r.
      apply spec_internal_proper => // x.
      by rewrite bi.emp_wand.
    - rewrite cons_middle assoc IHP post_except_ok.
      apply spec_internal_proper => // x.
      by rewrite ?bi.wand_curry.
  Qed.

  Lemma all_args_ok (wp : WpSpec) acc_args acc_pre acc_post acc_post_except args K K__except
    : spec_internal wp acc_args acc_pre acc_post acc_post_except args K K__except
      ⊣⊢ ∃ aa : list ARG, [| args = rev acc_args ++ aa |] ∗ spec_internal wp [] acc_pre acc_post acc_post_except aa K K__except.
  Proof.
    intros. change acc_args with ([] ++ acc_args). rewrite args_ok /=. eauto.
  Qed.
  Lemma all_pres_ok (wp : WpSpec) acc_args acc_pre acc_post acc_post_except args K K__except :
    spec_internal wp acc_args acc_pre acc_post acc_post_except args K K__except
    ⊣⊢ [∗] acc_pre ∗ spec_internal wp acc_args [] acc_post acc_post_except args K K__except.
  Proof.
    intros. have ->: acc_pre = acc_pre ++ nil by rewrite app_nil_r. rewrite pres_ok app_nil_r/=; eauto.
  Qed.
  Lemma all_posts_ok (wp : WpSpec) acc_args acc_pre acc_post acc_post_except args K K__except :
    spec_internal wp acc_args acc_pre acc_post acc_post_except args K K__except ⊣⊢
    spec_internal wp acc_args acc_pre [] acc_post_except args (λ x : RESULT, ([∗ list] p ∈ acc_post, p x) -∗ K x) K__except.
  Proof.
    intros. have ->: acc_post = [] ++ acc_post by done. rewrite posts_ok/=; eauto.
  Qed.

  Lemma all_posts_except_ok (wp : WpSpec) acc_args acc_pre acc_post acc_post_except args K K__except :
    spec_internal wp acc_args acc_pre acc_post acc_post_except args K K__except ⊣⊢
    spec_internal wp acc_args acc_pre acc_post [] args K (λ x : RESULT, ([∗ list] p ∈ acc_post_except, p x) -∗ K__except x).
  Proof.
    intros. have ->: acc_post_except = [] ++ acc_post_except by done. rewrite posts_except_ok/=; eauto.
  Qed.

  Lemma all_accs_ok (wp : WpSpec) acc_args acc_pre acc_post acc_post_except args K K__except :
    spec_internal wp acc_args acc_pre acc_post acc_post_except args K K__except
    ⊣⊢ ∃ aa : list ARG,
        [| args = rev acc_args ++ aa |] ∗
        [∗] acc_pre ∗
        spec_internal wp [] [] [] [] aa
          (λ x : RESULT, ([∗ list] p ∈ acc_post, p x) -∗ K x)
          (λ x : RESULT, ([∗ list] p ∈ acc_post_except, p x) -∗ K__except x).
  Proof.
    rewrite all_args_ok. f_equiv; intro. f_equiv.
    rewrite all_pres_ok; f_equiv.
    by rewrite all_posts_ok all_posts_except_ok.
  Qed.

  Lemma spec_internal_denote wp acc_arg acc_pre acc_post acc_post_except args K K__except :
        wp.(spec_internal) acc_arg acc_pre acc_post acc_post_except args K K__except
    ⊣⊢ ([∗list] P ∈ acc_pre, P) ∗
       ∃ aa, [| args = rev acc_arg ++ aa |] ∗
             wp.(spec_internal) [] [] [] [] aa
                  (fun x => ([∗list] P ∈ acc_post, P x) -∗ K x)
                  (fun x => ([∗list] P ∈ acc_post_except, P x) -∗ K__except x).
  Proof.
    rewrite -{1}[acc_pre]app_nil_r pres_ok.
    rewrite -{1}[acc_post]app_nil_l posts_ok.
    rewrite -{1}[acc_post_except]app_nil_l posts_except_ok.
    by rewrite -{1}[acc_arg]app_nil_l args_ok.
  Qed.

  (** The meaning of a [WpSpec] as a weakest pre-condition. *)
  Definition wp_specE (wpp : WpSpec) : list ARG -> (RESULT -> PROP) -> (RESULT -> PROP) -> PROP :=
    wpp.(spec_internal) nil nil nil nil.
  Definition wp_specD (wpp : WpSpec) : list ARG -> (RESULT -> PROP) -> PROP :=
    fun args post => wpp.(spec_internal) nil nil nil nil args post (fun _ => False%I).

  Theorem wp_specE_frame (wpp : WpSpec) : forall args Q Q' Q__except Q__except',
    (∀ r, Q r -∗ Q' r) ∧
    (∀ r, Q__except r -∗ Q__except' r)
    ⊢ wp_specE wpp args Q Q__except -∗ wp_specE wpp args Q' Q__except'.
  Proof.
    intros. apply spec_internal_frame.
  Qed.

  Theorem wp_specD_frame (wpp : WpSpec) : forall args Q Q',
      (∀ r, Q r -∗ Q' r) ⊢ wp_specD wpp args Q -∗ wp_specD wpp args Q'.
  Proof.
    intros; rewrite -spec_internal_frame.
    iIntros "$"; iSplit => //; iIntros "% $".
  Qed.

End with_prop.
#[global,deprecated(since="2022-02-28",note="use [wp_specD_frame].")]
Notation wpp_frame := (wp_specD_frame) (only parsing).

Arguments WpSpec : clear implicits.
#[local] Coercion wp_specE : WpSpec >-> Funclass.

Module Export wpspec_ofe.
Section wpspec_ofe.
  Context {PROP : bi} {ARGS RESULT : Type}.
  Notation WPP := (WpSpec PROP ARGS RESULT) (only parsing).
  Instance wpspec_equiv : Equiv WPP :=
    fun wpp1 wpp2 => forall x Q Qe, wp_specE wpp1 x Q Qe ≡ wp_specE wpp2 x Q Qe.
  Instance wpspec_dist : Dist WPP :=
    fun n wpp1 wpp2 => forall x Q Qe, wp_specE wpp1 x Q Qe ≡{n}≡ wp_specE wpp2 x Q Qe.

  Lemma wpspec_ofe_mixin : OfeMixin WPP.
  Proof.
    by apply (iso_ofe_mixin (A := list ARGS -d> (RESULT -> PROP) -d> (RESULT -> PROP) -d> PROP) wp_specE).
  Qed.
  Canonical Structure WpSpecO := Ofe WPP wpspec_ofe_mixin.
End wpspec_ofe.
End wpspec_ofe.
Arguments WpSpecO : clear implicits.

(** Relations between WPPs. *)
Definition wpspec_relation {PROP : bi} (R : relation PROP)
    {ARGS : Type} {RESULT : Type}
    (wpp2 : WpSpec PROP ARGS RESULT)
    (wpp1 : WpSpec PROP ARGS RESULT) : Prop :=
  (** We use a single [K] rather than pointwise equal [K1], [K2] for
      compatibility with [fs_entails], [fs_impl]. *)
  forall xs K Ke, R (wpp1 xs K Ke) (wpp2 xs K Ke).
#[global] Instance: Params (@wpspec_relation) 4 := {}.

Notation wpspec_entailsN n := (wpspec_relation (entailsN n)) (only parsing).
Notation wpspec_entails := (wpspec_relation bi_entails) (only parsing).
Notation wpspec_dist n := (wpspec_relation (flip (dist n))) (only parsing).
Notation wpspec_equiv := (wpspec_relation (flip equiv)) (only parsing).

Definition wpspec_relation_fupd {PROP : bi} `{BiFUpd PROP} (R : relation PROP)
    {ARGS : Type} {RESULT : Type}
    (wpp2 : WpSpec PROP ARGS RESULT)
    (wpp1 : WpSpec PROP ARGS RESULT) : Prop :=
  (** We use a single [K] rather than pointwise equal [K1], [K2] for
      compatibility with [fs_entails_fupd], [fs_impl_fupd]. *)
  forall xs K Ke, R (wpp1 xs K Ke)
               (|={top}=> wpp2 xs (λ v, |={top}=> K v) (λ v, |={top}=> Ke v))%I.
#[global] Instance: Params (@wpspec_relation_fupd) 4 := {}.

Notation wpspec_entails_fupd := (wpspec_relation_fupd bi_entails) (only parsing).

Definition wpspec_relationI {PROP : bi}
    (R : PROP -> PROP -> PROP)
    {ARGS : Type} {RESULT : Type}
    (R' : (RESULT -> PROP) -> (RESULT -> PROP))
    (Re' : (RESULT -> PROP) -> (RESULT -> PROP))
    (wpp2 : WpSpec PROP ARGS RESULT)
    (wpp1 : WpSpec PROP ARGS RESULT) : PROP :=
  ∀ xs K Ke, R (wpp1 xs K Ke) (wpp2 xs (R' K) (Re' Ke)).

#[global] Instance: Params (@wpspec_relationI) 5 := {}.

Notation wpspec_wand := (wpspec_relationI bi_wand id) (only parsing).
Notation wpspec_wand_fupd :=
  (wpspec_relationI (λ P1 P2, P1 -∗ |={⊤}=> P2)%I (λ K v, |={⊤}=> K v)%I) (only parsing).

Section wpspec_relations.
  Context {ARGS RESULT : Type}.
  Context `{!BiEntailsN PROP} `{!BiFUpd PROP}.

  #[local] Notation wpspec_relation R := (@wpspec_relation PROP R ARGS RESULT).

  #[global] Instance wpspec_relation_refl (R : relation PROP) :
    Reflexive R ->
    Reflexive (wpspec_relation R).
  Proof. unfold wpspec_relation. naive_solver. Qed.
  #[global] Instance wpspec_relation_symm (R : relation PROP) :
    Symmetric R ->
    Symmetric (wpspec_relation R).
  Proof. unfold wpspec_relation. naive_solver. Qed.
  #[global] Instance wpspec_relation_trans (R : relation PROP) :
    Transitive R ->
    Transitive (wpspec_relation R).
  Proof. unfold wpspec_relation. naive_solver. Qed.

  Lemma wpspec_equiv_spec wpp1 wpp2 :
    wpspec_relation (≡) wpp1 wpp2 <->
    wpspec_relation (⊢) wpp1 wpp2 /\
    wpspec_relation (⊢) wpp2 wpp1.
  Proof.
    split.
    - intros Hwpp. by split=>vs K Ke; rewrite (Hwpp vs K).
    - intros [] vs K Ke. by split'.
  Qed.

  Lemma wpspec_equiv_dist wpp1 wpp2 :
    wpspec_relation (≡) wpp1 wpp2 <->
    ∀ n, wpspec_relation (dist n) wpp1 wpp2.
  Proof.
    split.
    - intros Hwpp n vs K Ke. apply equiv_dist, Hwpp.
    - intros Hwpp vs K Ke. apply equiv_dist=>n. apply Hwpp.
  Qed.

  Notation entailsN := (@entailsN PROP).

  Lemma wpspec_dist_entailsN wpp1 wpp2 n :
    wpspec_relation (dist n) wpp1 wpp2 <->
    wpspec_relation (entailsN n) wpp1 wpp2 /\
    wpspec_relation (entailsN n) wpp2 wpp1.
  Proof.
    split.
    - intros Hwpp. by split=>vs K Ke; apply dist_entailsN; rewrite (Hwpp vs K).
    - intros [] vs K Ke. by apply dist_entailsN.
  Qed.

  Lemma wpspec_entails_entails_fupd
      (wpp1 wpp2 : WpSpec PROP ARGS RESULT) :
    wpspec_entails wpp1 wpp2 -> wpspec_entails_fupd wpp1 wpp2.
  Proof.
    iIntros (EN vs K Ke). rewrite EN.
    iIntros "WPP !>". iApply (spec_internal_frame with "[] WPP").
    iSplit; eauto.
  Qed.
End wpspec_relations.

Require Import skylabs.iris.extra.proofmode.proofmode.

(** Combinators for building [WpSpec]s *)
Section with_AR.
  Context {PROP : bi}.
  Context {A : Type} {R : Type}.

  #[local] Notation WPP := (WpSpec PROP A R).

  (** [add_with T wpp] adds [T] as logical variable to [wpp] *)
  #[program] Definition add_with {T : Type@{universes.Quant}} (wpp : T -> WPP) (name : PrimString.string) (_ : dummy_prop) : WPP :=
    {| spec_internal := funI args' P Q Qe args K Ke => ∃ x : NamedBinder T name, (wpp x).(spec_internal) args' P Q Qe args K Ke |}.
  Next Obligation.
    intros. simpl.
    iIntros "A B"; iDestruct "B" as (b) "B"; iExists b; iRevert "B"; iApply spec_internal_frame; iAssumption.
  Qed.
  Next Obligation.
    simpl; intros.
    setoid_rewrite bi.sep_exist_l.
    rewrite bi.exist_exist.
    apply bi.exist_proper; intro.
    rewrite -arg_ok. done.
  Qed.
  Next Obligation.
    simpl; intros.
    rewrite bi.sep_exist_l.
    apply bi.exist_proper; intro.
    by rewrite pre_ok.
  Qed.
  Next Obligation.
    simpl; intros.
    apply bi.exist_proper; intro.
    by rewrite post_ok.
  Qed.
  Next Obligation.
    by simpl; intros; f_equiv => ?; rewrite post_except_ok.
  Qed.

  (** [add_pre P wpp] adds [P] as a pre-condition to [wpp] *)
  #[program] Definition add_pre (P : PROP) (wpp : WPP) : WPP :=
    {| spec_internal := funI args' PRE Q args K =>
         wpp.(spec_internal) args' (P :: PRE) Q args K |}.
  Next Obligation.
    intros; simpl; iIntros "A B"; iRevert "B"; iApply spec_internal_frame; iAssumption.
  Qed.
  Next Obligation.
    simpl; intros. by rewrite -arg_ok.
  Qed.
  Next Obligation.
    simpl; intros. do 3 rewrite pre_ok.
    rewrite assoc (comm _ P) -assoc. done.
  Qed.
  Next Obligation.
    simpl; intros. by rewrite post_ok.
  Qed.
  Next Obligation.
    simpl; intros. by rewrite post_except_ok.
  Qed.

  (** [add_post_with P wpp] adds [P result] as a post-condition to [wpp]

      TODO: while simple, this produces iterated magic wands rather than a single
      magic wand, which is much nicer to deal with.
   *)
  #[program] Definition add_post_with (P : R -> PROP) (wpp : WPP) : WPP :=
    {| spec_internal := funI args' PRE Q =>
         wpp.(spec_internal) args' PRE (P :: Q) |}.
  Next Obligation.
    simpl; intros.
    iIntros "A"; by iApply spec_internal_frame.
  Qed.
  Next Obligation.
    simpl; intros. by rewrite arg_ok.
  Qed.
  Next Obligation.
    simpl; intros; by rewrite pre_ok.
  Qed.
  Next Obligation.
    simpl; intros. by rewrite -post_ok.
  Qed.
  Next Obligation.
    simpl; intros. by rewrite -post_except_ok.
  Qed.

  (** [add_post P wpp] adds [P : PROP] as a post-condition to [wpp]
   *)
  Definition add_post := fun p => add_post_with (fun _ => p).

  #[program] Definition add_except_post_with (P : R -> PROP) (wpp : WPP) : WPP :=
    {| spec_internal := funI args' PRE Q Qe =>
         wpp.(spec_internal) args' PRE Q (P :: Qe) |}.
  Next Obligation.
    simpl; intros.
    iIntros "A"; by iApply spec_internal_frame.
  Qed.
  Next Obligation.
    simpl; intros. by rewrite arg_ok.
  Qed.
  Next Obligation.
    simpl; intros; by rewrite pre_ok.
  Qed.
  Next Obligation.
    simpl; intros. by rewrite -post_ok.
  Qed.
  Next Obligation.
    simpl; intros. by rewrite -post_except_ok.
  Qed.

  Definition add_except_post := fun p => add_except_post_with (fun _ => p).

  #[global] Instance WpSpec_SpecGen : SpecGen PROP WPP :=
    {| classy.add_pre := add_pre
     ; classy.add_except_post := add_except_post
     ; classy.add_post := add_post
     ; classy.add_with := @add_with |}.

End with_AR.

#[global] Instance: Params (@add_with) 5 := {}.
#[global] Instance: Params (@add_pre) 3 := {}.
#[global] Instance: Params (@add_post_with) 3 := {}.
#[global] Instance: Params (@add_post) 3 := {}.
#[global] Instance: Params (@add_except_post_with) 3 := {}.
#[global] Instance: Params (@add_except_post) 3 := {}.

Section list_arg.
  Context {PROP : bi}.
  Context {A : Type}.

  #[local] Notation WPP R := (WpSpec PROP A R).

  Section list_local.
    Context {T : Type}.
    #[local] Fixpoint rev_append (ls ls' : list T) : list T :=
      match ls with
      | nil => ls'
      | l :: ls => rev_append ls (l :: ls')
      end.
  End list_local.

  (** [add_arg v wpp] adds an argument with value [v] to
      the beginning of [wpp].
   *)
  #[program] Definition add_arg {R} (v : A) (wpp : WPP R) : WPP R :=
    {| spec_internal := funI args' Q =>
         wpp.(spec_internal) (v :: args') Q |}.
  Next Obligation.
    simpl; intros.
    iIntros "A"; destruct args'; by iApply spec_internal_frame.
  Qed.
  Next Obligation.
    simpl; intros. by rewrite -arg_ok.
  Qed.
  Next Obligation.
    simpl; intros. by rewrite pre_ok.
  Qed.
  Next Obligation.
    simpl; intros. by rewrite post_ok.
  Qed.
  Next Obligation.
    simpl; intros. by rewrite post_except_ok.
  Qed.

  Lemma add_arg_nil_contra {R} (v : A) (wpp : WPP R) (PQ PQe : R -> PROP) :
        add_arg v wpp [] PQ PQe ⊢ False.
  Proof.
    iIntros "A"; unfold add_arg.
    destruct wpp; cbn.
    rewrite -(app_nil_l [v]) arg_ok0.
    iDestruct "A" as (?) "[%CONTRA _]".
    iPureIntro.
    discriminate.
  Qed.

  #[program] Definition add_args {R} (vs : list A) (wpp : WPP R) : WPP R :=
    {| spec_internal := funI args' Q =>
                          wpp.(spec_internal) (rev_append vs args') Q |}.
  Next Obligation.
    simpl. intros.
    iIntros "A"; by iApply spec_internal_frame.
  Qed.
  Next Obligation.
    simpl; intros.
    change (rev_append vs (acc_args ++ [A0])) with (List.rev_append vs (acc_args ++ [A0])).
    rewrite rev_append_rev assoc.
    rewrite arg_ok.
    rewrite -rev_append_rev. done.
  Qed.
  Next Obligation.
    simpl; intros. by rewrite pre_ok.
  Qed.
  Next Obligation.
    simpl; intros; by rewrite post_ok.
  Qed.
  Next Obligation.
    simpl; intros; by rewrite post_except_ok.
  Qed.

  #[global] Instance WpSpec_WithArg {R} : WithArg (WPP R) A :=
    {| classy.add_arg := @add_arg _
     ; classy.add_args := @add_args _ |}.

End list_arg.

Section post_val.
  Context {PROP : bi} {ARG : Type} {RESULT : Type}.

  (* Fixpoint list_sep_into (ls : list PROP) (P : PROP) (Pe : PROP) : PROP := *)
  Fixpoint list_sep_into (ls : list PROP) (P : PROP) : PROP :=
    match ls with
    | nil => P
    | l :: ls => list_sep_into ls (l ∗ P) (* l ∗ list_sep_into ls P *)
    end.

  Lemma list_sep_into_take : forall ls P,
      list_sep_into ls P ⊣⊢ P ∗ list_sep_into ls emp%I.
  Proof.
    induction ls; simpl; intros.
    - split'; eauto. iIntros "[$ _]".
    - rewrite IHls. symmetry. rewrite IHls. rewrite !assoc bi.sep_emp (comm _ a). done.
  Qed.

  #[local] Ltac take_all :=
    try change @rev_append with List.rev_append ;
    repeat match goal with
           | |- context [ list_sep_into _ ?X ] =>
               lazymatch X with
               | emp => fail
               | _ => rewrite (list_sep_into_take _ X)
               end
      end.

  Lemma list_sep_into_frame : forall ls P P',
    (P -∗ P')
    (* (P -∗ P') ∧ (Pe -∗ Pe') *)
    ⊢ list_sep_into ls P -∗ list_sep_into ls P'.
  Proof. Admitted.
  (*   intros. *)
  (*   elim: ls => [|l ls ->] /=. *)
  (*   - iIntros "A B"; iSplit. *)
  (*     + by rewrite !bi.and_elim_l; iApply "A". *)
  (*     + by rewrite !bi.and_elim_r; iApply "A". *)
  (*   - by iIntros "A [$ B]"; iApply "A". *)
  (* Qed. *)

  Lemma list_sep_into_app : forall ls ls' P,
      list_sep_into (ls ++ ls') P ⊣⊢ list_sep_into ls (list_sep_into ls' P).
  Proof. Admitted.
  (*   induction ls; simpl; eauto. *)
  (*   - by intros; rewrite bi.and_idem. *)
  (*   - by move => ls' P Pe; rewrite IHls. *)
  (* Qed. *)
  (* Lemma list_sep_into_rev : forall ls P Pe, *)
  (*     list_sep_into (rev ls) P Pe ⊣⊢ list_sep_into ls P Pe. *)
  (* Proof. *)
  (*   induction ls; simpl; intros; eauto. *)

  (*   rewrite list_sep_into_app IHls /=. *)
  (*   rewrite -IHls. rewrite list_sep_into_app. *)
  (*   Search (_ ∧ (_ ∗ _))%I. *)
  (*   simpl. done. *)
  (* Qed. *)

  (* We opt to reify this to avoid adding extra equalities when we do not actually need them. arguments that are awkward *)
  Inductive _post : Type :=
  | WITH [t : Type@{universes.Quant}] (_ : t -> _post) (_ : PrimString.string) (_ : dummy_prop)
  | DONE (_ : RESULT) (_ : PROP).

  Fixpoint _postD (p : _post) (ls : list (RESULT -> PROP)) (K : RESULT -> PROP) : PROP :=
    match p with
    | WITH f _name _ => ∀ x, _postD (f x) ls K (* TODO: using the name here gets in the way of proofs. *)
    | DONE r P => list_sep_into ((fun p => p r) <$> ls) P -∗ K r
    end.
  #[global] Coercion _postD : _post >-> Funclass.

  Lemma _postD_frame p ls : forall K K',
      (∀ r, K r -∗ K' r) ⊢ _postD p ls K -∗ _postD p ls K'.
  Proof.
    induction p; simpl; intros.
    - iIntros "A B" (?); iApply (H with "A"). eauto.
    - iIntros "A B C"; iApply "A"; by iApply "B".
  Qed.
  Lemma _postD_proper p ls : forall K K',
      (forall x, K x ⊣⊢ K' x) ->
      (_postD p ls K ⊣⊢ _postD p ls K').
  Proof.
    induction p; simpl; intros.
    - apply bi.forall_proper; intro; eauto.
    - apply bi.wand_proper; eauto.
  Qed.

  #[program] Definition start_post_list (P Pe : _post) : WpSpec PROP ARG RESULT :=
    {| spec_internal args' PRE POST POSTe :=
        funI args K Ke => [| args = rev_append args' nil |] ∗
                         list_sep_into PRE
                           (_postD P POST K ∧ _postD Pe POSTe Ke)
    |}.
  Next Obligation.
    simpl; intros.
    iIntros "A [$ B]"; iRevert "B"; iApply list_sep_into_frame.
    iIntros "B"; iSplit.
    - rewrite !bi.and_elim_l.
      by iRevert "B"; iApply _postD_frame.
    - rewrite !bi.and_elim_r.
      iRevert "B"; iApply _postD_frame.
      iApply "A".
      iApply _postD_frame; eauto.
  Qed.
  Next Obligation.
    simpl; intros.
    setoid_rewrite (assoc _ [| _ |] [| _ |]).
    setoid_rewrite (comm _ [| _ |] [| _ |]).
    setoid_rewrite <- (assoc _ [| _ |] [| _ |]).
    rewrite ex_eq'.
    have ->: (rev_append (acc_args ++ [A]) [] = A :: rev_append acc_args []); eauto.
    change (@rev_append) with (@List.rev_append).
    rewrite !rev_append_rev !rev_app_distr /=. done.
  Qed.
  Next Obligation.
    simpl; intros.
    rewrite assoc (comm _ P0 [| _ |]) -assoc.
    apply bi.sep_proper; eauto.
    rewrite list_sep_into_take.
    symmetry.
    rewrite list_sep_into_take.
    rewrite assoc. done.
  Qed.
  Next Obligation.
    simpl; intros.
    apply bi.sep_proper; eauto.
    rewrite list_sep_into_take; symmetry; rewrite list_sep_into_take.
    apply bi.sep_proper; eauto.
    induction P; simpl.
    - apply bi.forall_proper; eauto.
    - rewrite bi.wand_curry. apply bi.wand_proper; eauto.
      rewrite fmap_app.
      rewrite list_sep_into_app. simpl.
      rewrite list_sep_into_take; symmetry; rewrite list_sep_into_take.
      rewrite (comm _ _ (P0 r)) assoc. done.
  Qed.

  #[program,global] Instance WpSpec_WithPost : WithPost PROP (WpSpec PROP ARG RESULT) RESULT :=
    {| classy.start_post := start_post_list
     ; post_with := @WITH
     ; post_ret := @DONE |}.

End post_val.

Section bind.
  Context {PROP : bi} {ARG ARG' RESULT RESULT' : Type}.

  (** [wp_spec_bind wp a K] effectively forwards to the specification of [wp]
      evaluated with the arguments [a] and binds the result of the call passing
      it to [cont].

      This is used to "wrap" a function specification *and produce another type*.

      It is effectively the same as:

      [[
      \pre{K} wp a K
      \post{res' ..}[...] K res' ** ...
      ]]

      where [res'] is the return value of [wp].

      NOTE: This is still experimental.
   *)
  #[program] Definition wp_spec_bind (wp : WpSpec PROP ARG RESULT) (a : list ARG)
             (cont : RESULT -> @_post PROP RESULT')
    : WpSpec PROP ARG' RESULT' :=
    {| spec_internal := funI args PRE POST args' K => [| rev_append args nil = args' |] ∗
                          list_sep_into PRE ((wp a) (fun r => _postD (cont r) POST K))
    |}.
  Next Obligation.
    simpl. intros.
    iIntros "A [$ B]"; iRevert "B"; iApply list_sep_into_frame.
    iApply spec_internal_frame.
    iIntros (?); iApply _postD_frame. done.
  Qed.
  Next Obligation.
    simpl; intros.
    change @rev_append with List.rev_append.
    rewrite -!rev_alt.
    rewrite rev_app_distr/=.
    split'.
    - iIntros "[<- A]".
      iExists _; iSplitR; eauto.
    - iIntros "A"; iDestruct "A" as (?) "(-> & <- & A)".
      iSplitR; eauto.
  Qed.
  Next Obligation.
    simpl; intros.
    rewrite list_sep_into_take; symmetry; rewrite list_sep_into_take.
    split'.
    - iIntros "($ & $ & $ & $)".
    - iIntros "($ & [$ $] & $)".
  Qed.
  Next Obligation.
    simpl; intros.
    apply bi.sep_proper; eauto.
    rewrite list_sep_into_take; symmetry; rewrite list_sep_into_take.
    apply bi.sep_proper; eauto.
    apply spec_internal_proper. intro.
    induction (cont x); simpl; eauto.
    - apply bi.forall_proper; eauto.
    - rewrite bi.wand_curry. apply bi.wand_proper; eauto.
      rewrite fmap_app.
      rewrite list_sep_into_app.
      rewrite list_sep_into_take; symmetry; rewrite list_sep_into_take.
      simpl.
      split'.
      + iIntros "[[$ $] $]".
      + iIntros "[[$ $] $]".
  Qed.

  Lemma wp_spec_bind_add_post (P : PROP) spec aargs aas aps aqs args K KONT :
          spec_internal (wp_spec_bind (add_post P spec) aargs KONT) aas aps aqs args K
      ⊣⊢ spec_internal (wp_spec_bind spec aargs KONT) aas aps aqs args (funI x => P -∗ K x).
  Proof.
    intros. rewrite /wp_spec_bind/=.
    apply bi.sep_proper; eauto.
    rewrite list_sep_into_take; symmetry; rewrite list_sep_into_take.
    apply bi.sep_proper; eauto.
    change ([fun _ => P]) with ([] ++ [fun _ : RESULT => P]).
    rewrite post_ok.
    apply spec_internal_proper.
    intros.
    induction KONT; simpl.
    - split'.
      + iIntros "A B" (a).
        iSpecialize ("A" $! a).
        iRevert "A".
        iApply _postD_frame.
        iIntros (?) "A"; iApply "A"; done.
      + iIntros "A" (a).
        rewrite H. iIntros "B".
        iDestruct ("A" with "B") as "A".
        iApply "A".
    - split'.
      + iIntros "A B C". iApply ("A" with "C B").
      + iIntros "A B C". iApply ("A" with "C B").
  Qed.

  Lemma wp_spec_bind_add_pre P spec aargs aas aps aqs args K KONT :
          spec_internal (wp_spec_bind (add_pre P spec) aargs KONT) aas aps aqs args K
      ⊣⊢ P ∗ spec_internal (wp_spec_bind spec aargs KONT) aas aps aqs args K.
  Proof.
    intros. rewrite /wp_spec_bind/=.
    rewrite list_sep_into_take; symmetry; rewrite list_sep_into_take.
    rewrite pre_ok.
    split'.
    - iIntros "($ & $ & $ & $)".
    - iIntros "($ & [$ $] & $)".
  Qed.

  Lemma wp_spec_bind_add_with (T : Type) name i (spec : T → _) aargs aas aps aqs args K KONT :
      spec_internal (wp_spec_bind (add_with spec name i) aargs KONT) aas aps aqs args K
                    ⊣⊢ (∃ x : T, spec_internal (wp_spec_bind (spec x) aargs KONT) aas aps aqs args K).
  Proof.
    intros; simpl.
    rewrite list_sep_into_take.
    split'.
    * iIntros "[$ [A B]]".
      iDestruct "A" as (a) "A".
      iExists a. rewrite (list_sep_into_take _ (spec _ _ _)).
      iFrame.
    * iIntros "A".
      iDestruct "A" as (a) "[$ A]".
      rewrite list_sep_into_take.
      iDestruct "A" as "[A $]".
      iExists a. eauto.
  Qed.

  #[global] Instance wp_spec_bind_ne n :
    Proper (dist n ==> eq ==> eq ==> dist n) wp_spec_bind.
  Proof.
    repeat red; rewrite /wp_spec_bind /=.
    intros ?? H ??? ??? ??. subst. f_equiv. by apply H.
  Qed.

  #[global] Instance wp_spec_bind_proper :
    Proper (equiv ==> eq ==> eq ==> equiv) wp_spec_bind.
  Proof.
    repeat red; rewrite /wp_spec_bind /=.
    intros ?? H ??? ??? ??. subst. f_equiv. by apply H.
  Qed.
End bind.

#[global] Instance: Params (@wp_spec_bind) 5 := {}.

#[global] Instance add_with_ne PROP A R T n :
  Proper (pointwise_relation _ (dist n) ==> eq ==> eq ==> dist n) (@add_with PROP A R T).
Proof.
  repeat red; rewrite /add_with/wpspec_relation/=; intros ?? H ?? ? ?? ? ??.
  f_equiv. f_equiv. by apply H.
Qed.
#[global] Instance add_with_proper PROP A R T :
  Proper (pointwise_relation _ equiv ==> eq ==> eq ==> equiv) (@add_with PROP A R T).
Proof.
  repeat red; rewrite /add_with/wpspec_relation/=; intros ?? H ?? ? ?? ? ??.
  f_equiv. f_equiv. by apply H.
Qed.

#[global] Instance add_pre_ne PROP A R :
  NonExpansive2 (@add_pre PROP A R).
Proof.
  repeat red; rewrite /add_pre/wpspec_relation/=; intros n x y ? ?? H ??.
  rewrite -(app_nil_r [x]) -(app_nil_r [y]) !pres_ok.
  f_equiv. solve_proper. by apply H.
Qed.
#[global] Instance add_pre_proper PROP A R :
  Proper (equiv ==> equiv ==> equiv) (@add_pre PROP A R).
Proof. exact : ne_proper_2. Qed.

#[global] Instance add_post_with_ne PROP A R n :
  Proper (eq ==> dist n ==> dist n)
         (@add_post_with PROP A R).
Proof.
  repeat red; rewrite /add_post/wpspec_relation/=; intros x y ? ?? H ??.
  rewrite -(app_nil_l [x]) -(app_nil_l [y]) !posts_ok.
  subst. by apply H.
Qed.
#[global] Instance add_post_with_proper PROP A R :
  Proper (eq ==> equiv ==> equiv)
         (@add_post_with PROP A R).
Proof.
  do 6 red; rewrite /add_post/wpspec_relation/=; intros x y ? ?? H ??.
  rewrite -(app_nil_l [x]) -(app_nil_l [y]) !posts_ok.
  subst. by apply H.
Qed.

#[global] Instance add_post_ne PROP A R n :
  Proper (eq ==> dist n ==> dist n)
         (@add_post PROP A R).
Proof.
  repeat red; intros. apply add_post_with_ne; eauto. by subst.
Qed.
#[global] Instance add_post_proper PROP A R :
  Proper (eq ==> equiv ==> equiv)
         (@add_post PROP A R).
Proof.
  repeat red; intros. apply add_post_with_proper; eauto. by subst.
Qed.

#[global] Instance list_sep_into_ne {PROP : bi} n :
  Proper (Forall2 (dist n) ==> dist n ==> dist n) (@list_sep_into PROP).
Proof.
  repeat red; induction 1 as [|?????? IH]; eauto.
  intros. apply IH. solve_proper.
Qed.
#[global] Instance add_arg_ne {PROP : bi} {A R} (x : A) :
  NonExpansive (@add_arg PROP A R x).
Proof.
  repeat red. rewrite /add_arg/=. intros n ?? H ??.
  rewrite -(app_nil_l [x]) !arg_ok.
  do 3 f_equiv. by apply H.
Qed.
#[global] Instance add_arg_proper {PROP : bi} {A R} (x : A) :
  Proper (equiv ==> equiv) (@add_arg PROP A R x).
Proof. exact : ne_proper. Qed.

#[global] Instance wp_specD_ne {PROP : bi} {A R} n
  : Proper (dist n ==> eq ==> eq ==> dist n) (@wp_specD PROP A R).
Proof. repeat red; intros ?? H ??? ???; subst; by apply H. Qed.
#[global] Instance wp_specD_proper {PROP : bi} {A R}
  : Proper (equiv ==> eq ==> eq ==> equiv) (@wp_specD PROP A R).
Proof. repeat red; intros ?? H ??? ???; subst; by apply H. Qed.

Lemma add_with_equiv {PROP : bi} {ARG RESULT : Type} : forall T name i (PQ : T -> WpSpec PROP ARG RESULT) args K,
    add_with PQ name i args K ⊣⊢ (∃ x, wp_specD (PQ x) args K).
Proof. split'; intros; iIntros "A"; iDestruct "A" as (x) "A"; iExists x; iApply "A". Qed.
Lemma spec_add_with {PROP : bi} {ARG RESULT : Type} : forall T name i (PQ : T -> WpSpec PROP ARG RESULT) args K,
    (∃ x : NamedBinder _ name, wp_specD (PQ x) args K) ⊢ add_with PQ name i args K.
Proof. intros; by rewrite add_with_equiv. Qed.

Lemma add_arg_equiv {PROP : bi} {ARG RESULT : Type} : forall v (PQ : WpSpec PROP ARG RESULT) args K,
    add_arg v PQ args K ⊣⊢
    match args with
    | nil => False
    | v' :: vs => [| v = v' |] ∗ wp_specD PQ vs K
    end.
Proof.
  intros; destruct args; [| cbn].
  - split'; last by iIntros "[]".
    by apply add_arg_nil_contra.
  - rewrite -(app_nil_l [v]) arg_ok.
    split';
      [ iIntros "A"; iDestruct "A" as (args') "[%Hargs A]"; inversion Hargs; subst
      | iIntros "[-> A]"; iExists args
      ].
    all: by eauto.
Qed.
Lemma spec_add_arg {PROP : bi} {ARG RESULT : Type} : forall v (PQ : WpSpec PROP ARG RESULT) args K,
    match args with
    | nil => False
    | v' :: vs => [| v = v' |] ∗ wp_specD PQ vs K
    end ⊢ add_arg v PQ args K.
Proof. intros; by rewrite add_arg_equiv. Qed.

Lemma add_pre_equiv {PROP : bi} {ARG RESULT : Type} : forall P (PQ : WpSpec PROP ARG RESULT) args K,
    add_pre P PQ args K ⊣⊢ P ∗ PQ args K.
Proof.
  intros; rewrite /wp_specD/=; rewrite pre_ok. done.
Qed.
Lemma spec_add_pre {PROP : bi} {ARG RESULT : Type} : forall P (PQ : WpSpec PROP ARG RESULT) args K,
    P ∗ PQ args K ⊢ add_pre P PQ args K.
Proof. intros; by rewrite add_pre_equiv. Qed.

Lemma add_post_equiv {PROP : bi} {ARG RESULT : Type} : forall P (PQ : WpSpec PROP ARG RESULT) args K,
    add_post P PQ args K ⊣⊢ PQ args (fun res => P -∗ K res).
Proof.
  intros. rewrite /wp_specD/=.
  change [fun _ => P] with ([] ++ [fun _ : RESULT => P]).
  rewrite post_ok. done.
Qed.
Lemma spec_add_post {PROP : bi} {ARG RESULT : Type} : forall P (PQ : WpSpec PROP ARG RESULT) args K,
    PQ args (fun res => P -∗ K res) ⊢ add_post P PQ args K.
Proof. intros; by rewrite add_post_equiv. Qed.

Lemma add_prepost_equiv {PROP : bi} {ARG RESULT : Type} : forall P (PQ : WpSpec PROP ARG RESULT) args K,
    add_prepost P PQ args K ⊣⊢ P ∗ PQ args (fun res => P -∗ K res).
Proof.
  intros. rewrite /add_prepost.
  by rewrite -add_pre_equiv -add_post_equiv.
Qed.
Lemma spec_add_prepost {PROP : bi} {ARG RESULT : Type} : forall P (PQ : WpSpec PROP ARG RESULT) args K,
    P ∗ PQ args (fun res => P -∗ K res) ⊢ add_prepost P PQ args K.
Proof. intros; by rewrite add_prepost_equiv. Qed.

Arguments list_sep_into {PROP} !_ _/.
Arguments rev_append {T} !_ _.

Coercion wp_specD : WpSpec >-> Funclass.
