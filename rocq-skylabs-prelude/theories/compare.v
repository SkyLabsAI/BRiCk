(*
 * Copyright (C) 2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import elpi.apps.NES.NES.
Require Import skylabs.prelude.base.
Require Import skylabs.prelude.numbers.
Require Import skylabs.prelude.list.
Require skylabs.prelude.uint63.

(** ** Generic comparison *)
(**
Inspired by:

Benjamin Grégoire, Jean-Christophe Léchenet, Enrico Tassi.
Practical and Sound Equality Tests, Automatically: Deriving eqType
Instances for Jasmin's Data Types with Coq-Elpi.
CPP 2023.
*)
Section compare.
  #[local] Open Scope positive.
  Import EqNotations.

  (**
  Compare constructors represented as tags and data.
  *)
  Definition compare_ctor {A : Type}
      (**
      constructor numbers (<<#[only(tag)] derive>>)
      *)
      (tag : A -> positive)
      (**
      constructor data (<<#[only(fields)] derive>>)
      *)
      (car : positive -> Type) (data : ∀ a, car (tag a))
      (compare : ∀ p, car p -> car p -> comparison)	(** data comparison *)
      (t : positive) (d : unit -> car t)	(* deconstructed inhabitant of <<A>> *)
      (a : A) : comparison :=
    let ta := tag a in
    let c := Pos.compare ta t in
    match c as c' return c = c' -> comparison with
    | Eq => fun EQ => compare t (d ()) $ rew (Pos.compare_eq _ _ EQ) in data a
    | Lt => fun _ => Gt
    | Gt => fun _ => Lt
    end eq_refl.

  (**
  Compare tags (for trivial constructors)
  *)
  Definition compare_tag {A : Type}
      (tag : A -> positive)
      (t : positive)
      (a : A) : comparison :=
    Pos.compare t (tag a).

End compare.

Definition compare_lex (a : comparison) (b : unit -> comparison) : comparison :=
  match a with
  | Eq => b ()
  | Lt | Gt => a
  end.

Module compare.

  Section derived.
    Context `{!Compare A}.
    #[local] Infix "?=" := (@compare A _).
    Notation "(?=)" := (@compare A _) (only parsing).

    Definition eq (x y : A) : Prop := x ?= y = Eq.
    Definition lt (x y : A) : Prop := x ?= y = Lt.
    Definition le (x y : A) : Prop := x ?= y <> Gt.
    Definition gt (x y : A) : Prop := x ?= y = Gt.
    Definition ge (x y : A) : Prop := x ?= y <> Lt.

    #[global] Instance eq_dec : RelDecision eq.
    Proof. rewrite/eq. solve_decision. Defined.
    #[global] Instance lt_dec : RelDecision lt.
    Proof. rewrite/lt. solve_decision. Defined.
    #[global] Instance le_dec : RelDecision le.
    Proof. rewrite/le. solve_decision. Defined.
    #[global] Instance gt_dec : RelDecision gt.
    Proof. rewrite/gt. solve_decision. Defined.
    #[global] Instance ge_dec : RelDecision ge.
    Proof. rewrite/ge. solve_decision. Defined.

    #[local] Infix "==" := eq.
    #[local] Infix "<" := lt.
    #[local] Infix ">" := gt.

    Lemma compare_spec x y : CompareSpec (x == y) (x < y) (x > y) (x ?= y).
    Proof. rewrite/eq/lt/gt. by destruct (x ?= y); constructor. Qed.

    #[global] Instance eq_equiv `{!Comparison (?=)} : Equivalence eq.
    Proof.
      rewrite /eq. split.
      - intros x. apply comparison_refl.
      - intros x y. by rewrite (compare_antisym y x) => ->.
      - intros x y z. apply compare_trans.
    Qed.

    #[global] Instance le_refl `{!Comparison (?=)} : Reflexive le.
    Proof. move => x. by rewrite /le comparison_refl. Qed.

    #[global] Instance ge_refl `{!Comparison (?=)} : Reflexive ge.
    Proof. move => x. by rewrite /ge comparison_refl. Qed.

    #[global] Instance lt_trans `{!Comparison (?=)} : Transitive lt.
    Proof. rewrite /lt. intros x y z. apply compare_trans. Qed.

    #[global] Instance gt_trans `{!Comparison (?=)} : Transitive gt.
    Proof. rewrite /gt. intros x y z. apply compare_trans. Qed.

    Lemma ordered_type_compare `{!Comparison (?=)} x y : OrderedType.Compare lt eq x y.
    Proof.
      rewrite /lt/eq. destruct (x ?= y) eqn:Hc; try by constructor.
      apply OrderedType.GT. by rewrite compare_antisym Hc.
    Qed.

    (** All these relations are antisymmetric wrt eq.
    No instance for [eq] since that case is degenerate (see [anti_symm_refl]). *)

    Ltac solve_antisymm R :=
      intros x y; rewrite /R /eq (compare_antisym y x); by destruct (x ?= y).
      (* intros x y; unfold R; rewrite /eq (compare_antisym y x); by destruct (x ?= y). *)

    #[global] Instance lt_anti_symm `{!Comparison (?=)} : AntiSymm eq lt.
    Proof. solve_antisymm lt. Qed.

    #[global] Instance le_anti_symm `{!Comparison (?=)} : AntiSymm eq le.
    Proof. solve_antisymm le. Qed.

    #[global] Instance gt_anti_symm `{!Comparison (?=)} : AntiSymm eq gt.
    Proof. solve_antisymm gt. Qed.

    #[global] Instance ge_anti_symm `{!Comparison (?=)} : AntiSymm eq ge.
    Proof. solve_antisymm ge. Qed.

    (** [le] and [ge] are total. *)
    #[global] Instance le_total `{!Comparison (?=)} : Total le.
    Proof.
      intros x y. rewrite /le (compare_antisym y x).
      case: (x ?= y) => /=; auto.
    Qed.

    #[global] Instance ge_total `{!Comparison (?=)} : Total ge.
    Proof.
      intros x y. rewrite /ge (compare_antisym y x).
      case: (x ?= y) => /=; auto.
    Qed.
  End derived.

  (**
  These notation effects are opt-in because they can interfere with
  existing theory tied to notation scopes like <<nat_scope>> (e.g.,
  <<Peano.lt>> differs from the comparison-based [lt] relation on
  natural numbers).
  *)
  Module Notations.
    Infix "?=" := compare : stdpp_scope.
    Infix "?=@{ A }" := (@compare A _) (only parsing) : stdpp_scope.
    Notation "(?=)" := compare (only parsing) : stdpp_scope.
    Notation "(?=@{ A } )" := (@compare A _) (only parsing) : stdpp_scope.
    Notation "( x ?=.)" := (compare x) (only parsing) : stdpp_scope.
    Notation "(.?= y )" := (fun x => compare x y) (only parsing) : stdpp_scope.

    Infix "<" := lt : stdpp_scope.
    Infix "<@{ A }" := (@lt A _) (only parsing) : stdpp_scope.
    Notation "(<)" := lt (only parsing) : stdpp_scope.
    Notation "(<@{ A } )" := (@lt A _) (only parsing) : stdpp_scope.
    Notation "( x <.)" := (lt x) (only parsing) : stdpp_scope.
    Notation "(.< y )" := (fun x => lt x y) (only parsing) : stdpp_scope.

    Infix "<=" := le : stdpp_scope.
    Infix "<=@{ A }" := (@le A _) (only parsing) : stdpp_scope.
    Notation "(<=)" := le (only parsing) : stdpp_scope.
    Notation "(<=@{ A } )" := (@le A _) (only parsing) : stdpp_scope.
    Notation "( x <=.)" := (le x) (only parsing) : stdpp_scope.
    Notation "(.<= y )" := (fun x => le x y) (only parsing) : stdpp_scope.

    Infix ">" := gt : stdpp_scope.
    Infix ">@{ A }" := (@gt A _) (only parsing) : stdpp_scope.
    Notation "(>)" := gt (only parsing) : stdpp_scope.
    Notation "(>@{ A } )" := (@gt A _) (only parsing) : stdpp_scope.
    Notation "( x >.)" := (gt x) (only parsing) : stdpp_scope.
    Notation "(.> y )" := (fun x => gt x y) (only parsing) : stdpp_scope.

    Infix ">=" := ge : stdpp_scope.
    Infix ">=@{ A }" := (@ge A _) (only parsing) : stdpp_scope.
    Notation "(>=)" := ge (only parsing) : stdpp_scope.
    Notation "(>=@{ A } )" := (@ge A _) (only parsing) : stdpp_scope.
    Notation "( x >=.)" := (ge x) (only parsing) : stdpp_scope.
    Notation "(.>= y )" := (fun x => ge x y) (only parsing) : stdpp_scope.
  End Notations.

End compare.

NES.Begin LeibnizComparison.

  Section with_A.
    Context {A : Type}.
    Implicit Type (a b : A).

    Section with_Comparison.
      Context `{Comp : !Comparison (A := A) cmp}.
      #[local] Set Default Proof Using "Comp".

      (* TODO: make instance? *)
      #[program] Definition from_comparison {LC : C cmp} : EqDecision A := fun l r =>
        match cmp l r as C return cmp l r = C -> _ with
        | Eq => fun pf => left (LC _ _ pf)
        | Lt => fun pf => right _
        | Gt => fun pf => right _
        end eq_refl.
      Next Obligation. intros ** ->. by rewrite -> comparison_refl in *. Qed.
      Next Obligation. intros ** ->. by rewrite -> comparison_refl in *. Qed.
    End with_Comparison.
  End with_A.

  Section with_Compare.
    Context `{!Compare A}.

    Import compare.Notations.

    #[local] Instance eq_anti_symm R :
      C (?=@{A}) ->
      AntiSymm (compare.eq (A := A)) R ->
      AntiSymm (=) R.
    Proof.
      rewrite /AntiSymm /C /compare.eq.
      move=> E AS x y Hxy Hyx.
      exact /E /AS.
    Qed.

    Context `{!C (?=@{A})}.
    Context `{!Comparison (?=@{A})}.

    #[global] Instance lt_anti_symm : AntiSymm (=) (<@{A}) := _.
    #[global] Instance le_anti_symm : AntiSymm (=) (<=@{A}) := _.
    #[global] Instance gt_anti_symm : AntiSymm (=) (>@{A}) := _.
    #[global] Instance ge_anti_symm : AntiSymm (=) (>=@{A}) := _.

    #[global] Instance le_trans : Transitive (<=@{A}).
    Proof using Type*.
      rewrite /compare.le => x y z.
      specialize (compare_trans x y z) as Hc.
      destruct (x ?= y) eqn:Hxy, (y ?= z) eqn:Hyz, (x ?= z) eqn:Hxz => //.
      all: try by destruct (Hc _ eq_refl).
      { rewrite (cmp_eq _ x y Hxy) in Hxz. congruence. }
      { rewrite (cmp_eq _ y z Hyz) in Hxy. congruence. }
    Qed.

    #[global] Instance ge_trans : Transitive (>=@{A}).
    Proof using Type*.
      rewrite /compare.ge => x y z.
      specialize (compare_trans x y z) as Hc.
      destruct (x ?= y) eqn:Hxy, (y ?= z) eqn:Hyz, (x ?= z) eqn:Hxz => //.
      all: try by destruct (Hc _ eq_refl).
      { rewrite (cmp_eq _ x y Hxy) in Hxz. congruence. }
      { rewrite (cmp_eq _ y z Hyz) in Hxy. congruence. }
    Qed.
  End with_Compare.

  Lemma PrimInt63_int_compare_eq (x y : PrimInt63.int) :
    PrimInt63.compare x y = Eq ->
    PrimInt63.eqb x y = true.
  Proof.
    rewrite Uint63Axioms.compare_def_spec /Uint63Axioms.compare_def.
    repeat case_match; congruence.
  Qed.

  Definition by_prim_tag {T} (f : T -> PrimInt63.int) {Hinj : Inj eq eq f}
    : C (fun a b => PrimInt63.compare (f a) (f b)).
  Proof.
    move=> a b E. apply (inj f), Uint63.eqb_spec, PrimInt63_int_compare_eq, E.
  Qed.

NES.End LeibnizComparison.

  Section Compare.
    Context `{cmp : !Compare A, Hcmp : !Comparison (A := A) base.compare}.

    #[global] Instance cmp_antisymm `{Hleib : !LeibnizComparison (T := A) base.compare} :
      Antisymmetric _ eq (compare.le (A := A)).
    Proof using Hcmp.
      move => x y; rewrite /compare.le => Hxy Hyx.
      apply LeibnizComparison.cmp_eq with (cmp := base.compare); first apply Hleib.
      move: Hyx Hxy; rewrite -(inj_iff (R := eq) (S := eq) CompOpp (Inj0 := CompOpp_inj)).
      rewrite -compare_antisym/=.
      by case: (compare x y).
    Qed.

    #[global] Instance cmp_trans :
      Transitive (compare.le (A := A)).
    Proof using Hcmp.
      move => x y z.
      rewrite /compare.le => Hxy Hyz.
      have {}Hxy : base.compare x y = Eq ∨ base.compare x y = Lt
        by case: (base.compare x y) Hxy; [left|right|].
      have {}Hyz : base.compare y z = Eq ∨ base.compare y z = Lt
        by case: (base.compare y z) Hyz; [left|right|].
      move: Hxy Hyz => [] Hxy [] Hyz.
      - by rewrite (compare_trans _ _ _ _ Hxy Hyz).
      - move => Hxz.
        move: Hyz Hxz; rewrite [base.compare x z] base.compare_antisym CompOpp_iff/=.
        move => /(base.compare_trans _ _ _) /[apply].
        by rewrite base.compare_antisym => /CompOpp_iff/=; rewrite Hxy.
      - move => Hxz.
        move: Hxz Hxy; rewrite [base.compare x z] base.compare_antisym CompOpp_iff/=.
        move => /(base.compare_trans _ _ _) /[apply].
        by rewrite base.compare_antisym => /CompOpp_iff/=; rewrite Hyz.
      - by rewrite (compare_trans _ _ _ _ Hxy Hyz).
    Qed.

    #[global] Instance cmp_trichotomy `{LeibnizComparison (T := A) base.compare} :
      Trichotomy (compare.lt (A := A)).
    Proof using Hcmp.
      move => x y.
      case Hxy : (base.compare (Compare := cmp) x y).
      - by move: Hxy => /(LeibnizComparison.cmp_eq _ _ _); right; left.
      - by rewrite /compare.lt Hxy; left.
      - move: Hxy; rewrite /compare.lt base.compare_antisym CompOpp_iff /=.
        by move => ->; right; right.
    Qed.

    #[global] Instance cmp_total :
      Total (compare.le (A := A)).
    Proof using Hcmp.
      move => x y.
      rewrite /compare.le.
      case Hxy : (base.compare (Compare := cmp) x y).
      - by left.
      - by left.
      - move: Hxy; rewrite base.compare_antisym CompOpp_iff /= => ->.
        by right.
    Qed.

    Lemma cmp_absurd {c0 c1 : comparison} {P} (H : c0 = c1) :
      match c0, c1 with
      | Lt, Lt => P -> P
      | Eq, Eq => P -> P
      | Gt, Gt => P -> P
      | _, _ => P
      end.
    Proof. by case: c0 c1 H => [] []. Qed.

  End Compare.

Section comparison.
  Context {A} `{!Compare A}.

  Definition compare_on {B} (f : B -> A) : Compare B :=
    fun x y => base.compare (f x) (f y).

End comparison.

Module sorted.
Section sorted.
  Context {A} `{!Compare A}.

  Definition compare_on {B} (f : B -> A) : Compare B :=
    fun x y => compare (f x) (f y).

  (** Remove duplicates from a sorted list *)
  Definition nub (xs : list A) : list A :=
    let fix go (x : option A) (xs : list A) : list A :=
      match x, xs with
      | None, [] => []
      | None, x :: xs => go (Some x) xs
      | Some x, [] => [x]
      | Some x0, x1 :: xs =>
          if bool_decide (compare.eq x0 x1) then
            go (Some x0) xs
          else
            x0 :: go (Some x1) xs
      end in
    go None xs.

  (** The intersection of two sorted lists *)
  Fixpoint intersection (xs ys : list A) : list A :=
    match xs with
    | [] => []
    | x :: xs =>
        let ys' := drop_while (compare.gt x) ys in
        match ys' with
        | [] => []
        | y :: ys'' =>
            if bool_decide (compare.eq x y) then
              x :: intersection xs ys''
            else
              intersection xs (y :: ys'')
        end
    end.

End sorted.
End sorted.

Section compare_lex.
  Context {A} {cmpA : A -> A -> comparison} `{HcmpA : !Comparison cmpA}.

  #[local] Arguments compare_trans {A f _ x y z c}.

  Lemma compare_eq_trans {x y z c} :
    cmpA x y = c ->
    cmpA y z = Eq ->
    cmpA x z = c .
  Proof using HcmpA.
    case: (decide (c = Eq));
      first by move => ->; apply compare_trans.
    move => Hc Hxy Hyz.
    have Hnot_opp : cmpA x z <> CompOpp c.
    { rewrite compare_antisym => /CompOpp_inj Hzx.
      pose proof (Hzy := compare_trans Hzx Hxy).
      move: Hyz Hzy Hc => - /(f_equal CompOpp).
      by rewrite -compare_antisym /= => -> <-. }
    have Hnot_eq : cmpA x z <> Eq.
    { move: Hyz =>  /(f_equal CompOpp);
        rewrite -compare_antisym /=.
      move => /[swap] /(compare_trans) /[apply].
      by rewrite Hxy. }
    case: (cmpA x z) c Hc Hnot_opp Hnot_eq {Hxy} => // - [] //.
  Qed.

  Lemma eq_compare_trans {x y z c} :
    cmpA x y = Eq ->
    cmpA y z = c ->
    cmpA x z = c .
  Proof using HcmpA.
    case: (decide (c = Eq));
      first by move => ->; apply compare_trans.
    move => Hc Hxy Hyz.
    have Hnot_opp : cmpA x z <> CompOpp c.
    { rewrite compare_antisym => /CompOpp_inj Hzx.
      pose proof (Hzy := compare_trans Hyz Hzx).
      move: Hxy Hzy Hc => - /(f_equal CompOpp).
      by rewrite -compare_antisym /= => -> <-. }
    have Hnot_eq : cmpA x z <> Eq.
    { move: Hxy =>  /(f_equal CompOpp);
        rewrite -compare_antisym /=.
      move => /(compare_trans) /[apply].
      by rewrite Hyz. }
    case: (cmpA x z) c Hc Hnot_opp Hnot_eq {Hyz} => // - [] //.
  Qed.

End compare_lex.

Section compare_lex.
  Context {A} {cmpA : A -> A -> comparison} `{HcmpA : !Comparison cmpA} `{HlcmpA : !compare.LeibnizComparison cmpA}.
  Context {B} {cmpB : B -> B -> comparison} `{HcmpB : !Comparison cmpB} `{HlcmpB : !compare.LeibnizComparison cmpB}.

  Definition lex_comparison : A * B -> A * B -> comparison :=
    fun '(a0,b0) '(a1,b1) => compare.compare_lex (cmpA a0 a1) (fun _ => cmpB b0 b1).

  Lemma compare_lex_inv c0 c1 c2 :
    compare.compare_lex c0 c1 = c2 <->
    if bool_decide (c2 = Eq)
     then c0 = Eq ∧ c1 () = Eq
     else c0 = c2 ∨ (c0 = Eq ∧ c1 () = c2).
  Proof.
    case: bool_decide_reflect c0 => Heq [] /=;
      by intuition; subst.
  Qed.

  #[global] Instance lex_comparison_comparison : Comparison (A := A * B) lex_comparison.
  Proof using HcmpA HcmpB.
    constructor.
    - case => [a0 b0] [a1 b1] /=.
      rewrite [cmpA a0 a1]compare_antisym.
      by case: cmpA => //=; rewrite -compare_antisym.
    - case => [a0 b0] [a1 b1] [a2 b2] c /=.
      rewrite 3!compare_lex_inv.
      case: bool_decide_reflect;
        [ move => {c} _ [Ha01 Hb01] [Ha12 Hb12]
        | move => Hc [Ha01|[Ha01 Hb01]] [Ha12|[Ha12 Hb12]]].
      all: repeat
          lazymatch goal with
          | Hxy : ?cmp ?x ?y = ?c,
            Hyz : ?cmp ?y ?z = ?c
            |- _ =>
              pose proof (compare_trans _ _ _ _ Hxy Hyz) ;
              clear Hxy Hyz
          | Hxy : ?cmp ?x ?y = Eq,
            Hyz : ?cmp ?y ?z = _
            |- _ =>
              pose proof (eq_compare_trans Hxy Hyz) ;
              clear Hxy Hyz
          | Hxy : ?cmp ?x ?y = _,
            Hyz : ?cmp ?y ?z = Eq
            |- _ =>
              pose proof (compare_eq_trans Hxy Hyz) ;
              clear Hxy Hyz
          end.
      all: first [by left | by right| by []].
  Qed.

  #[global] Instance lex_comparison_leibniz_comparison :
    compare.LeibnizComparison (T := A * B) lex_comparison.
  Proof using HlcmpA HlcmpB.
    case => [a0 b0] [a1 b1] /=.
    by move => /compare_lex_inv/= []
         => /(LeibnizComparison.cmp_eq _ _ _) <-
         => /(LeibnizComparison.cmp_eq _ _ _) <-.
  Qed.

End compare_lex.
