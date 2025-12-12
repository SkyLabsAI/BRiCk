(*
 * Copyright (C) 2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bluerock.prelude.base.
Require Import bluerock.prelude.numbers.
Require bluerock.prelude.uint63.

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

Module LeibnizComparison.
  (** [LeibnizComparison] states that the comparison function
    implies provable equality. This allows deriving [EqDecision]
    from [LeibnizComparison] (using [from_comparison]).
    This avoids the complexity of implementing both a comparison
    function and a equality decision instance.
   *)
  Class C {T} (cmp : T -> T -> comparison) : Prop :=
    cmp_eq : forall a b, cmp a b = Eq -> a = b.
  Arguments cmp_eq {_} _ {_} _ _.

  Lemma comparison_refl {A cmp} {C : Comparison cmp} :
    forall a : A, cmp a a = Eq.
  Proof.
    intros.
    generalize (compare_antisym a a).
    destruct (cmp a a); simpl; eauto; inversion 1.
  Qed.

  Lemma comparison_not_eq {A cmp} {C : Comparison cmp} :
    forall a b : A, cmp a b <> Eq -> a <> b.
  Proof.
    intros; intro. subst. apply H. apply comparison_refl.
  Qed.
  Lemma comparison_not_eq_Lt {A cmp} {C : Comparison cmp} :
    forall {a b : A}, cmp a b = Lt -> a <> b.
  Proof.
    intros; intro. subst. eapply (comparison_not_eq b b); congruence.
  Qed.
  Lemma comparison_not_eq_Gt {A cmp} {C : Comparison cmp} :
    forall {a b : A}, cmp a b = Gt -> a <> b.
  Proof.
    intros; intro. subst. eapply (comparison_not_eq b b); congruence.
  Qed.

  Definition by_prim_tag {T} (f : T -> PrimInt63.int) {Hinj : Inj eq eq f}
    : C (fun a b => PrimInt63.compare (f a) (f b)).
  Proof.
    red; move=> ? ? H. apply Hinj.
    rewrite Uint63Axioms.compare_def_spec in H.
    compute in H.
    repeat case_match; try congruence.
    by apply Uint63.eqb_spec.
  Qed.

  Definition from_comparison {A cmp} {Cmp : Comparison cmp} {LC : @C A cmp} : EqDecision A :=
    fun l r => match cmp l r as C return cmp l r = C -> _ with
            | Eq => fun pf => left (LC _ _ pf)
            | Lt => fun pf => right (comparison_not_eq_Lt pf)
            | Gt => fun pf => right (comparison_not_eq_Gt pf)
            end eq_refl.

End LeibnizComparison.
Notation LeibnizComparison := LeibnizComparison.C.
