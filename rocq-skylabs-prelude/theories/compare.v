(*
 * Copyright (C) 2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import skylabs.prelude.base.
Require Import skylabs.prelude.numbers.
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

Module LeibnizComparison.
  (** [LeibnizComparison] states that the comparison function
    implies provable equality. This allows deriving [EqDecision]
    from [LeibnizComparison] (using [from_comparison]).
    This avoids the complexity of implementing both a comparison
    function and a equality decision instance.
   *)
  Class C {T} (cmp : T -> T -> comparison) : Prop :=
    cmp_eq : forall a b, cmp a b = Eq -> a = b.
  #[global] Arguments cmp_eq {_} _ {_} _ _.

  Section with_A.
    Context {A : Type}.
    Implicit Type (a b : A).

    Section with_Comparison.
      Context `{Comp : !Comparison (A := A) cmp}.
      #[local] Set Default Proof Using "Comp".

      Lemma comparison_refl {a} : cmp a a = Eq.
      Proof.
        have := Refine (compare_antisym a a).
        by case: (cmp a a).
      Qed.

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

End LeibnizComparison.
Notation LeibnizComparison := LeibnizComparison.C.
