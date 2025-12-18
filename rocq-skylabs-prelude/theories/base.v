(*
 * Copyright (c) 2020-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(** "Prelude" for available-everywhere dependencies. *)

Require Import Stdlib.Structures.OrderedType.
Require Export stdpp.prelude.
Require Export stdpp.countable.
Require Export skylabs.prelude.stdpp_ssreflect.
Require Export skylabs.prelude.tc_cond_type.
Require Export skylabs.prelude.notations.
Require Export skylabs.upoly.upoly.
Require skylabs.prelude.tactics.base_dbs. (* For [br_opacity]; import not required. *)

#[global] Hint Opaque elem_of : typeclass_instances.

(** ** Missing from Coq's stdlib *)

Lemma not_or {P Q : Prop} : ~ (P ∨ Q) <-> ~ P ∧ ~ Q.
Proof. tauto. Qed.

Lemma and_proper_l {P Q R} :
  (P -> (Q <-> R)) -> Q ∧ P <-> R ∧ P.
Proof. by split => - [] /[swap] /[dup] HP /H /[apply]. Qed.

Lemma and_proper_r {P Q R} :
  (P -> (Q <-> R)) -> P ∧ Q <-> P ∧ R.
Proof. by split => - [] /[dup] HP /H /[apply]. Qed.

Lemma or_proper_l {P Q R} `{!Decision P} :
  (¬ P -> (Q <-> R)) -> Q ∨ P <-> R ∨ P.
Proof.
  move => H.
  case (decide P).
  - by split; right.
  - by move /H ->.
Qed.

Lemma or_proper_r {P Q R} `{!Decision P} :
  (¬ P -> (Q <-> R)) -> P ∨ Q <-> P ∨ R.
Proof.
  move => /or_proper_l H.
  by rewrite or_comm H or_comm.
Qed.

Lemma iff_impl (A B C : Prop) : (A → B ↔ C) ↔ ((A → B) ↔ (A → C)).
Proof. tauto. Qed.

Lemma iff_and (P Q R : Prop) :
  (P -> Q ↔ R) ->
  (P ∧ Q) <-> (P ∧ R).
Proof. tauto. Qed.

(** Workaround https://github.com/coq/coq/issues/4230. Taken from Software Foundations. *)
#[global] Remove Hints Bool.trans_eq_bool : core.

#[global] Set Suggest Proof Using. (* also warns about forgotten [Proof.] *)
#[global] Set Default Proof Using "Type".
(** Disable [Program]'s compiler for pattern matches.
It's more expressive, but it mangles definitions and can cause a quadratic size
explosion. *)
#[global] Unset Program Cases.
#[global] Set Ltac Backtrace.

(** * Small extensions to [stdpp.base] *)

Notation "~~ b" := (negb b) : bool_scope.
Infix "==>" := implb : bool_scope.

(** These associate to the right *)
Notation "[&& b1 & c ]" := (b1 && c) (only parsing) : bool_scope.
Notation "[&& b1 , b2 , .. , bn & c ]" := (b1 && (b2 && .. (bn && c) ..)) : bool_scope.

(** Solve decidable goal [P] via [vm_compute] on [bool_decide P]. *)
Ltac vm_decide := apply: bool_decide_eq_true_1; vm_compute; reflexivity.

(** Ensure the given instance isn't already provable. *)
Ltac GUARD_TC := assert_fails (apply _).

(**
Solve [Inhabited foo] goals. Proof using this tactic should be closed with [Qed].
*)
Ltac solve_inhabited := by repeat (apply inhabitant || econstructor).

Lemma TCElemOf_iff {A} (x : A) (l : list A) : TCElemOf x l ↔ x ∈ l.
Proof. split; induction 1; by constructor. Qed.

Lemma iff_forall T P Q :
  (forall i : T, P i <-> Q i) ->
  (forall i : T, P i) <-> (forall i : T, Q i).
Proof. naive_solver. Qed.

#[global] Instance reflexive_proper A :
  Proper (pointwise_relation A (pointwise_relation A iff) ==> iff) Reflexive.
Proof.
  unfold Reflexive=> r1 r2 Heq.
  apply iff_forall => i. by rewrite Heq.
Qed.

#[global] Instance transitive_proper A :
  Proper (pointwise_relation A (pointwise_relation A iff) ==> iff) Transitive.
Proof.
  unfold Reflexive=> r1 r2 Heq.
  apply iff_forall => i.
  apply iff_forall => j.
  apply iff_forall => k.
  by rewrite Heq.
Qed.

#[global] Instance preorder_proper A :
  Proper (pointwise_relation A (pointwise_relation A iff) ==> iff) PreOrder.
Proof. by intros r1 r2 Heq; split => -[]; [rewrite Heq|rewrite -Heq]. Qed.

(** Not an instance, because of the risk of loops. *)
Lemma flip_assoc {A} {R : relation A} `{!Symmetric R} `{!Assoc R f} : Assoc R (flip f).
Proof. intros ???. symmetry. apply: (assoc f). Qed.

Section flip_app.
  Context {A : Type}.

  #[global] Instance flip_app_left_id : LeftId (=) (@nil A) (flip app).
  Proof. apply: right_id. Qed.
  #[global] Instance flip_app_right_id : RightId (=) (@nil A) (flip app).
  Proof. apply: left_id. Qed.
  #[global] Instance flip_app_assoc : Assoc (=) (flip (@app A)).
  Proof. apply: flip_assoc. Qed.
End flip_app.

(** Not an instance to avoid TC resolution loops *)
Lemma subrelation_flip {A} (R S : relation A) :
  subrelation R S -> subrelation (flip R) (flip S).
Proof. intros HR x y ?. exact: HR. Qed.

(** [flip2] *)

#[universes(polymorphic)]
Definition flip2 {A B C D} (f : A -> B -> C -> D) (b : B) (c : C) (a : A) : D := f a b c.
#[global] Arguments flip2 {_ _ _ _} _ _ _ _ / : assert.

Lemma dec_stable_iff `{Decision P} : ¬ ¬ P ↔ P.
Proof. split. apply dec_stable. tauto. Qed.

#[global] Arguments stdpp.base.difference : simpl nomatch.

(** ** Monads *)
(**
We put most notation in [stdpp_scope] (open by default).

We put notation with other purposes, like [let*], in [monad_scope]
(not open by default).

One can locally open [monad_scope], or use notations like <<funM>>,
<<letM*>>.
*)

Declare Scope monad_scope.
Delimit Scope monad_scope with M.

(**
NOTE: We bundle these effects so they can be replayed.
*)
Module Export MonadNotations.

  #[global] Notation "'funM' x .. y => t" :=
    (fun x => .. (fun y => t%M) ..) (only parsing) : function_scope.
  #[global] Notation "'letM*' x , .. , z := t 'in' f" :=
    (mbind (fun x => .. (fun z => f) ..) t%M) (only parsing) : stdpp_scope.
  #[global] Notation "'letM*' := t 'in' f" :=
    (mbind (fun _ : unit => f) t%M) (only parsing) : stdpp_scope.

  #[global] Notation "m >>= f" := (mbind f m) : stdpp_scope.
  #[global] Notation "m ≫= f" := (m >>= f) (only parsing) : stdpp_scope.
  #[global] Notation "m >>=@{ M } f" := (mbind (M:=M) f m) (only parsing) : stdpp_scope.

  #[global] Notation "( m >>=.)" := (fun f => mbind f m) (only parsing) : stdpp_scope.
  #[global] Notation "(.>>= f )" := (mbind f) (only parsing) : stdpp_scope.
  #[global] Notation "(>>=)" := mbind (only parsing) : stdpp_scope.

  #[global] Notation "'let*' x , .. , z := t 'in' f" :=
    (mbind (fun x => .. (fun z => f) ..) t) (only parsing) : monad_scope.
  #[global] Notation "'let*' := t 'in' f" :=
    (mbind (fun _ : unit => f) t) (only parsing) : monad_scope.

End MonadNotations.

(* Very incomplete set of monadic liftings. *)
Definition liftM2 `{MRet M, MBind M} `(f : A → B → C) : M A → M B → M C :=
  λ mx my,
    x ← mx; y ← my; mret (f x y).

(* Less common; name inspired by Haskell. *)
Definition bindM2 `{MBind M} `(f : A → B → M C) : M A → M B → M C :=
  λ mx my,
    x ← mx; y ← my; f x y.

#[global] Notation Unfold x tm :=
  ltac:(let H := eval unfold x in tm in exact H) (only parsing).
#[global] Notation Reduce tm :=
  ltac:(let H := eval red in tm in exact H) (only parsing).
#[global] Notation Hnf tm :=
  ltac:(let H := eval hnf in tm in exact H) (only parsing).
#[global] Notation Cbn tm :=
  ltac:(let H := eval cbn in tm in exact H) (only parsing).
#[global] Notation Beta tm :=
  ltac:(let H := eval cbv beta in tm in exact H) (only parsing).
#[global] Notation Evaluate tm :=
  ltac:(let H := eval vm_compute in tm in exact H) (only parsing).

(**
Useful to force typeclass inference; inspired by math-comp's [!!] notation.
Example:
[suff Hname: Refine (∀ (xs : gset nat), xs ∪ xs = xs).]
*)
#[global] Notation Refine x := (ltac:(refine x)) (only parsing).

(** ** Pairwise disjointness *)
(** Operational type class for pairwise disjointness, with notation
[Xs ##ₚ Ys] and [[##ₚ Xs]]. *)
Class PairwiseDisjoint A := pairwise_disjoint : relation A.
#[global] Hint Mode PairwiseDisjoint ! : typeclass_instances.
#[global] Instance: Params (@pairwise_disjoint) 2 := {}.
Infix "##ₚ" := pairwise_disjoint (at level 70) : stdpp_scope.
Notation "(##ₚ)" := pairwise_disjoint (only parsing) : stdpp_scope.
Notation "( Xs ##ₚ.)" := (pairwise_disjoint Xs) (only parsing) : stdpp_scope.
Notation "(.##ₚ Ys )" := (fun Xs => Xs ##ₚ Ys) (only parsing) : stdpp_scope.

Infix "##ₚ@{ A }" := (@pairwise_disjoint A _) (at level 70, only parsing) : stdpp_scope.
Notation "(##ₚ@{ A } )" := (@pairwise_disjoint A _) (only parsing) : stdpp_scope.

Notation "[##ₚ  Xs ]" := (Xs ##ₚ Xs) (at level 0) : stdpp_scope.
Notation "[##ₚ@{ A }  Xs ]" := (Xs ##ₚ@{A} Xs) (at level 0, only parsing) : stdpp_scope.

(** ** Typeclass operations *)
(** [TCLeq (a ?= b)] expresses [a <= b] in a way that can be proved,
    for some [a]s and [b]s, during typeclass resolution. *)
Variant TCLeq : comparison -> Prop :=
| TCLeq_eq : TCLeq Eq
| TCLeq_lt : TCLeq Lt.
Existing Class TCLeq.
#[global] Existing Instances TCLeq_eq TCLeq_lt.
#[global] Hint Mode TCLeq + : typeclass_instances.

Lemma TCLeq_iff c : TCLeq c <-> c ≠ Gt.
Proof. split. by inversion 1. by destruct c; first [done|constructor]. Qed.
Lemma TCLeq_positive x y : (TCLeq (x ?= y) <-> x <= y)%positive.
Proof. by rewrite TCLeq_iff. Qed.
Lemma TCLeq_Z x y : (TCLeq (x ?= y) <-> x <= y)%Z.
Proof. by rewrite TCLeq_iff. Qed.
Lemma TCLeq_N x y : (TCLeq (x ?= y) <-> x <= y)%N.
Proof. by rewrite TCLeq_iff. Qed.
Lemma TCLeq_nat x y : (TCLeq (x ?= y) <-> x <= y)%nat.
Proof. by rewrite TCLeq_iff Nat.compare_le_iff. Qed.

(** [TCLt (a ?= b)] expresses [a < b] in a way that can be proved,
    for some [a]s and [b]s, during typeclass resolution. *)
Variant TCLt : comparison -> Prop :=
| TCLt_lt : TCLt Lt.
Existing Class TCLt.
#[global] Existing Instance TCLt_lt.
#[global] Hint Mode TCLt + : typeclass_instances.

Lemma TCLt_iff c : TCLt c <-> c = Lt.
Proof. split. by destruct 1. by intros ->. Qed.
Lemma TCLt_positive x y : (TCLt (x ?= y) <-> x < y)%positive.
Proof. by rewrite TCLt_iff. Qed.
Lemma TCLt_Z x y : (TCLt (x ?= y) <-> x < y)%Z.
Proof. by rewrite TCLt_iff. Qed.
Lemma TCLt_N x y : (TCLt (x ?= y) <-> x < y)%N.
Proof. by rewrite TCLt_iff. Qed.
Lemma TCLt_nat x y : (TCLt (x ?= y) <-> x < y)%nat.
Proof. by rewrite TCLt_iff Nat.compare_lt_iff. Qed.

(** Let TC resolution discharge side-conditions [n <> 0] (sometimes). *)
Class NNonZero (n : N) : Prop := N_non_zero : (n ≠ 0)%N.
#[global] Hint Mode NNonZero ! : typeclass_instances.
#[global] Instance N_non_empty p : NNonZero (Npos p).
Proof. done. Qed.

(** Useful when rewriting. *)
Lemma refl_True `(R : relation A) `{!Reflexive R} a : R a a ↔ True.
Proof. done. Qed.

(** Witnessing non-disjointness *)
(** We prove a few lemmas witnessing non-disjointness. Examples
include [list_not_disjoint] in [./list.v] and [set_not_disjoint] in
[./fin_sets.v]. Such lemmas convert non-disjointness into constructive
evidence; for example, turning `¬ X ## Y` when `X, Y : list A` into an
`x : A` s.t. `x ∈ X`, `y ∈ Y`.

Such witnesses can be useful to prove disjointness properties from
ownership. Suppose, for example, that you have a representation
predicate [myList (l : list A) : Rep] for some [A : Type] defined so
that [myList l ** myList k] implies [l ## k]. One way to prove an
observation like [Observe2 [| l ## k |] (myList l) (mList k)] is to

- decide if [l ## k] (possible because lists have finite inhabitants)
  and,

- when they are not disjoint, convert [¬ l ## k] into a witness [x :
  A] such that [x ∈ l], [y ∈ k], and

- use that witness to derive a contradiction from the ownership in
  [myList l ** myList k]. *)

#[global] Hint Mode Reflexive ! ! : typeclass_instances.
#[global] Hint Mode Symmetric ! ! : typeclass_instances.

(** Global notation for [UPoly.ap] *)

Infix "<*>" := UPoly.ap : stdpp_scope.
Infix "<*>@{ F }" := (UPoly.ap (F:=F)) (only parsing) : stdpp_scope.

(** Some default instances (for stdpp monads) *)
#[global,universes(polymorphic)]
Instance applicative_fmap {F} `{!MRet F, !UPoly.Ap F} : FMap F | 1000 := fun _ _ f =>
  UPoly.ap (mret f).
#[global] Arguments applicative_fmap _ _ _ _ _ _ !_ / : simpl nomatch, assert.

#[global,universes(polymorphic)]
Instance monad_ap {M} `{!MBind M, !MRet M} : UPoly.Ap M | 1000 := fun _ _ mf ma =>
  f ← mf; a ← ma; mret (f a).
#[global] Arguments monad_ap _ _ _ _ _ _ !_ / : simpl nomatch, assert.

(** Analogue of [inj_iff]. *)
Lemma inj2_iff {A B C} {R1 : relation A} {R2 : relation B} (S : relation C) (f : A → B → C)
  `{Hinj : !Inj2 R1 R2 S f} `{!Proper (R1 ==> R2 ==> S) f} x1 x2 y1 y2 :
  S (f x1 y1) (f x2 y2) ↔ R1 x1 x2 ∧ R2 y1 y2.
Proof. split. apply Hinj. firstorder. Qed.

#[global] Instance inj2_inj `{H : Inj2 A B C eq eq eq f} `{Inhabited B} : Inj eq eq f.
Proof.
  intros x y E. apply (inj2 f (Inj2 := H) x inhabitant y inhabitant).
  by rewrite E.
Qed.

(** ** Comparisons *)

Section compare.
  #[local] Set Typeclasses Unique Instances.

  (** A version of Coq's <<OrderedTypeAlt>>. *)
  Class Comparison {A} (f : A -> A -> comparison) : Prop := {
    compare_antisym (x y : A) : f x y = CompOpp (f y x);
    compare_trans (x y z : A) c : f x y = c -> f y z = c -> f x z = c;
  }.
  #[global] Hint Mode Comparison + - : typeclass_instances.
  #[global] Hint Mode Comparison - + : typeclass_instances.
  #[global] Hint Opaque compare_antisym compare_trans : typeclass_instances.

  Class Compare A := compare : A -> A -> comparison.
  #[global] Hint Mode Compare ! : typeclass_instances.
  #[global] Instance: Params (@compare) 2 := {}.
  #[global] Hint Opaque compare : typeclass_instances.
  #[global] Arguments compare : simpl never.
End compare.

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
      - intros x. generalize (compare_antisym x x). by destruct (compare x x).
      - intros x y. rewrite compare_antisym. by destruct (compare y x).
      - intros x y z. apply compare_trans.
    Qed.

    #[global] Instance lt_trans `{!Comparison (?=)} : Transitive lt.
    Proof. intros x y z. apply compare_trans. Qed.

    Lemma compare `{!Comparison (?=)} x y : OrderedType.Compare lt eq x y.
    Proof.
      rewrite /lt/eq. destruct (x ?= y) eqn:Hc; try by constructor.
      apply OrderedType.GT. by rewrite compare_antisym Hc.
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
