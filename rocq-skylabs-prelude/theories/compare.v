(*
 * Copyright (C) 2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import elpi.apps.NES.NES.
Require Export skylabs.prelude.base.
Require Import skylabs.prelude.numbers.
Require Import skylabs.prelude.list.
Require Import skylabs.prelude.pstring.
Require skylabs.prelude.uint63.

#[local] Set Default Proof Using "Type*".

(** Every relation is antisymmetric relative to itself.
Not an instance because this is a degenerate case.
 *)
Lemma anti_symm_refl {A} (R : relation A) : AntiSymm R R.
Proof. by intros x y. Qed.

Lemma comparison_refl `{!Comparison (A := A) cmp} {a : A} : cmp a a = Eq.
Proof. pose proof (compare_antisym (f:=cmp) a a). by destruct (cmp a a). Qed.

(** Laws for arbitrary comparison functions, including comparisons whose
[Eq] result identifies an equivalence class rather than Leibniz equality. *)
Section comparison_laws.
  Context {A : Type} (cmp : A -> A -> comparison) `{Hcmp : !Comparison cmp}.
  Lemma comparison_eq_left x y z : cmp x y = Eq -> cmp x z = cmp y z.
  Proof.
    intros Hxy.
    have Hyx : cmp y x = Eq by rewrite (compare_antisym (f:=cmp)) Hxy.
    have Hzy := @compare_antisym A cmp Hcmp z y.
    have Txz := @compare_trans A cmp Hcmp x y z.
    have Tyz := @compare_trans A cmp Hcmp y x z.
    have Txy := @compare_trans A cmp Hcmp x z y.
    destruct (cmp x z) eqn:Hxz, (cmp y z) eqn:Hyz; simpl in *;
      try reflexivity.
    all: exfalso; first
      [ specialize (Tyz Eq Hyx eq_refl); discriminate
      | specialize (Txz Eq Hxy eq_refl); discriminate
      | specialize (Txy Lt eq_refl Hzy); congruence
      | specialize (Txy Gt eq_refl Hzy); congruence ].
  Qed.
  Lemma comparison_eq_right x y z : cmp x y = Eq -> cmp z x = cmp z y.
  Proof.
    intros Hxy. rewrite (compare_antisym (f:=cmp) z x) (compare_antisym (f:=cmp) z y).
    by rewrite (comparison_eq_left x y z Hxy).
  Qed.

  Lemma compare_eq_trans {x y z c} :
    cmp x y = c -> cmp y z = Eq -> cmp x z = c.
  Proof. intros Hxy Hyz. by rewrite <- (comparison_eq_right y z x Hyz). Qed.

  Lemma eq_compare_trans {x y z c} :
    cmp x y = Eq -> cmp y z = c -> cmp x z = c.
  Proof. intros Hxy. by rewrite (comparison_eq_left x y z Hxy). Qed.
End comparison_laws.

#[global] Arguments compare_eq_trans {_ cmp _ x y z c}.
#[global] Arguments eq_compare_trans {_ cmp _ x y z c}.

(** Comparison laws depend only on the pointwise results of a comparator. *)
Lemma comparison_ext {A : Type} (cmp cmp' : A -> A -> comparison)
    `{!Comparison cmp} (Hcmp : forall x y, cmp x y = cmp' x y) : Comparison cmp'.
Proof.
  constructor.
  - intros x y. rewrite <- !Hcmp. apply compare_antisym.
  - intros x y z c Hxy Hyz. rewrite <- Hcmp in *. eapply compare_trans; eassumption.
Qed.

Lemma leibniz_comparison_ext {A : Type} (cmp cmp' : A -> A -> comparison)
    `{!LeibnizComparison cmp} (Hcmp : forall x y, cmp x y = cmp' x y) :
  LeibnizComparison cmp'.
Proof. intros x y Hxy. apply (LeibnizComparison.cmp_eq cmp). by rewrite Hcmp. Qed.

(** A comparator inherits the comparison laws from finite approximations when
    each pair eventually has a stable result. No uniform convergence bound or
    equality reflection is required. *)
Lemma comparison_of_approximations {A : Type} (cmp : A -> A -> comparison)
    (approx : nat -> A -> A -> comparison)
    (Happrox : forall n, Comparison (approx n))
    (Hagrees : forall x y, exists bound, forall n,
      (bound <= n)%nat -> approx n x y = cmp x y) : Comparison cmp.
Proof.
  constructor.
  - intros x y. destruct (Hagrees x y) as [n Hxy], (Hagrees y x) as [m Hyx].
    rewrite <- (Hxy (n + m)%nat ltac:(lia)), <- (Hyx (n + m)%nat ltac:(lia)).
    exact (@compare_antisym _ _ (Happrox (n + m)%nat) x y).
  - intros x y z c Hxy Hyz.
    destruct (Hagrees x y) as [n Hn], (Hagrees y z) as [m Hm],
      (Hagrees x z) as [p Hp].
    rewrite <- (Hn (n + m + p)%nat ltac:(lia)) in Hxy.
    rewrite <- (Hm (n + m + p)%nat ltac:(lia)) in Hyz.
    rewrite <- (Hp (n + m + p)%nat ltac:(lia)).
    exact (@compare_trans _ _ (Happrox (n + m + p)%nat) x y z c Hxy Hyz).
Qed.

(** Pulling a comparison back along a function needs no injectivity. *)
Lemma comparison_pullback {A B : Type} (f : A -> B) (cmp : B -> B -> comparison)
    `{!Comparison cmp} : Comparison (fun x y => cmp (f x) (f y)).
Proof. constructor; intros; [apply compare_antisym | eapply compare_trans; eassumption]. Qed.

(** Injectivity is needed only when pulling back Leibniz equality. *)
Lemma leibniz_comparison_pullback {A B : Type} (f : A -> B)
    (cmp : B -> B -> comparison) `{!Inj (=) (=) f, !LeibnizComparison cmp} :
  LeibnizComparison (fun x y => cmp (f x) (f y)).
Proof. intros x y Hxy. apply (inj f), (LeibnizComparison.cmp_eq cmp), Hxy. Qed.

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
    (* The cast requires the transparent proof, independently of import order. *)
    match c as c' return c = c' -> comparison with
    | Eq => fun EQ => compare t (d ()) $ rew (numbers.Pos.compare_eq _ _ EQ) in data a
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

Lemma compare_lex_eq (a : comparison) (b : unit -> comparison) :
  compare_lex a b = Eq <-> a = Eq /\ b () = Eq.
Proof. destruct a; cbn; intuition congruence. Qed.

Lemma compare_lex_inv c0 c1 c2 :
  compare_lex c0 c1 = c2 <->
  if bool_decide (c2 = Eq)
  then c0 = Eq /\ c1 () = Eq
  else c0 = c2 \/ (c0 = Eq /\ c1 () = c2).
Proof. case: bool_decide_reflect c0 => Heq [] /=; by intuition; subst. Qed.

Lemma compare_lex_antisym a b :
  compare_lex (CompOpp a) (fun _ => CompOpp (b ())) = CompOpp (compare_lex a b).
Proof. by destruct a. Qed.

(** Transitivity with arbitrary tails.  In recursive comparisons, the tail
premise can be an induction hypothesis rather than a global instance. *)
Lemma compare_lex_trans {A : Type} (cmp : A -> A -> comparison)
    `{Hcmp : !Comparison cmp} (x y z : A) (bxy byz bxz : unit -> comparison) c :
  (bxy () = c -> byz () = c -> bxz () = c) ->
  compare_lex (cmp x y) bxy = c ->
  compare_lex (cmp y z) byz = c ->
  compare_lex (cmp x z) bxz = c.
Proof.
  intros Htail Hxy Hyz.
  destruct (cmp x y) eqn:E1, (cmp y z) eqn:E2; cbn [compare_lex] in Hxy, Hyz; try congruence.
  all: try (rewrite (@compare_trans _ cmp Hcmp x y z _ E1 E2); cbn [compare_lex];
    first [exact Hxy | exact Hyz | by apply Htail]).
  all: try (rewrite (comparison_eq_left cmp x y z E1) E2; cbn [compare_lex]; congruence).
  all: try (rewrite <- (comparison_eq_right cmp y z x E2), E1; cbn [compare_lex]; congruence).
Qed.

(** Convenient pointwise composition of already available comparators.
[g x y] is delayed; an expression constructing [g] itself is a strict argument.
Use [compare_lex] to delay comparator construction as well. *)
Definition lex_compare {A : Type} (f g : A -> A -> comparison) (x y : A) : comparison :=
  compare_lex (f x y) (fun _ => g x y).

Lemma lex_compare_comparison {A : Type} (f g : A -> A -> comparison)
    `{Hf : !Comparison f, Hg : !Comparison g} : Comparison (lex_compare f g).
Proof.
  constructor.
  - intros x y. rewrite /lex_compare (compare_antisym x y (Comparison:=Hf))
      (compare_antisym x y (Comparison:=Hg)).
    apply (compare_lex_antisym (f y x) (fun _ => g y x)).
  - intros x y z c Hxy Hyz.
    eapply (compare_lex_trans f (Hcmp:=Hf) x y z
      (fun _ => g x y) (fun _ => g y z) (fun _ => g x z) c);
      [apply (@compare_trans _ g Hg) | exact Hxy | exact Hyz].
Qed.

Module compare.
  Section derived.
    Context `{!Compare A}.
    #[local] Infix "?=" := (@compare A _).
    #[local] Notation "(?=)" := (@compare A _) (only parsing).

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

    Lemma compare_spec x y : CompareSpec (eq x y) (lt x y) (gt x y) (x ?= y).
    Proof. rewrite /eq /lt /gt. by destruct (x ?= y); constructor. Qed.

    Section laws.
      Context `{!Comparison (?=)}.

      #[global] Instance eq_equiv : Equivalence eq.
      Proof.
        rewrite /eq. split.
        - intros x. apply comparison_refl.
        - intros x y. by rewrite (compare_antisym (f:=(?=)) y x) => ->.
        - intros x y z. apply compare_trans.
      Qed.

      #[global] Instance compare_proper : Proper (eq ==> eq ==> (=)) (?=).
      Proof.
        intros x y Hxy z w Hzw.
        rewrite (comparison_eq_left (?=) x y z Hxy).
        by rewrite (comparison_eq_right (?=) z w y Hzw).
      Qed.

      #[global] Instance eq_proper : Proper (eq ==> eq ==> iff) eq.
      Proof. intros x y Hxy z w Hzw. rewrite /eq Hxy Hzw. done. Qed.
      #[global] Instance lt_proper : Proper (eq ==> eq ==> iff) lt.
      Proof. intros x y Hxy z w Hzw. rewrite /lt Hxy Hzw. done. Qed.
      #[global] Instance le_proper : Proper (eq ==> eq ==> iff) le.
      Proof. intros x y Hxy z w Hzw. rewrite /le Hxy Hzw. done. Qed.
      #[global] Instance gt_proper : Proper (eq ==> eq ==> iff) gt.
      Proof. intros x y Hxy z w Hzw. rewrite /gt Hxy Hzw. done. Qed.
      #[global] Instance ge_proper : Proper (eq ==> eq ==> iff) ge.
      Proof. intros x y Hxy z w Hzw. rewrite /ge Hxy Hzw. done. Qed.

      Lemma gt_lt x y : gt x y <-> lt y x.
      Proof. rewrite /gt /lt (compare_antisym (f:=(?=))). by destruct (y ?= x). Qed.
      Lemma ge_le x y : ge x y <-> le y x.
      Proof. rewrite /ge /le (compare_antisym (f:=(?=))). by destruct (y ?= x). Qed.

      #[local] Instance le_refl : Reflexive le.
      Proof. intros x. by rewrite /le comparison_refl. Qed.
      #[local] Instance ge_refl : Reflexive ge.
      Proof. intros x. apply ge_le, le_refl. Qed.

      #[local] Instance lt_trans : Transitive lt.
      Proof. intros x y z. apply compare_trans. Qed.
      #[local] Instance gt_trans : Transitive gt.
      Proof. intros x y z. rewrite !gt_lt. intros; by etransitivity. Qed.

      #[local] Instance lt_irrefl : Irreflexive lt.
      Proof.
        intros x Hxx. change (x ?= x = Lt) in Hxx.
        have Hrefl : x ?= x = Eq := comparison_refl.
        rewrite Hrefl in Hxx. discriminate.
      Qed.
      #[local] Instance gt_irrefl : Irreflexive gt.
      Proof.
        intros x Hxx. change (x ?= x = Gt) in Hxx.
        have Hrefl : x ?= x = Eq := comparison_refl.
        rewrite Hrefl in Hxx. discriminate.
      Qed.
      #[global] Instance lt_strict_order : StrictOrder lt.
      Proof. split; apply _. Qed.
      #[global] Instance gt_strict_order : StrictOrder gt.
      Proof. split; apply _. Qed.

      (** Opposing strict comparisons are contradictory, even without Leibniz equality. *)
      #[global] Instance lt_anti_symm : AntiSymm (=) lt.
      Proof.
        intros x y Hxy Hyx. rewrite /lt (compare_antisym (f:=(?=)) y x) Hxy /= in Hyx.
        discriminate.
      Qed.
      #[global] Instance gt_anti_symm : AntiSymm (=) gt.
      Proof. intros x y Hxy Hyx. symmetry. apply (lt_anti_symm y x); by apply gt_lt. Qed.

      #[local] Instance le_trans : Transitive le.
      Proof.
        intros x y z. rewrite /le.
        destruct (x ?= y) eqn:Hxy; [rewrite (comparison_eq_left (?=) x y z Hxy) | | done].
        { done. }
        destruct (y ?= z) eqn:Hyz.
        - by rewrite <- (comparison_eq_right (?=) y z x Hyz), Hxy.
        - by rewrite (compare_trans x y z Lt Hxy Hyz).
        - done.
      Qed.
      #[local] Instance ge_trans : Transitive ge.
      Proof. intros x y z. rewrite !ge_le. intros; by etransitivity. Qed.
      #[global] Instance le_preorder : PreOrder le.
      Proof. split; apply _. Qed.
      #[global] Instance ge_preorder : PreOrder ge.
      Proof. split; apply _. Qed.

      Lemma ordered_type_compare x y : OrderedType.Compare lt eq x y.
      Proof.
        rewrite /lt /eq. destruct (x ?= y) eqn:Hc; try by constructor.
        apply OrderedType.GT. by rewrite (compare_antisym (f:=(?=))) Hc.
      Qed.

      (** These versions also apply to comparisons identifying only equivalence classes. *)
      #[global] Instance lt_anti_symm_compare_eq : AntiSymm eq lt.
      Proof. intros x y. rewrite /lt /eq (compare_antisym (f:=(?=)) y x). by destruct (x ?= y). Qed.
      #[global] Instance le_anti_symm_compare_eq : AntiSymm eq le.
      Proof. intros x y. rewrite /le /eq (compare_antisym (f:=(?=)) y x). by destruct (x ?= y). Qed.
      #[global] Instance gt_anti_symm_compare_eq : AntiSymm eq gt.
      Proof. intros x y Hxy Hyx. symmetry. apply (lt_anti_symm_compare_eq y x); by apply gt_lt. Qed.
      #[global] Instance ge_anti_symm_compare_eq : AntiSymm eq ge.
      Proof. intros x y Hxy Hyx. symmetry. apply (le_anti_symm_compare_eq y x); by apply ge_le. Qed.

      #[global] Instance le_total : Total le.
      Proof.
        intros x y. rewrite /le (compare_antisym (f:=(?=)) y x).
        destruct (x ?= y); cbn; auto.
      Qed.
      #[global] Instance ge_total : Total ge.
      Proof. intros x y. rewrite !ge_le. apply le_total. Qed.

      Section leibniz.
        Context `{!LeibnizComparison (?=)}.

        Lemma eq_eq x y : eq x y <-> x = y.
        Proof.
          split; [intros Hxy; exact (LeibnizComparison.cmp_eq (?=) x y Hxy)
            | intros ->; apply comparison_refl].
        Qed.

        #[local] Instance le_anti_symm : AntiSymm (=) le.
        Proof. intros x y Hxy Hyx. apply eq_eq. by apply le_anti_symm_compare_eq. Qed.
        #[local] Instance ge_anti_symm : AntiSymm (=) ge.
        Proof. intros x y Hxy Hyx. symmetry. apply (le_anti_symm y x); by apply ge_le. Qed.
        #[global] Instance le_partial_order : PartialOrder le.
        Proof. split; apply _. Qed.
        #[global] Instance ge_partial_order : PartialOrder ge.
        Proof. split; apply _. Qed.
        #[global] Instance lt_trichotomy : Trichotomy lt.
        Proof.
          intros x y. destruct (x ?= y) eqn:Hxy.
          - right; left. by apply eq_eq.
          - by left.
          - right; right. apply gt_lt. exact Hxy.
        Qed.
      End leibniz.
    End laws.
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

Section comparison.
  Context {A} `{!Compare A}.

  Definition compare_on {B} (f : B -> A) : Compare B :=
    fun x y => base.compare (f x) (f y).

End comparison.

#[global] Instance compare_on_comparison {A B : Type} `{!Compare A}
    (f : B -> A) `{!Comparison (compare (A:=A))} :
    Comparison (@compare B (compare_on f)).
Proof. exact (comparison_pullback f (compare (A:=A))). Qed.

#[global] Instance compare_on_leibniz_comparison {A B : Type} `{!Compare A}
    (f : B -> A) `{!Inj (=) (=) f, !LeibnizComparison (compare (A:=A))} :
    LeibnizComparison (@compare B (compare_on f)).
Proof. exact (leibniz_comparison_pullback f (compare (A:=A))). Qed.

#[global] Hint Opaque compare_on : typeclass_instances.

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
  Context {A} {cmpA : A -> A -> comparison} `{HcmpA : !Comparison cmpA} `{HlcmpA : !LeibnizComparison cmpA}.
  Context {B} {cmpB : B -> B -> comparison} `{HcmpB : !Comparison cmpB} `{HlcmpB : !LeibnizComparison cmpB}.

  Definition lex_comparison : A * B -> A * B -> comparison :=
    fun '(a0,b0) '(a1,b1) => compare.compare_lex (cmpA a0 a1) (fun _ => cmpB b0 b1).

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
    LeibnizComparison (T := A * B) lex_comparison.
  Proof using HlcmpA HlcmpB.
    case => [a0 b0] [a1 b1] /=.
    by move => /compare_lex_inv/= []
         => /(LeibnizComparison.cmp_eq _ _ _) <-
         => /(LeibnizComparison.cmp_eq _ _ _) <-.
  Qed.

End compare_lex.

(** Comparison laws extracted from SkyLabsAI/BRiCk#337. *)
Module List.
  Section compare.
    Context {A : Type}.
    Context (compareA : A -> A -> comparison).

    (* for types with a small number of constructors the direct comparison function is faster *)
    Fixpoint compare (l l' : list A) : comparison :=
      match l , l' with
      | nil , nil => Eq
      | nil , _ :: _ => Lt
      | _ :: _ , nil => Gt
      | x :: xs , y :: ys => compare_lex (compareA x y) (fun _ => compare xs ys)
      end.

  End compare.
End List.
#[global] Instance list_compare `{!Compare A} : Compare (list A) := List.compare compare.

Section comparison_laws.
  #[local] Set Default Proof Using "Type*".
  Lemma list_comparison {A} (cmp : A -> A -> comparison) `{Hcmp : !Comparison cmp} :
    Comparison (List.compare cmp).
  Proof.
    constructor.
    - intros xs. induction xs as [|x xs IH]; intros [|y ys]; try done.
      cbn [List.compare]. rewrite (compare_antisym x y) (IH ys).
      by destruct (cmp y x).
    - fix IH 1. intros xs ys zs c Hxy Hyz.
      destruct xs as [|x xs], ys as [|y ys], zs as [|z zs];
        cbn [List.compare] in *; try congruence.
      destruct (cmp x y) eqn:E1, (cmp y z) eqn:E2; simpl in Hxy, Hyz; try congruence.
      all: try (rewrite (@compare_trans _ cmp Hcmp x y z _ E1 E2); cbn;
        first [exact Hxy | exact Hyz | eapply IH; eassumption]).
      all: try (rewrite (comparison_eq_left cmp x y z E1) E2; cbn; congruence).
      all: try (rewrite <- (comparison_eq_right cmp y z x E2), E1; cbn; congruence).
  Qed.

  #[global] Instance string_comparison : Comparison PrimString.compare.
  Proof. constructor; intros; [apply PString.compare_antisym | eapply PString.compare_trans; eassumption]. Qed.
End comparison_laws.

Lemma list_compare_eq {A} (cmp : A -> A -> comparison)
    (Hcmp : forall x y, cmp x y = Eq -> x = y) (xs ys : list A) :
  List.compare cmp xs ys = Eq -> xs = ys.
Proof.
  revert ys. induction xs as [|x xs IH]; intros [|y ys] H; try done.
  simpl in H. unfold compare_lex in H.
  destruct (cmp x y) eqn:E; try discriminate.
  f_equal; [by apply Hcmp | by apply IH].
Qed.

#[global] Instance primitive_integer_comparison : Comparison PrimInt63.compare.
Proof. constructor; intros; [apply PString.char63_compare_antisym | eapply PString.char63_compare_trans; eassumption]. Qed.
