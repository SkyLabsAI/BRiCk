(*
 * Copyright (c) 2020-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
(*
 * The following code contains code derived from code original to the
 * stdpp project. That original code is
 *
 *	Copyright stdpp developers and contributors
 *
 * and used according to the following license.
 *
 *	SPDX-License-Identifier: BSD-3-Clause
 *
 * Original stdpp License:
 * https://gitlab.mpi-sws.org/iris/stdpp/-/blob/5415ad3003fd4b587a2189ddc2cc29c1bd9a9999/LICENSE
 *)

Require Import elpi.apps.locker.locker.
Require Import bluerock.prelude.base.
Require Import bluerock.prelude.bool.

Module option.
  Definition existsb {A} (f : A -> bool) (m : option A) : bool :=
    if m is Some x then f x else false.

  (**
  Haskell's [Data.Function.on]
  (https://hackage.haskell.org/package/base-4.17.0.0/docs/Data-Function.html#v:on).

  Examples:
  - Lift relation [R] by precomposing with function [f] (with [C := Prop].
  We provide theory specialized to this use-case.
  *)
  Definition on {A B C} (R : B -> B -> C) (f : A -> B) (x y : A) : C :=
    R (f x) (f y).
End option.

(** Boolean version of stdpp's [is_Some] *)
Definition isSome {A} (m : option A) : bool :=
  if m is Some _ then true else false.

Lemma isSomeP {A} {m : option A} : reflect (is_Some m) (isSome m).
Proof. destruct m; cbn; constructor. by eexists. exact: is_Some_None. Qed.

(** * Theory for [is_Some_proj]

[@stdpp.option.is_Some_proj A mx P] extracts the element of type [A]
from [mx] knowing that [mx] is not a [None].

The theory for [is_Some_proj] is simply [is_Some_proj_eq], which can
be used in combination with [Some_inj] to switch between [A] and [option A].
*)
Lemma is_Some_proj_eq {A : Type} {mx : option A} (P : is_Some mx) :
  mx = Some (is_Some_proj P).
Proof. rewrite /is_Some_proj. case_match; [done|by destruct P]. Qed.

(** Preorder properties lift through [on].
Only import locally when declaring specialized instances!
These instances can lead to divergence of setoid rewriting, so they're only
available when importing [on_props]. *)
Module on_props.
Section on_props.
  Import option.

  Context {A B : Type} {f : A -> B}.
  (* We use both [R] and [strict R] *)
  Implicit Type (R : relation B).

  (* We can safely make this global. *)
  #[global] Instance on_decidable `{!RelDecision R} : RelDecision (on R f).
  Proof. GUARD_TC. rewrite /on => ??. apply _. Defined.

  (** * Lift basic relation typeclasses from [RelationClasses] *)
  #[export] Instance on_reflexive `{!Reflexive R} : Reflexive (on R f).
  Proof. GUARD_TC. rewrite /on. by intros ?. Qed.
  #[export] Instance on_irreflexive `{!Irreflexive R} : Irreflexive (on R f).
  Proof. GUARD_TC. rewrite /on. by intros ??%irreflexivity. Qed.

  #[export] Instance on_symmetric `{!Symmetric R} : Symmetric (on R f).
  Proof. GUARD_TC. rewrite /on. by intros ?. Qed.
  #[export] Instance on_asymmetric `{!Asymmetric R} : Asymmetric (on R f).
  Proof. GUARD_TC. rewrite /on. intros ??. apply: asymmetry. Qed.

  #[export] Instance on_transitive `{!Transitive R} : Transitive (on R f).
  Proof. GUARD_TC. rewrite /on. by intros ???; etrans. Qed.

  (** * Lift bundled relation typeclasses from [RelationClasses] *)
  #[export] Instance on_equivalence `{!Equivalence R} : Equivalence (on R f).
  Proof. GUARD_TC. split; apply _. Qed.
  #[export] Instance on_preorder `{!PreOrder R} : PreOrder (on R f).
  Proof. GUARD_TC. split; apply _. Qed.
  #[export] Instance on_per `{!RelationClasses.PER R} : RelationClasses.PER (on R f).
  Proof. GUARD_TC. split; apply _. Qed.
  #[export] Instance on_strict_order `{!StrictOrder R} : StrictOrder (on R f).
  Proof. GUARD_TC. split; apply _. Qed.

  (** * Lift basic relation typeclasses from [stdpp.base] *)
  #[export] Instance on_antisymm
      (S : relation B) `{!AntiSymm S R} :
    AntiSymm (on S f) (on R f) | 100.
  Proof. GUARD_TC. rewrite /on. intros ??. apply: anti_symm. Qed.

  (** Needed to lift [PartialOrder] *)
  #[export] Instance on_antisymm_eq_inj
      `{!AntiSymm (=) R} `{!Inj eq eq f} :
    AntiSymm (=) (on R f).
  Proof. GUARD_TC. rewrite /on. intros ????. apply (inj f). exact: anti_symm. Qed.

  (** Needed to lift [TotalOrder] *)
  #[export] Instance on_trichotomy
      `{!Trichotomy R} `{!Inj eq eq f} :
    Trichotomy (on R f).
  Proof. GUARD_TC. rewrite /on. intros ??. rewrite -(inj_iff f). apply: trichotomy. Qed.

  #[export, refine] Instance on_trichotomyT
      `{!TrichotomyT R} `{!Inj eq eq f} :
    TrichotomyT (on R f) := fun x y =>
      match trichotomyT R (f x) (f y) with
      | inleft (left H) => inleft (left H)
      | inleft (right H) => inleft (right _)
      | inright H => inright H
      end.
  Proof. abstract (apply (inj f _ _ H)). Defined.

  (** * Lift bundled relation typeclasses from [stdpp.base] *)
  #[export] Instance on_partial_order `{!PartialOrder R} `{!Inj eq eq f} : PartialOrder (on R f).
  Proof. GUARD_TC. split; apply _. Qed.

  #[export] Instance on_total_order `{!TotalOrder R} `{!Inj eq eq f} : TotalOrder (on R f).
  Proof. GUARD_TC. split; rewrite -?[strict (on R f)]/(on (strict R) f); apply _. Qed.
End on_props.
End on_props.
#[global] Typeclasses Opaque option.on.

(**
TODO: Consider calling this <<option.Rleq>> or <<option.leq>>
*)
Variant Roption_leq {A} (R : relation A) : relation (option A) :=
| Rleq_None {x} : Roption_leq R None x
| Rleq_Some {x y} (_ : R x y) : Roption_leq R (Some x) (Some y).

Section Roption_leq.
  Context {A : Type}.
  Implicit Type (R : relation A) (ox oy : option A) (x y : A).

  #[local] Hint Constructors Roption_leq : core.

  Lemma Roption_leq_option_relation {R ox oy} :
    Roption_leq R ox oy <-> option_relation R (const False) (const True) ox oy.
  Proof. destruct ox, oy; simpl; split; try inversion 1; naive_solver. Qed.

  Lemma Roption_leq_Some_l_inv {R x oy} :
    Roption_leq R (Some x) oy <-> ∃ y, oy = Some y ∧ R x y.
  Proof. split; inversion 1; naive_solver. Qed.
  Lemma Roption_leq_None_inv {R oy} :
    Roption_leq R None oy <-> True.
  Proof. split; inversion 1; naive_solver. Qed.

  Lemma Roption_leq_inv_l_Some_eq {R ox oy} :
    Roption_leq R ox oy <-> forall x, ox = Some x -> exists y, oy = Some y /\ R x y.
  Proof. split. by inversion_clear 1; naive_solver. by destruct ox; naive_solver. Qed.

  Lemma Roption_leq_inv_l_Some {R ox oy} :
    Roption_leq R ox oy <->
    match ox with
    | None => True
    | Some x => exists y, oy = Some y /\ R x y
    end.
  Proof. rewrite Roption_leq_inv_l_Some_eq; destruct ox; naive_solver. Qed.

  Lemma Roption_leq_equiv R {ox oy} :
    Roption_leq R ox oy <->
    match ox, oy with
    | None, _ => True
    | Some x, None => False
    | Some x, Some y => R x y
    end.
  Proof. split. by inversion_clear 1. by destruct ox, oy; naive_solver. Qed.

  Lemma Roption_leq_eq_equiv {R ox oy} :
    Roption_leq eq ox oy <-> forall a, ox = Some a -> oy = Some a.
  Proof. rewrite Roption_leq_equiv; by destruct ox, oy; naive_solver. Qed.

End Roption_leq.

mlock Definition some_Forall2 {A} (R : relation A) (oa1 oa2 : option A) :=
  is_Some oa1 ∧ is_Some oa2 ∧ option_Forall2 R oa1 oa2.
#[global] Arguments some_Forall2 {A} _ _ _ : assert.
(* ^^ Necessary to workaround [mlock] bugs. *)

Section some_Forall2.
  Context `{R : relation A}.

  (* #[global] Instance some_Forall2_reflexive `{!Reflexive R}: Reflexive (some_Forall2 R).
  Proof. rewrite some_Forall2.unlock. intros ?. Qed. *)
  #[global] Instance some_Forall2_symmetric `{!Symmetric R}: Symmetric (some_Forall2 R).
  Proof. GUARD_TC. rewrite some_Forall2.unlock. intros ?; naive_solver. Qed.
  #[global] Instance some_Forall2_transitive `{!Transitive R}: Transitive (some_Forall2 R).
  Proof. GUARD_TC. rewrite some_Forall2.unlock. intros ?; intuition idtac. by etrans. Qed.
  #[global] Instance some_Forall2_per `{!RelationClasses.PER R} : RelationClasses.PER (some_Forall2 R).
  Proof. GUARD_TC. split; apply _. Qed.

  Lemma some_Forall2_iff oa1 oa2 :
    some_Forall2 R oa1 oa2 ↔
    ∃ (a1 a2 : A), oa1 = Some a1 ∧ oa2 = Some a2 ∧ R a1 a2.
  Proof.
    rewrite some_Forall2.unlock; split.
    { destruct 1 as ([??] & [??] & Hop); inversion Hop; naive_solver. }
    destruct 1 as (? & ? & -> & -> & ?); split_and!; by econstructor.
  Qed.

  #[global, refine] Instance option_Forall2_decision
      `{EqDecision A} `{!RelDecision R} :
    RelDecision (option_Forall2 R) :=
    fun oa1 oa2 =>
      match oa1, oa2 with
      | None, None => left _
      | Some a1, Some a2 => cast_if (decide (R a1 a2))
      | _, _ => right _
      end.
  Proof.
    all: abstract (intros; by [inversion_clear 1 | constructor]).
  Defined.

  #[global, refine] Instance some_Forall2_decision `{EqDecision A} `{!RelDecision R} :
    RelDecision (some_Forall2 R) :=
    λ oa1 oa2, cast_if (decide (is_Some oa1 ∧ is_Some oa2 ∧ option_Forall2 R oa1 oa2)).
  Proof. all: abstract (by rewrite some_Forall2.unlock). Defined.
End some_Forall2.

Section some_Forall2_eq.
  Context {A : Type}.

  Lemma some_Forall2_eq_iff (oa1 oa2 : option A) :
    some_Forall2 eq oa1 oa2 ↔
    ∃ (a : A), oa1 = Some a ∧ oa2 = Some a.
  Proof. rewrite some_Forall2_iff; naive_solver. Qed.
End some_Forall2_eq.

(** ** Define a partial equivalence relation from an observation *)
Definition same_property `(obs : A → option B) :=
  option.on (some_Forall2 eq) obs.
Section same_property.
  Context `{obs : A → option B}.

  (* Lift [#[global]] and [#[export]] instances from [on_props] before making it
  opaque. *)
  #[global] Instance same_property_decision `{EqDecision B} :
    RelDecision (same_property obs) := _.

  Section with_on_props.
    Import on_props.
    #[global] Instance same_property_per : RelationClasses.PER (same_property obs) := _.
  End with_on_props.

  #[global] Typeclasses Opaque same_property.

  #[global] Instance: RewriteRelation (same_property obs) := {}.

  Lemma same_property_iff a1 a2 :
    same_property obs a1 a2 ↔
    ∃ (b : B), obs a1 = Some b ∧ obs a2 = Some b.
  Proof. by rewrite /same_property /option.on some_Forall2_eq_iff. Qed.

  Lemma same_property_intro a1 a2 b :
    obs a1 = Some b -> obs a2 = Some b -> same_property obs a1 a2.
  Proof. rewrite same_property_iff. eauto. Qed.

  Lemma same_property_reflexive_equiv a :
    is_Some (obs a) ↔ same_property obs a a.
  Proof. rewrite same_property_iff /is_Some. naive_solver. Qed.

  Lemma same_property_partial_reflexive a b :
    obs a = Some b → same_property obs a a.
  Proof. rewrite -same_property_reflexive_equiv. naive_solver. Qed.
End same_property.

Section add_opt.
  Definition add_opt (oz1 oz2 : option Z) : option Z := liftM2 Z.add oz1 oz2.
  #[global] Instance add_opt_inj a : Inj eq eq (add_opt (Some a)).
  Proof.
    rewrite /add_opt => -[b1|] [b2|] // [?]. f_equal. lia.
  Qed.
End add_opt.

Lemma option_list_nil {A} (x : option A) : option_list x = [] -> x = None.
Proof. case: x => //=. Qed.

(** *** Forcing

    The functions [force_some] and [get_some] ascribe a precise
    type to the function that extracts a value from an [option].
    Because of the complex types, these should only be used for
    convenience wrappers that are meant to be written by user terms.

    Example.
    Suppose that you have a complex data structure [T] that
    can be easily represented via a [string]. You might implement
    [parse : string -> option T], and then provide a convenience wrapper
    [mk : forall s : string, force_some (parse s)]. This allows users to
    write [mk "foo,bar,baz"] and they will get a type error if
    ["foo,bar,baz"] does not parse.
    This use case fits within the functionality of [String Notation]
    but this setup is a bit more general allowing parsing and checking
    invariants on other user-written data.
 *)

Definition force_some {T : Set} (o : option T) : Set :=
  match o with
  | Some _ => T
  | None => unit
  end.

Definition get_some {T : Set} (o : option T) : force_some o :=
  match o as o return force_some o with
  | Some t => t
  | None => tt
  end.

#[deprecated(since="20240317", note="Use [option.on].")]
Notation on := option.on.
