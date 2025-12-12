(*
 * Copyright (c) 2020-2021 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(**
Import this module to make uPred mostly non-affine, while still assuming [▷ emp
⊣⊢ emp] and other principles that do not cause leaks.

All changes to [typeclass_instances] will not propagate to your clients:
technically, they have [#[export]] visibility.
*)

Require Import bluerock.prelude.base.
Require Import bluerock.iris.extra.bi.prelude.
Require Import bluerock.iris.extra.bi.only_provable.
Require Import iris.bi.monpred.
Require Import bluerock.iris.extra.proofmode.proofmode.
Require Import iris.bi.lib.laterable.

(* Disable [BiAffine uPred] *)
#[export] Remove Hints uPred_affine : typeclass_instances.

(*
As a small optimization, we can remove dependent instances.
This causes further incompleteness if other affine logics are relevant.
*)
#[export] Remove Hints monPred_bi_affine : typeclass_instances.
#[export] Remove Hints absorbing_bi : typeclass_instances.
#[export] Remove Hints persistent_laterable : typeclass_instances.

(* Potentially useful to exploit [siProp_affine]. *)
Module enable_absorbing_bi.
  #[export] Hint Resolve absorbing_bi : typeclass_instances.
End enable_absorbing_bi.

Import bi.

Section with_later_emp.
  Context {PROP : bi} (Hlater_emp : ▷ emp ⊣⊢@{PROP} emp).
  Local Set Default Proof Using "Hlater_emp".
  Local Notation "'emp'" := (bi_emp (PROP := PROP)) : bi_scope.

  (**
  Very explicit proofs of some desirable principles, for any [bi]
  supporting [Hlater_emp].

  All lemmas use suffix [_with_later_emp].
  *)

  #[local] Lemma timeless_emp_with_later_emp : Timeless emp.
  Proof. by rewrite /Timeless -except_0_intro Hlater_emp. Qed.

  #[local] Instance affine_later_emp_with_later_emp : Affine (▷ emp).
  Proof. by rewrite /Affine Hlater_emp. Qed.

  #[local] Lemma affine_later_with_later_emp {P : PROP} `{!Affine P} :
    Affine (▷ P).
  Proof. intros. by rewrite /Affine (affine P) (affine (▷ emp)). Qed.

  #[local] Lemma persistent_affine_laterable (P : PROP) :
    Persistent P → Affine P → Laterable P.
  Proof. intros. apply /intuitionistic_laterable /timeless_emp_with_later_emp. Qed.
End with_later_emp.

(* Here, we assume [affinely_sep] as reasonable,
and derive desirable consequences, such as BiPositive. *)
Section with_affinely_sep.
  Context {PROP : bi} (Haffinely_sep : ∀ P Q : PROP, <affine> (P ∗ Q) ⊣⊢ <affine> P ∗ <affine> Q).
  Local Set Default Proof Using "Haffinely_sep".

  (* Iris proves [affinely_sep] from [BiPositive PROP]; we prove the converse holds *)
  (* [BiPositive PROP] is equivalent to [affinely_sep], which in turn seems
  perfectly natural. *)
  #[local] Instance bi_positive_with_affinely_sep : BiPositive PROP.
  Proof. intros P Q. by rewrite (Haffinely_sep P Q) (affinely_elim Q). Qed.
End with_affinely_sep.

(**
Specialize the lemmas in [Section with_later_emp] to [uPred] (hence
[iProp] and for now [mpred]).

All lemmas use suffix [_uPred].
*)

Section uPred_with_later_emp.
  Context (M : ucmra).
  Implicit Type (P : uPredI M).

  Definition later_emp_uPred := @bi.later_emp _ (uPred_affine M).

  #[export] Instance timeless_emp_uPred : Timeless (PROP := uPredI M) emp.
  Proof. apply timeless_emp_with_later_emp, later_emp_uPred. Qed.

  #[export] Instance affine_later_emp_uPred : Affine (PROP := uPredI M) (▷ emp).
  Proof. apply affine_later_emp_with_later_emp, later_emp_uPred. Qed.

  #[export] Instance affine_later_uPred P :
    Affine P → Affine (▷ P).
  Proof. apply affine_later_with_later_emp, later_emp_uPred. Qed.

  #[export] Instance persistent_affine_laterable_upred P :
    Persistent P → Affine P → Laterable P.
  Proof. apply persistent_affine_laterable, later_emp_uPred. Qed.
End uPred_with_later_emp.

(** *** Other instances that we derive from affinity but seem safe. *)
Section uPred.
  Context (M : ucmra).
  Definition affinely_sep_uPred := @affinely_sep _ (@bi_affine_positive _ (uPred_affine M)).

  #[export] Instance bi_positive_uPred : BiPositive (uPredI M).
  Proof. apply bi_positive_with_affinely_sep, affinely_sep_uPred. Qed.

  (*
  This instance is needed by some [only_provable] lemmas. It proves that
  [ (∀ x : A, [| φ x |]) ⊢@{PROP} <affine> (∀ x : A, [| φ x |]) ]
  so it seems related to [affinely_sep].
  *)
  #[export] Instance bi_emp_forall_only_provable_uPred (M : ucmra) : BiEmpForallOnlyProvable (uPredI M) :=
    bi_affine_emp_forall_only_provable (uPred_affine M).
End uPred.

(** *** Lift over [monPred] instances declared above. *)
Section monPred_lift.
  Context (PROP : bi).
  Context (I : biIndex).
  Local Notation monPredI := (monPredI I PROP).
  Implicit Type (P : monPredI).

  #[export] Instance timeless_emp_monPred_lift (HT : Timeless (PROP := PROP) emp) :
    Timeless (PROP := monPredI) emp.
  Proof. constructor=> i. rewrite monPred_at_later monPred_at_except_0 monPred_at_emp. exact HT. Qed.

  #[export] Instance affine_later_emp_monPred_lift (HA : Affine (PROP := PROP) (▷ emp)) :
    Affine (PROP := monPredI) (▷ emp).
  Proof. constructor=> i. rewrite monPred_at_later monPred_at_emp. exact HA. Qed.

  #[export] Instance affine_later_monPred_lift P
    (HA : ∀ P : PROP, Affine P → Affine (▷ P)) :
    Affine P → Affine (▷ P).
  Proof.
    intros AP. constructor=> i. rewrite monPred_at_later monPred_at_emp.
    apply HA, monPred_at_affine, AP.
  Qed.

  #[export] Instance persistent_affine_laterable_monPred_lift P
    (HT : Timeless (PROP := PROP) emp) :
    Persistent P → Affine P → Laterable P.
  Proof. intros. apply: intuitionistic_laterable. Qed.
  (** Liftings for [BiPositive] and [BiEmpForallOnlyProvable] are declared elsewhere. *)
End monPred_lift.

#[export] Remove Hints class_instances.from_forall_intuitionistically : typeclass_instances.

Section UPSTREAM_PROP.
  Context {PROP : bi}.
  (* To upstream to Iris. *)
  #[export] Instance from_forall_intuitionistically {A} `{!BiPersistentlyForall PROP}
      P (Φ : A → PROP) name :
    (* Compute [A] before searching for [Inhabited A]: *)
    FromForall P Φ name →
    TCOrT (BiAffine PROP) (Inhabited A) ->
    FromForall (□ P) (λ a, □ (Φ a))%I name.
  Proof.
    Import bi.
    rewrite /FromForall => /[swap] HT <-.
    destruct HT.
    - setoid_rewrite intuitionistically_into_persistently.
      by rewrite persistently_forall.
    - rewrite {2} /bi_intuitionistically /bi_affinely.
      apply and_intro; first exact: affine.
      setoid_rewrite intuitionistically_into_persistently_1 at 1.
      by rewrite persistently_forall.
  Qed.
End UPSTREAM_PROP.
