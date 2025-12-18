(*
 * Copyright (C) 2020-2023 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Export iris.algebra.lib.excl_auth.
Require Export skylabs.prelude.base.
Set Printing Coercions.

(** * Extension to [excl_auth] *)
(** Extend [iris.algebra.lib.excl_auth] with fractional authoritative
elements [excl_auth_frac] (notation [●E{q} a]) such that

- fraction [1] coincides with the existing [excl_auth_auth] (notation
  [●E a])

- the operation [⋅] on such elements is addition of fractions

- [●E{q} a] valid implies fraction [q] valid

- [●E{q1} a1 ⋅ ●E{q2} a2] valid implies [a1 ≡ a2]

- [●E{q} a ⋅ ◯E b] valid implies [a ≡ b]

This is entirely straightforward because the underlying authoritative
construction supports such fractions. *)

(** Fractional authoritative elements for [excl_auth]. *)
Definition excl_auth_frac {SI : sidx} {A : ofe} (q : Qp) (a : A) : excl_authR A :=
  ●{#q} (Excl' a).
#[global] Instance: Params (@excl_auth_frac) 1 := {}.
#[global] Hint Opaque excl_auth_frac : typeclass_instances.

Notation "●E{ q } a" := (excl_auth_frac q a) (at level 10, format "●E{ q }  a").

Section excl_auth_frac.
  Context {SI : sidx} {A : ofe}.
  Implicit Types a b : A.
  Import proofmode_classes.

  Lemma excl_auth_auth_frac a : ●E a = ●E{1} a.
  Proof. done. Qed.

  #[global] Instance excl_auth_frac_ne q : NonExpansive (@excl_auth_frac _ A q).
  Proof. solve_proper. Qed.
  #[global] Instance excl_auth_frac_proper q : Proper ((≡) ==> (≡)) (@excl_auth_frac _ A q).
  Proof. apply: ne_proper. Qed.

  #[global] Instance excl_auth_frac_discrete q a `{!Discrete a} : Discrete (●E{q} a).
  Proof. apply auth_auth_discrete. apply Some_discrete, _. apply _. Qed.

  Lemma excl_auth_frac_op p q a : ●E{p + q} a ≡ ●E{p} a ⋅ ●E{q} a.
  Proof. by rewrite -auth_auth_dfrac_op. Qed.

  #[global] Instance excl_auth_frac_is_op q q1 q2 a :
    IsOp q q1 q2 → IsOp' (●E{q} a) (●E{q1} a) (●E{q2} a).
  Proof. rewrite /excl_auth_frac. apply _. Qed.

  Lemma excl_auth_frac_validN n q a : ✓{n} (●E{q} a) ↔ (q ≤ 1)%Qp.
  Proof. rewrite /excl_auth_frac. by rewrite auth_auth_dfrac_validN right_id. Qed.
  Lemma excl_auth_frac_valid q a : ✓ (●E{q} a) ↔ (q ≤ 1)%Qp.
  Proof. rewrite /excl_auth_frac. by rewrite auth_auth_dfrac_valid right_id. Qed.

  Lemma excl_auth_auth_frac_op_validN n q1 q2 a1 a2 :
    ✓{n} (●E{q1} a1 ⋅ ●E{q2} a2) ↔ (q1 + q2 ≤ 1)%Qp ∧ a1 ≡{n}≡ a2.
  Proof.
    rewrite/excl_auth_frac.
    by rewrite auth_auth_dfrac_op_validN (inj_iff Some) (inj_iff Excl) right_id.
  Qed.
  Lemma excl_auth_auth_frac_op_valid q1 q2 a1 a2 :
    ✓ (●E{q1} a1 ⋅ ●E{q2} a2) ↔ (q1 + q2 ≤ 1)%Qp ∧ a1 ≡ a2.
  Proof.
    rewrite/excl_auth_frac.
    by rewrite auth_auth_dfrac_op_valid (inj_iff Some) (inj_iff Excl) right_id.
  Qed.
  Lemma excl_auth_auth_frac_op_valid_L `{!LeibnizEquiv A} q1 q2 a1 a2 :
    ✓ (●E{q1} a1 ⋅ ●E{q2} a2) ↔ (q1 + q2 ≤ 1)%Qp ∧ a1 = a2.
  Proof. unfold_leibniz. apply excl_auth_auth_frac_op_valid. Qed.

  Lemma excl_auth_frac_op_invN n p a q b : ✓{n} (●E{p} a ⋅ ●E{q} b) → a ≡{n}≡ b.
  Proof.
    rewrite /excl_auth_frac=>/auth_auth_dfrac_op_invN.
    by rewrite (inj_iff Some) (inj_iff Excl).
  Qed.
  Lemma excl_auth_frac_op_inv p a q b : ✓ (●E{p} a ⋅ ●E{q} b) → a ≡ b.
  Proof.
    rewrite/excl_auth_frac=>/auth_auth_dfrac_op_inv.
    by rewrite (inj_iff Some) (inj_iff Excl).
  Qed.
  Lemma excl_auth_frac_op_inv_L `{!LeibnizEquiv A} p a q b :
    ✓ (●E{p} a ⋅ ●E{q} b) → a = b.
  Proof. unfold_leibniz. apply excl_auth_frac_op_inv. Qed.

  Lemma excl_auth_frac_agreeN q n a b : ✓{n} (●E{q} a ⋅ ◯E b) → a ≡{n}≡ b.
  Proof.
    rewrite/excl_auth_frac=>/auth_both_dfrac_validN-[] _ []Hinc Hv. move: Hinc.
    move/Some_includedN_exclusive/(_ Hv){Hv}. by rewrite (inj_iff Excl).
  Qed.
  Lemma excl_auth_frac_agree q a b : ✓ (●E{q} a ⋅ ◯E b) → a ≡ b.
  Proof.
    intros. apply equiv_dist=>n.
    by apply (excl_auth_frac_agreeN q), cmra_valid_validN.
  Qed.
  Lemma excl_auth_frac_agree_L `{!LeibnizEquiv A} q a b : ✓ (●E{q} a ⋅ ◯E b) → a = b.
  Proof. unfold_leibniz. apply excl_auth_frac_agree. Qed.

End excl_auth_frac.
