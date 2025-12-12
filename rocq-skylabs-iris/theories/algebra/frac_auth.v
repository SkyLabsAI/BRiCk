(*
 * Copyright (C) 2021-2023 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Export iris.algebra.lib.frac_auth.
Require Export bluerock.prelude.base.
Set Printing Coercions.

(** * Extension to [frac_auth] *)
(** Extend [iris.algebra.lib.frac_auth] with fractional authorative elements
    [frac_auth_auth_frac] (notation [●F{q} a]) such that

    - fraction [1] coincides with the existing [frac_auth_frac]
      (notation [●F a])

    - and is FracSplittable.
*)


(** Fractional authorative elements for [frac_auth]. *)
Definition frac_auth_auth_frac {SI : sidx} {A : cmra} (q : Qp) (a : A) : frac_authR A :=
  ●{#q} (Some (1%Qp,a)).

#[global] Instance: Params (@frac_auth_auth_frac) 2 := {}.
#[global] Hint Opaque frac_auth_auth_frac : typeclass_instances.

Notation "●F{ q } a" := (frac_auth_auth_frac q a) (at level 10, format "●F{ q }  a").

Section frac_auth_auth_frac.
  Context {SI : sidx} {A : cmra}.
  Implicit Types a b : A.
  Import proofmode_classes.

  Lemma frac_auth_auth_auth_frac a : ●F a = ●F{1} a.
  Proof. done. Qed.

  #[global] Instance frac_auth_auth_frac_ne q : NonExpansive (@frac_auth_auth_frac _ A q).
  Proof. solve_proper. Qed.
  #[global] Instance frac_auth_auth_frac_proper q : Proper ((≡) ==> (≡)) (@frac_auth_auth_frac _ A q).
  Proof. solve_proper. Qed.

  #[global] Instance frac_auth_auth_frac_discrete q a `{!Discrete a} : Discrete (●F{q} a).
  Proof. apply auth_auth_discrete. apply Some_discrete, _. apply _. Qed.

  Lemma frac_auth_auth_frac_op p q a : ●F{p + q} a ≡ ●F{p} a ⋅ ●F{q} a.
  Proof. by rewrite -auth_auth_dfrac_op. Qed.

  #[global] Instance frac_auth_auth_frac_is_op q q1 q2 a :
    IsOp q q1 q2 -> IsOp' (●F{q} a) (●F{q1} a) (●F{q2} a).
  Proof. rewrite /frac_auth_auth_frac. apply _. Qed.

  Lemma frac_auth_auth_frac_validN n q a : ✓{n} (●F{q} a) ↔ (q ≤ 1)%Qp ∧ ✓{n} a.
  Proof.
    rewrite /frac_auth_auth_frac.
    rewrite auth_auth_dfrac_validN Some_validN pair_validN.
    by intuition.
  Qed.
  Lemma frac_auth_auth_frac_valid q a : ✓ (●F{q} a) ↔ (q ≤ 1)%Qp ∧ ✓ a.
  Proof.
    rewrite/frac_auth_auth_frac.
    rewrite auth_auth_dfrac_valid Some_valid pair_valid.
    by intuition.
  Qed.

  Lemma frac_auth_auth_frac_op_validN n q1 q2 a1 a2 :
    ✓{n} (●F{q1} a1 ⋅ ●F{q2} a2) ↔ (q1 + q2 ≤ 1)%Qp ∧ a1 ≡{n}≡ a2 ∧ ✓{n} a1.
  Proof.
    rewrite/frac_auth_auth_frac.
    rewrite auth_auth_dfrac_op_validN Some_validN pair_validN (inj_iff Some).
    split.
    { by move => [? [[? ?] [? ?]]]. }
    by repeat split; intuition.
  Qed.
  Lemma frac_auth_auth_frac_op_valid q1 q2 a1 a2 :
    ✓ (●F{q1} a1 ⋅ ●F{q2} a2) ↔ (q1 + q2 ≤ 1)%Qp ∧ a1 ≡ a2 ∧ ✓ a1.
  Proof.
    rewrite/frac_auth_auth_frac.
    rewrite auth_auth_dfrac_op_valid Some_valid pair_valid.
    rewrite (inj_iff Some).
    split.
    { by move => [? [[? ?] [? ?]]]. }
    by repeat split; intuition.
  Qed.

  Lemma frac_auth_auth_frac_op_valid_L `{!LeibnizEquiv A} q1 q2 a1 a2 :
    ✓ (●F{q1} a1 ⋅ ●F{q2} a2) ↔ (q1 + q2 ≤ 1)%Qp ∧ a1 = a2 ∧ ✓ a1.
  Proof. unfold_leibniz. apply frac_auth_auth_frac_op_valid. Qed.

  Lemma frac_auth_auth_frac_op_invN n p a q b : ✓{n} (●F{p} a ⋅ ●F{q} b) → a ≡{n}≡ b.
  Proof.
    rewrite /frac_auth_auth_frac=>/auth_auth_dfrac_op_invN.
    rewrite (inj_iff Some).
    by move => [] //.
  Qed.
  Lemma frac_auth_auth_frac_op_inv p a q b : ✓ (●F{p} a ⋅ ●F{q} b) → a ≡ b.
  Proof.
    rewrite/frac_auth_auth_frac=>/auth_auth_dfrac_op_inv.
    rewrite (inj_iff Some).
    by move => [] //.
  Qed.
  Lemma frac_auth_auth_frac_op_inv_L `{!LeibnizEquiv A} p a q b :
    ✓ (●F{p} a ⋅ ●F{q} b) → a = b.
  Proof. unfold_leibniz. apply frac_auth_auth_frac_op_inv. Qed.

  Lemma frac_auth_auth_frag_includedN n q1 q2 a b :
    ✓{n} (●F{q1} a ⋅ ◯F{q2} b) → Some b ≼{n} Some a.
  Proof.
    rewrite Some_includedN. move/auth_both_dfrac_validN=>-[]_ []. case/Some_includedN.
    - move=>-[] _ /=. by left.
    - move/pair_includedN=>-[]_. by right.
  Qed.
  Lemma frac_auth_auth_frag_included `{!CmraDiscrete A} q1 q2 a b :
    ✓ (●F{q1} a ⋅ ◯F{q2} b) → Some b ≼ Some a.
  Proof.
    move/cmra_valid_validN/(_ sidx_zero)/frac_auth_auth_frag_includedN.
    exact: cmra_discrete_included_r.
  Qed.

  Lemma frac_auth_auth_frag_includedN_total `{!CmraTotal A} n q1 q2 a b :
    ✓{n} (●F{q1} a ⋅ ◯F{q2} b) → b ≼{n} a.
  Proof. by move/frac_auth_auth_frag_includedN/Some_includedN_total. Qed.
  Lemma frac_auth_auth_frag_included_total `{!CmraDiscrete A, !CmraTotal A} q1 q2 a b :
    ✓ (●F{q1} a ⋅ ◯F{q2} b) → b ≼ a.
  Proof.
    move/cmra_valid_validN/(_ sidx_zero)/frac_auth_auth_frag_includedN_total.
    exact: cmra_discrete_included_r.
  Qed.

  Lemma frac_auth_auth_frac_agreeN q n a b : ✓{n} (●F{q} a ⋅ ◯F b) → a ≡{n}≡ b.
  Proof.
    rewrite/frac_auth_auth_frac=>/auth_both_dfrac_validN-[] _ []Hinc Hv. move: Hinc.
    by move/Some_includedN_exclusive/(_ Hv){Hv} => [].
  Qed.
  Lemma frac_auth_auth_frac_agree q a b : ✓ (●F{q} a ⋅ ◯F b) → a ≡ b.
  Proof.
    intros. apply equiv_dist=>n.
    by apply (frac_auth_auth_frac_agreeN q), cmra_valid_validN.
  Qed.
  Lemma frac_auth_frac_agree_L `{!LeibnizEquiv A} q a b :
    ✓ (●F{q} a ⋅ ◯F b) → a = b.
  Proof. unfold_leibniz. apply frac_auth_auth_frac_agree. Qed.

End frac_auth_auth_frac.
