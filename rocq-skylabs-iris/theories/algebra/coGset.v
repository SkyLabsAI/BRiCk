(*
 * Copyright (c) 2021 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *
 * This file defines union and disjoint union CMRAs for [coGset A]. It
 * was originally written (and not distributed) in March 2020 by David
 * Swasey:
 *
 *	Copyright (C) 2020 David Swasey
 *
 *	SPDX-License-Identifier: BSD-3-Clause
 *
 * Swasey had derived it from similar constructions for [gset A],
 * which is code original to the Iris project. That original code is
 *
 *	Copyright Iris developers and contributors
 *
 * and used according to the following license.
 *
 *	SPDX-License-Identifier: BSD-3-Clause
 *
 * Original Code:
 * https://gitlab.mpi-sws.org/iris/iris/-/blob/79a110823166f989e622c8cdf1a8d564cc2078fd/iris/algebra/gset.v
 *
 * Original Iris License:
 * https://gitlab.mpi-sws.org/iris/iris/-/blob/79a110823166f989e622c8cdf1a8d564cc2078fd/LICENSE-CODE
 *)

Require Export stdpp.coGset.
Require Export bluerock.iris.extra.algebra.base.

(** Misplaced: Upstream to [iris.algebra.coGset]? *)

(** * The union CMRA *)
Section coGset.
  Context {SI : sidx} `{Countable A}.
  Notation C := (coGset A).
  Implicit Types X Y : C.

  Canonical Structure coGsetO := discreteO C.

  Local Instance coGset_valid : Valid C := λ _, True.
  Local Instance coGset_unit : Unit C := (∅ : C).
  Local Instance coGset_op : Op C := union.
  Local Instance coGset_pcore : PCore C := Some.

  Lemma coGset_op_union X Y : X ⋅ Y = X ∪ Y.
  Proof. done. Qed.
  Lemma coGset_core_self X : core X = X.
  Proof. done. Qed.
  Lemma coGset_included X Y : X ≼ Y ↔ X ⊆ Y.
  Proof.
    split.
    - intros [Z ->]. rewrite coGset_op_union. set_solver.
    - intros HY%subseteq_union. exists Y. by rewrite -{1}HY.
  Qed.

  Lemma coGset_ra_mixin : RAMixin C.
  Proof.
    apply ra_total_mixin; eauto.
    - solve_proper.
    - solve_proper.
    - done.
    - intros X1 X2 X3. by rewrite !coGset_op_union assoc.
    - intros X1 X2. by rewrite !coGset_op_union comm.
    - intros X. by rewrite coGset_core_self idemp.
  Qed.
  Canonical Structure coGsetR := discreteR C coGset_ra_mixin.

  Global Instance coGset_cmra_discrete : CmraDiscrete coGsetR.
  Proof. apply discrete_cmra_discrete. Qed.

  Lemma coGset_ucmra_mixin : UcmraMixin C.
  Proof. split; [done| |done]. intros X. by rewrite coGset_op_union left_id. Qed.
  Canonical Structure coGsetUR := Ucmra C coGset_ucmra_mixin.

  Global Instance coGset_core_id X : CoreId X.
  Proof. apply core_id_total. by rewrite coGset_core_self. Qed.

  Lemma coGset_opM X mY : X ⋅? mY ≡ X ∪ default ∅ mY.
  Proof. destruct mY; by rewrite /= ?right_id. Qed.
  Lemma coGset_opM_L `{!LeibnizEquiv C} X mY : X ⋅? mY = X ∪ default ∅ mY.
  Proof. unfold_leibniz. apply coGset_opM. Qed.

  Lemma coGset_update X Y : X ~~> Y.
  Proof. done. Qed.

  Lemma coGset_local_update X Y X' : X ⊆ X' → (X,Y) ~l~> (X',X').
  Proof.
    intros <-%subseteq_union.
    rewrite local_update_unital_discrete=> Z' _ ->.
    split; [done|]. rewrite !coGset_op_union. set_solver-.
  Qed.

End coGset.

Global Arguments coGsetO {_} _ {_ _} : assert.
Global Arguments coGsetR {_} _ {_ _} : assert.
Global Arguments coGsetUR {_} _ {_ _} : assert.

(** * The disjoint union CMRA *)
Inductive coGset_disj `{Countable A} :=
  | CoGSet (X : coGset A)
  | CoGSetBot.
Global Arguments coGset_disj _ {_ _} : assert.

Definition CoGSet_uninj `{Countable A} (X : coGset_disj A) : coGset A :=
  match X with CoGSet X => X | CoGSetBot => ∅ end.
Global Arguments CoGSet_uninj {_ _ _} !_ / : simpl nomatch, assert.

Global Instance coGset_disj_eq_dec `{Countable A} : EqDecision (coGset_disj A).
Proof. solve_decision. Defined.
Global Instance coGset_disj_countable `{Countable A} : Countable (coGset_disj A).
Proof.
  apply (inj_countable' (λ X, if X is CoGSet X then Some X else None)
    (from_option CoGSet CoGSetBot)). by intros [].
Defined.

Section set_disj.
  Context {SI : sidx} `{Countable A, Infinite A}.
  Notation C := (coGset A).
  Implicit Types x y : coGset_disj A.
  Implicit Types X Y : coGset A.

  Arguments op _ _ !_ !_ /.
  Arguments cmra_op _ !_ !_ /.
  Arguments ucmra_op _ !_ !_ /.

  Canonical Structure coGset_disjO := leibnizO (coGset_disj A).

  Local Instance coGset_disj_valid : Valid (coGset_disj A) := λ x,
    match x with CoGSet _ => True | CoGSetBot => False end.
  Local Instance coGset_disj_unit : Unit (coGset_disj A) := CoGSet ∅.
  Local Instance coGset_disj_op : Op (coGset_disj A) := λ x y,
    match x, y with
    | CoGSet X, CoGSet Y =>
      if decide (X ## Y) then CoGSet (X ∪ Y) else CoGSetBot
    | _, _ => CoGSetBot
    end.
  Local Instance coGset_disj_pcore : PCore (coGset_disj A) := λ _, Some ε.

  Ltac coGset_disj_solve :=
    repeat (simpl || case_decide);
    first [apply (f_equal CoGSet)|done|exfalso]; set_solver by eauto.

  Lemma coGset_disj_included X Y : CoGSet X ≼ CoGSet Y ↔ X ⊆ Y.
  Proof.
    split.
    - move=>[] [Z|] /=; try case_decide; inversion_clear 1; set_solver.
    - intros (Z&->&?)%subseteq_disjoint_union_L.
      exists (CoGSet Z). coGset_disj_solve.
  Qed.
  Lemma coGset_disj_valid_inv_l X y :
    ✓ (CoGSet X ⋅ y) → ∃ Y, y = CoGSet Y ∧ X ## Y.
  Proof. destruct y; repeat (simpl || case_decide); by eauto. Qed.
  Lemma coGset_disj_union X Y :
    X ##@{C} Y → CoGSet X ⋅ CoGSet Y = CoGSet (X ∪ Y).
  Proof. intros. by rewrite /= decide_True. Qed.
  Lemma coGset_disj_valid_op X Y : ✓ (CoGSet X ⋅ CoGSet Y) ↔ X ## Y.
  Proof. simpl. case_decide; by split. Qed.
  Lemma coGset_disj_valid_inv x y :
    ✓ (x ⋅ y) → ∃ X Y, x = CoGSet X ∧ y = CoGSet Y ∧ X ## Y.
  Proof. destruct x, y=>//= /coGset_disj_valid_op. eauto. Qed.

  Lemma coGset_disj_ra_mixin : RAMixin (coGset_disj A).
  Proof.
    apply ra_total_mixin; eauto.
    - intros [?|]; destruct 1; coGset_disj_solve.
    - by constructor.
    - by destruct 1.
    - intros [X1|] [X2|] [X3|]; coGset_disj_solve.
    - intros [X1|] [X2|]; coGset_disj_solve.
    - intros [X|]; coGset_disj_solve.
    - exists (CoGSet ∅); coGset_disj_solve.
    - intros [X1|] [X2|]; coGset_disj_solve.
  Qed.
  Canonical Structure coGset_disjR := discreteR (coGset_disj A) coGset_disj_ra_mixin.

  Global Instance coGset_disj_cmra_discrete : CmraDiscrete coGset_disjR.
  Proof. apply discrete_cmra_discrete. Qed.

  Lemma coGset_disj_ucmra_mixin : UcmraMixin (coGset_disj A).
  Proof. split; try apply _ || done. intros [X|]; coGset_disj_solve. Qed.
  Canonical Structure coGset_disjUR := Ucmra (coGset_disj A) coGset_disj_ucmra_mixin.

  Global Instance coGset_disj_core_id : CoreId (CoGSet (∅ : coGset A)).
  Proof. by rewrite/CoreId /pcore. Qed.

  Local Arguments op _ _ _ _ : simpl never.

  Lemma coGset_disj_alloc_updateP_strong P (Q : coGset_disj A → Prop) X :
    (∀ Y, X ⊆ Y → ∃ j, j ∉ Y ∧ P j) →
    (∀ i, i ∉ X → P i → Q (CoGSet ({[i]} ∪ X))) →
    CoGSet X ~~>: Q.
  Proof.
    intros Hfresh HQ.
    apply cmra_discrete_total_updateP=> ? /coGset_disj_valid_inv_l [Y [->?]].
    destruct (Hfresh (X ∪ Y)) as (i&?&?); first set_solver.
    exists (CoGSet ({[ i ]} ∪ X)); split.
    - apply HQ; set_solver by eauto.
    - apply coGset_disj_valid_op. set_solver by eauto.
  Qed.
  Lemma coGset_disj_alloc_updateP_strong' P X :
    (∀ Y, X ⊆ Y → ∃ j, j ∉ Y ∧ P j) →
    CoGSet X ~~>: λ y, ∃ i, y = CoGSet ({[ i ]} ∪ X) ∧ i ∉ X ∧ P i.
  Proof. eauto using coGset_disj_alloc_updateP_strong. Qed.

  Lemma coGset_disj_alloc_empty_updateP_strong P (Q : coGset_disj A → Prop) :
    (∀ Y : C, ∃ j, j ∉ Y ∧ P j) →
    (∀ i, P i → Q (CoGSet {[i]})) → CoGSet ∅ ~~>: Q.
  Proof.
    intros. apply (coGset_disj_alloc_updateP_strong P); eauto.
    intros i. rewrite right_id_L. auto.
  Qed.
  Lemma coGset_disj_alloc_empty_updateP_strong' P :
    (∀ Y : C, ∃ j, j ∉ Y ∧ P j) →
    CoGSet ∅ ~~>: λ y, ∃ i, y = CoGSet {[ i ]} ∧ P i.
  Proof. eauto using coGset_disj_alloc_empty_updateP_strong. Qed.

  (** The "fresh updates" section of [iris.algebra.gset] is not sound
      for [coGset]. *)

  Lemma coGset_disj_dealloc_local_update X Y :
    (CoGSet X, CoGSet Y) ~l~> (CoGSet (X ∖ Y), CoGSet ∅).
  Proof.
    apply local_update_total_valid=> _ _ /coGset_disj_included HYX.
    rewrite local_update_unital_discrete=> -[Xf|] _ /leibniz_equiv_iff //=.
    rewrite {1}/op /=. destruct (decide _) as [HXf|]; [intros[= ->]|done].
    by rewrite difference_union_distr_l_L
      difference_diag_L !left_id_L difference_disjoint_L.
  Qed.
  Lemma coGset_disj_dealloc_empty_local_update X Z :
    (CoGSet Z ⋅ CoGSet X, CoGSet Z) ~l~> (CoGSet X, CoGSet ∅).
  Proof.
    apply local_update_total_valid=> /coGset_disj_valid_op HZX _ _.
    assert (X = (Z ∪ X) ∖ Z) as HX by set_solver.
    rewrite coGset_disj_union // {2}HX. apply coGset_disj_dealloc_local_update.
  Qed.
  Lemma coGset_disj_dealloc_op_local_update X Y Z :
    (CoGSet Z ⋅ CoGSet X, CoGSet Z ⋅ CoGSet Y) ~l~> (CoGSet X, CoGSet Y).
  Proof.
    rewrite -{2}(left_id_L ε _ (CoGSet Y)).
    apply op_local_update_frame, coGset_disj_dealloc_empty_local_update.
  Qed.

  Lemma coGset_disj_alloc_op_local_update X Y Z :
    Z ## X →
    (CoGSet X, CoGSet Y) ~l~>
    (CoGSet Z ⋅ CoGSet X, CoGSet Z ⋅ CoGSet Y).
  Proof.
    intros. apply op_local_update_discrete. by rewrite coGset_disj_valid_op.
  Qed.
  Lemma coGset_disj_alloc_local_update X Y Z :
    Z ## X → (CoGSet X, CoGSet Y) ~l~> (CoGSet (Z ∪ X), CoGSet (Z ∪ Y)).
  Proof.
    intros. apply local_update_total_valid=> _ _ /coGset_disj_included ?.
    rewrite -!coGset_disj_union //; last set_solver.
    auto using coGset_disj_alloc_op_local_update.
  Qed.
  Lemma coGset_disj_alloc_empty_local_update X Z :
    Z ## X → (CoGSet X, CoGSet ∅) ~l~> (CoGSet (Z ∪ X), CoGSet Z).
  Proof.
    intros. rewrite -{2}(right_id_L _ union Z).
    by apply coGset_disj_alloc_local_update.
  Qed.

  (** The [CoGSet_uninj] operation *)
  Lemma CoGSet_uninj_op x y :
    ✓ (x ⋅ y) → CoGSet_uninj (x ⋅ y) = CoGSet_uninj x ∪ CoGSet_uninj y.
  Proof.
    intros (?&?&->&->&?)%coGset_disj_valid_inv. by rewrite coGset_disj_union.
  Qed.
End set_disj.

Arguments coGset_disjO {_} _ {_ _} : assert.
Arguments coGset_disjR {_} _ {_ _ _} : assert.
Arguments coGset_disjUR {_} _ {_ _ _} : assert.
