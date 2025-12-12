(*
 * Copyright (C) 2021 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Export stdpp.sets.
Require Import bluerock.prelude.base.

(** * Small extensions to [stdpp.sets]. *)

#[global] Instance set_pairwise_disjoint `{ElemOf C D, Disjoint C} :
    PairwiseDisjoint D | 100 :=	(** high cost supports specialization *)
  (** Leibniz equality here is fine for all finite sets, [coPset], and
      [coGset]. We could presumably generalize to setoid equivalence. *)
  fun Xs Ys => set_Forall (fun X => set_Forall (fun Y => X = Y \/ X ## Y) Ys) Xs.

#[global] Instance set_pairwise_disjoint_symmetric
    `{ElemOf C D, Disjoint C, !Symmetric (##@{C})} :
  Symmetric (##ₚ@{D}) | 100. (** high cost supports specialization *)
Proof. intros ?? HD ? HY ? HX. destruct (HD _ HX _ HY). by left. by right. Qed.

Section semi_set.
  #[local] Set Default Proof Using "Type*".
  Context `{SemiSet A C}.
  Implicit Types X Y : C.

  (** Witnesses for disjoint semisets *)
  Lemma set_disjoint_not_Forall_1 X Y : X ## Y <-> set_Forall (.∉ Y) X.
  Proof. done. Qed.
  Lemma set_disjoint_not_Forall_2 X Y : X ## Y <-> set_Forall (.∉ X) Y.
  Proof. by rewrite [X ## Y]symmetry_iff. Qed.

  (* More convenient for rewriting than [set_Forall_union_inv_1,
  set_Forall_union_inv_2, set_Forall_union]. *)
  Lemma set_Forall_union_equiv (P : A → Prop) X Y :
    set_Forall P (X ∪ Y) ↔ set_Forall P X ∧ set_Forall P Y.
  Proof. unfold set_Forall. set_solver. Qed.
End semi_set.

(** Pairwise disjointness for [SemiSet] *)
Section semi_set.
  #[local] Set Default Proof Using "Type*".
  Context `{SemiSet C D, Disjoint C}.
  Implicit Types X Y : C.
  Implicit Types Xs Ys : D.

  Lemma pairwise_disjoint_singleton X : [##ₚ@{D} {[X]}].
  Proof.
    rewrite/pairwise_disjoint/set_pairwise_disjoint.
    rewrite !set_Forall_singleton. by left.
  Qed.

  Lemma pairwise_disjoint_union_1 Xs Ys :
    [##ₚ Xs ∪ Ys] -> [##ₚ Xs] /\ [##ₚ Ys] /\ Xs ##ₚ Ys.
  Proof.
    intros HD. split_and?.
    - apply (set_Forall_union_inv_1 _ _ Ys)=>X /HD. by apply set_Forall_union_inv_1.
    - apply (set_Forall_union_inv_2 _ Xs)=>X /HD. by apply set_Forall_union_inv_2.
    - apply (set_Forall_union_inv_1 _ _ Ys)=>X /HD. by apply set_Forall_union_inv_2.
  Qed.
  Lemma pairwise_disjoint_union_2 `{!Symmetric (##@{C})} Xs Ys :
    [##ₚ Xs] -> [##ₚ Ys] -> Xs ##ₚ Ys -> [##ₚ Xs ∪ Ys].
  Proof.
    intros HXs HYs HXYs. apply set_Forall_union=>X HX; apply set_Forall_union=>Y HY.
    - exact: HXs.
    - exact: HXYs.
    - apply symmetry in HXYs. exact: HXYs.
    - exact: HYs.
  Qed.
  Lemma pairwise_disjoint_union `{!Symmetric (##@{C})} Xs Ys :
    [##ₚ Xs ∪ Ys] <-> [##ₚ Xs] /\ [##ₚ Ys] /\ Xs ##ₚ Ys.
  Proof.
    split.
    - by apply pairwise_disjoint_union_1.
    - intros (? & ? & ?). by apply pairwise_disjoint_union_2.
  Qed.
End semi_set.
#[global] Hint Resolve pairwise_disjoint_union_2 : core.

Section top_set.
  Context `{TopSet A C}.
  Implicit Types x y : A.
  Implicit Types X Y : C.

  #[local] Set Default Proof Using "Type*".

  (* Named after [union_empty_l] (+ missing [top_set_] prefix) *)
  #[global] Instance top_set_intersection_top_l : LeftId (≡@{C}) ⊤ (∩).
  Proof. intros ?. set_solver. Qed.
  #[global] Instance top_set_intersection_top_r : RightId (≡@{C}) ⊤ (∩).
  Proof. intros ?. set_solver. Qed.

  Section leibniz.
    Context `{!LeibnizEquiv C}.

    #[global] Instance top_set_intersection_top_l_L : LeftId (=@{C}) ⊤ (∩).
    Proof. intros ?. unfold_leibniz. apply (left_id _ _). Qed.
    #[global] Instance top_set_intersection_top_r_L : RightId (=@{C}) ⊤ (∩).
    Proof. intros ?. unfold_leibniz. apply (right_id _ _). Qed.
  End leibniz.
End top_set.

Lemma union_minus_l `{Set_ A C} (X Y : C) : (X ∪ Y) ∖ X ≡ Y ∖ X.
Proof. set_solver. Qed.
Lemma union_minus_l_L `{Set_ A C, !LeibnizEquiv C} (X Y : C) : (X ∪ Y) ∖ X = Y ∖ X.
Proof. set_solver. Qed.
Lemma union_minus_r `{Set_ A C} (X Y : C) : (X ∪ Y) ∖ Y ≡ X ∖ Y.
Proof. set_solver. Qed.
Lemma union_minus_r_L `{Set_ A C, !LeibnizEquiv C} (X Y : C) : (X ∪ Y) ∖ Y = X ∖ Y.
Proof. set_solver. Qed.
