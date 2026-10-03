(*
 * Copyright (c) 2020-21 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(** Support code for [inductive_pointers.v]. *)

Require Import skylabs.prelude.base.
Require Import skylabs.prelude.addr.
Require Import skylabs.prelude.numbers.
Require Import skylabs.lang.cpp.semantics.values.

Module address_sums.
  Definition offset_vaddr : Z -> vaddr -> option vaddr := λ z pa,
    let sum : Z := (Z.of_N pa + z)%Z in
    guard (0 ≤ sum)%Z;; Some (Z.to_N sum).

  Lemma offset_vaddr_eq z pa :
    let sum := (Z.of_N pa + z)%Z in
    (0 ≤ sum)%Z ->
    offset_vaddr z pa = Some (Z.to_N sum).
  Proof. rewrite /offset_vaddr/= => /= Hle. rewrite option_guard_True //. Qed.

  Lemma offset_vaddr_eq' {z pa} :
    offset_vaddr z pa <> None ->
    offset_vaddr z pa = Some (Z.to_N (Z.of_N pa + z)).
  Proof. rewrite /offset_vaddr/= => /=. case_guard; naive_solver. Qed.

  Lemma offset_vaddr_0 pa :
    offset_vaddr 0 pa = Some pa.
  Proof. rewrite offset_vaddr_eq Z.add_0_r ?N2Z.id //. lia. Qed.

  Lemma offset_vaddr_combine {pa o o'} :
    offset_vaddr o pa <> None ->
    offset_vaddr o pa ≫= offset_vaddr o' = offset_vaddr (o + o') pa.
  Proof.
    rewrite /offset_vaddr => Hval.
    by case_guard; rewrite /= Z.add_assoc ?Z2N.id.
  Qed.
  #[local] Open Scope Z_scope.

  #[local] Lemma offset_vaddr_increase off a b va :
    (a <= b)%N ->
    offset_vaddr off a = Some va ->
    exists vb, offset_vaddr off b = Some vb /\
      Z.of_N vb = Z.of_N va + (Z.of_N b - Z.of_N a).
  Proof.
    intros Hab. rewrite /offset_vaddr.
    case_guard; last discriminate.
    intros [= <-]. rewrite Z2N.id; last lia.
    rewrite option_guard_True; last lia.
    eexists. split; first done. rewrite Z2N.id; lia.
  Qed.

  #[local] Lemma fold_offset_vaddr_increase offsets a b va :
    (a <= b)%N ->
    foldr (fun off ova => ova ≫= offset_vaddr off) (Some a) offsets = Some va ->
    exists vb,
      foldr (fun off ova => ova ≫= offset_vaddr off) (Some b) offsets = Some vb /\
      Z.of_N vb = Z.of_N va + (Z.of_N b - Z.of_N a).
  Proof.
    revert va. induction offsets as [|off offsets IH]; intros va Hab; simpl.
    - intros [= <-]. exists b. split; [done|lia].
    - destruct (foldr (fun off ova => ova ≫= offset_vaddr off)
        (Some a) offsets) as [mid|] eqn:E; simpl; last discriminate.
      have [mid' [Emid Hmid]] := IH mid Hab eq_refl.
      rewrite Emid /=. intros Hva.
      have Hle : (mid <= mid')%N by lia.
      destruct (offset_vaddr_increase off mid mid' va Hle Hva)
        as (vb & Evb & Hvb).
      exists vb. split; [exact Evb|lia].
  Qed.

  #[local] Lemma fold_offset_vaddr_none offsets :
    foldr (fun off ova => ova ≫= offset_vaddr off) None offsets = None.
  Proof. induction offsets; by simpl; rewrite ?IHoffsets. Qed.

  #[local] Lemma offset_vaddr_increase_offset a b base va :
    a <= b ->
    offset_vaddr a base = Some va ->
    exists vb, offset_vaddr b base = Some vb /\
      Z.of_N vb = Z.of_N va + (b-a).
  Proof.
    intros Hab. rewrite /offset_vaddr.
    case_guard; last discriminate.
    intros [= <-]. rewrite Z2N.id; last lia.
    rewrite option_guard_True; last lia.
    eexists. split; first done. rewrite Z2N.id; lia.
  Qed.

  Lemma fold_offset_vaddr_increase_tail offsets root a b va :
    a <= b ->
    foldr (fun off ova => ova ≫= offset_vaddr off)
      (root ≫= offset_vaddr a) offsets = Some va ->
    exists vb,
      foldr (fun off ova => ova ≫= offset_vaddr off)
        (root ≫= offset_vaddr b) offsets = Some vb /\
      Z.of_N vb = Z.of_N va + (b-a).
  Proof.
    intros Hab.
    destruct root as [base|]; simpl; last by rewrite fold_offset_vaddr_none.
    destruct (offset_vaddr a base) as [mid|] eqn:E;
      last by rewrite fold_offset_vaddr_none.
    intros Hva.
    destruct (offset_vaddr_increase_offset a b base mid Hab E)
      as (mid' & Emid & Hmid).
    have Hle : (mid <= mid')%N by lia.
    destruct (fold_offset_vaddr_increase offsets mid mid' va Hle Hva)
      as (vb & Evb & Hvb).
    exists vb. rewrite Emid. split; [exact Evb|lia].
  Qed.

End address_sums.

Module merge_elems.
Section merge_elem.
  Context {X} (f : X -> X -> list X).
  Definition merge_elem (x0 : X) (xs : list X) : list X :=
    match xs with
    | x1 :: xs' => f x0 x1 ++ xs'
    | [] => [x0]
    end.
  Lemma merge_elem_nil x0 : merge_elem x0 [] = [x0].
  Proof. done. Qed.
  Lemma merge_elem_cons x0 x1 xs : merge_elem x0 (x1 :: xs) = f x0 x1 ++ xs.
  Proof. done. Qed.

  Definition merge_elems_aux : list X -> list X -> list X := foldr merge_elem.
  Local Arguments merge_elems_aux _ !_ /.
  Definition merge_elems : list X -> list X := merge_elems_aux [].
  Local Arguments merge_elems !_ /.
  Lemma merge_elems_cons x xs :
    merge_elems (x :: xs) = merge_elem x (merge_elems xs).
  Proof. done. Qed.
  Lemma merge_elems_aux_app ys xs1 xs2 :
    merge_elems_aux ys (xs1 ++ xs2) = merge_elems_aux (merge_elems_aux ys xs2) xs1.
  Proof. apply foldr_app. Qed.
  Lemma merge_elems_app xs1 xs2 :
    merge_elems (xs1 ++ xs2) = merge_elems_aux (merge_elems xs2) xs1.
  Proof. apply merge_elems_aux_app. Qed.
End merge_elem.
End merge_elems.
