(*
 * Copyright (c) 2020-21 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(** Support code for [inductive_pointers.v]. *)

Require Import bluerock.prelude.base.
Require Import bluerock.prelude.addr.
Require Import bluerock.prelude.numbers.
Require Import bluerock.lang.cpp.semantics.values.

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
