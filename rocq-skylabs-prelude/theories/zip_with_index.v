(*
 * Copyright (C) 2022-2025 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bluerock.prelude.base.
Require Import bluerock.prelude.list.
Require Import bluerock.prelude.fin_maps.

(** [zip_with_index_from] converts a list [x0; x1; ... xn] to an association
list [(from, x0); (from + 1, x1); ... (from + n, xn)].

The crucial case is [from = 0], but the generalization is necessary at least in
inductive proofs.
*)

Definition zip_with_index_from {A} from (xs : list A) : list (nat * A) :=
  zip (seq from (length xs)) xs.
(* 
Alternatively, one might want to use [map_seq].
```
  Definition zip_with_index_from {A} from (xs : list A) : list (nat * A) :=
    map_to_list (map_seq from xs).
```
However, [map_to_list] does not give the expected order guarantee. For example
```
  Definition foo := zip_with_index_from 0 [42; 43; 44].
  Eval vm_compute in (zip_with_index_from 0 [42; 43; 44]).
  (* ^ = [(2, 44); (1, 43); (0, 42)] : list (nat * nat) *)
```
*)

Notation zip_with_index := (zip_with_index_from 0).

Section zip_with_index.
  Context {A : Type}.
  Implicit Types (x : A) (xs : list A) (i j : nat).

  Lemma length_zip_with_index xs :
    length (zip_with_index xs) = length xs.
  Proof. rewrite /zip_with_index length_zip_with length_seq. lia. Qed.

  Lemma zip_with_index_from_nil j :
    zip_with_index_from (A := A) j [] = [].
  Proof. done. Qed.
  Lemma zip_with_index_from_cons j x xs :
    zip_with_index_from j (x :: xs) = (j, x) :: zip_with_index_from (S j) xs.
  Proof. done. Qed.

  (* TODO (FM-2060): split this lemma. This probably only relies on the structure of
  [zip_with_index_from]'s "spine" as given by [.*1]. *)
  Lemma list_to_map_insert_zip_with_index_from `{FinMap nat M} i j x xs :
    i < length xs →
    list_to_map (<[i := (i + j, x)]> (zip_with_index_from j xs)) =@{M A}
      <[i + j := x]> (list_to_map (zip_with_index_from j xs)).
  Proof.
    elim: xs i j => /= [/ltac:(lia)|y xs IH] [j|i j /(proj2 (Nat.succ_lt_mono _ _))] Hlook /=;
      first by rewrite insert_insert.
    move: IH => /(_ i (S j) Hlook); rewrite Nat.add_succ_r => IH.
    rewrite insert_commute; last lia.
    by rewrite IH.
  Qed.

  Lemma list_to_map_insert_zip_with_index `{FinMap nat M} i x xs :
    i < length xs →
    list_to_map (<[i := (i, x)]> (zip_with_index xs)) =@{M A}
      <[i := x]> (list_to_map (zip_with_index xs)).
  Proof.
    have := Refine (list_to_map_insert_zip_with_index_from i 0 x xs).
    rewrite right_id_L. apply.
  Qed.

  Lemma NoDup_zip_with_index_from j xs : NoDup (zip_with_index_from j xs).
  Proof. apply /NoDup_zip_fst /NoDup_seq. Qed.

  Lemma zip_with_index_from_add_fmap j k xs :
    zip_with_index_from (j + k) xs = (λ iv, (j + fst iv, snd iv)) <$> zip_with_index_from k xs.
  Proof.
    elim: xs j k => [//|x xs IH] j k; rewrite !zip_with_index_from_cons fmap_cons //; csimpl.
    by rewrite -IH Nat.add_succ_r.
  Qed.
  Lemma zip_with_index_from_fmap j xs :
    zip_with_index_from j xs = (λ iv, (j + fst iv, snd iv)) <$> zip_with_index xs.
  Proof. rewrite -{1}(right_id_L 0 Nat.add j). apply zip_with_index_from_add_fmap. Qed.

  Lemma lookup_zip_with_index_from j k (v : A) xs :
    zip_with_index_from j xs !! k = Some (j + k, v) ↔
    xs !! k = Some v.
  Proof.
    elim: xs k j => [|x xs IH] k j /=;
      rewrite !(zip_with_index_from_nil, zip_with_index_from_cons) /=; [set_solver|].
    case: k => [|k] /=. { rewrite right_id_L. naive_solver. }
    rewrite -(IH _ (S j)). by rewrite Nat.add_succ_l Nat.add_succ_r.
  Qed.

  Lemma not_elem_of_zip_with_index_from_lt i j (v : A) xs :
    i < j →
    (i, v) ∈ zip_with_index_from j xs ↔ False.
  Proof.
    elim: xs i j => [|x xs IH] i j Hpos /=;
      rewrite !(zip_with_index_from_nil, zip_with_index_from_cons);
      [set_solver|].
    rewrite elem_of_cons; split_and!; last done.
    move=> [?|]. by simplify_eq; lia.
    apply IH. lia.
  Qed.

  Lemma not_elem_of_zip_with_index_from_succ j (v : A) xs :
    (j, v) ∈ zip_with_index_from (S j) xs ↔ False.
  Proof. by apply not_elem_of_zip_with_index_from_lt; lia. Qed.

  (* XXX names? *)
  Lemma elem_of_zip_with_index_from_plus_equiv j k (v : A) xs :
    (j + k, v) ∈ zip_with_index_from j xs ↔
    zip_with_index_from j xs !! k = Some (j + k, v).
  Proof.
    elim: xs j k => [//|x xs IH] j k; [set_solver|].
    rewrite !(zip_with_index_from_nil, zip_with_index_from_cons) elem_of_cons //; csimpl.
    case: k => [|k]; rewrite !(right_id_L, Nat.add_succ_r) -?Nat.add_succ_l /=. {
      trans (v = x); [split|]; [|naive_solver..].
      move=>[[] //|/not_elem_of_zip_with_index_from_lt []]; lia.
    }
    rewrite (IH (S j) k). naive_solver eauto with lia.
  Qed.

  Lemma elem_of_zip_with_index_from_plus j k (v : A) xs :
    (j + k, v) ∈ zip_with_index_from j xs ↔ xs !! k = Some v.
  Proof.
    by rewrite -(lookup_zip_with_index_from j) elem_of_zip_with_index_from_plus_equiv.
  Qed.

  Lemma lookup_zip_with_index_from_sub i j (v : A) xs :
    j <= i →
    zip_with_index_from j xs !! (i - j) = Some (i, v) ↔ xs !! (i - j) = Some v.
  Proof.
    intros. by rewrite -(lookup_zip_with_index_from j (i - j)) Nat.add_comm Nat.sub_add.
  Qed.

  Lemma elem_of_zip_with_index_from i j (v : A) xs :
    j <= i →
    (i, v) ∈ zip_with_index_from j xs ↔ xs !! (i - j) = Some v.
  Proof.
    intros. rewrite -{1}(Nat.sub_add j i) // {1}(Nat.add_comm).
    apply elem_of_zip_with_index_from_plus.
  Qed.
End zip_with_index.
