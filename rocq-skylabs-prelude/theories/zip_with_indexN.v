(*
 * Copyright (C) 2022-2025 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import stdpp.gmap.
Require Import bluerock.prelude.base.
Require Import bluerock.prelude.list_numbers.
Require Import bluerock.prelude.fin_maps.
Require Import bluerock.prelude.zip_with_index.

(** [zip_with_indexN_from] is like [zip_with_index_from], but for [N]. *)
Definition zip_with_indexN_from {A} from (xs : list A) : list (N * A) :=
  zip (seqN from (lengthN xs)) xs.
Notation zip_with_indexN := (zip_with_indexN_from 0).

Section zip_with_indexN_from.
  Open Scope N_scope.
  Context {A : Type}.
  Implicit Types (x : A) (xs : list A) (i j : N).

  Lemma zip_with_indexN_from_nil j :
    zip_with_indexN_from (A := A) j [] = [].
  Proof. done. Qed.

  Lemma zip_with_indexN_from_cons j x xs :
    zip_with_indexN_from j (x :: xs) = (j, x) :: zip_with_indexN_from (N.succ j) xs.
  Proof. by rewrite /zip_with_indexN_from lengthN_cons N.add_1_r seqN_S_start. Qed.

  Lemma zip_with_indexN_from_app j xs ys :
    zip_with_indexN_from j (xs ++ ys) = zip_with_indexN_from j xs ++ zip_with_indexN_from (lengthN xs + j) ys.
  Proof.
    elim: xs j => [//|x xs /= IH] j.
    rewrite !zip_with_indexN_from_cons {}IH /= lengthN_cons; do 3! f_equal; lia.
  Qed.

  Lemma zip_with_indexN_zip_with_index_from j xs :
    zip_with_indexN_from j xs = (λ '(i, x), (N.of_nat i, x)) <$> zip_with_index_from (N.to_nat j) xs.
  Proof.
    rewrite /zip_with_indexN_from /zip_with_index_from.
    elim: xs j => [//|x xs IHxs] j. csimpl.
    rewrite !lengthN_simpl N.add_1_r seqN_S_start /= {}IHxs.
    by rewrite N2Nat.id N2Nat.inj_succ.
  Qed.

  (* Not just [zip_with_indexN_zip_with_index_from] *)
  Lemma zip_with_indexN_zip_with_index xs :
    zip_with_indexN xs = (λ '(i, x), (N.of_nat i, x)) <$> zip_with_index xs.
  Proof. apply zip_with_indexN_zip_with_index_from. Qed.

  Lemma length_zip_with_indexN xs :
    length (zip_with_indexN xs) = length xs.
  Proof.
    by rewrite zip_with_indexN_zip_with_index length_fmap length_zip_with_index.
  Qed.

  Lemma zip_with_indexN_from_insert i j x xs :
    zip_with_indexN_from j (<[i := x]> xs) = <[i := (j + i, x)%N]> (zip_with_indexN_from j xs).
  Proof.
    rewrite /zip_with_indexN_from lengthN_insertN.
    rewrite !list_insertN_insert insert_zip_with -!list_insertN_insert.
    by rewrite insertN_seqN.
  Qed.
  Lemma zip_with_indexN_insert i x xs :
    zip_with_indexN (<[i := x]> xs) = <[i := (i, x)]> (zip_with_indexN xs).
  Proof. by rewrite zip_with_indexN_from_insert left_id_L. Qed.

  Lemma NoDup_zip_with_indexN_from j xs : NoDup (zip_with_indexN_from j xs).
  Proof. apply /NoDup_zip_fst /NoDup_seqN. Qed.

  Lemma zip_with_indexN_from_add_fmap j k xs :
    zip_with_indexN_from (j + k) xs = (λ iv, (j + fst iv, snd iv)) <$> zip_with_indexN_from k xs.
  Proof.
    elim: xs j k => [//|x xs IH] j k; rewrite !zip_with_indexN_from_cons fmap_cons //; csimpl.
    by rewrite -IH N.add_succ_r.
  Qed.
  Lemma zip_with_indexN_from_fmap j xs :
    zip_with_indexN_from j xs = (λ iv, (j + fst iv, snd iv)) <$> zip_with_indexN xs.
  Proof. rewrite -{1}(right_id_L 0 N.add j). apply zip_with_indexN_from_add_fmap. Qed.

  (* TODO (FM-2060): split this lemma. This probably only relies on the structure of
  [zip_with_index_from]'s "spine" as given by [.*1]. *)
  Lemma list_to_map_insert_zip_with_indexN_from `{FinMap N M} i j x xs :
    i < lengthN xs →
    list_to_map (<[i := (i + j, x)]> (zip_with_indexN_from j xs)) =@{M A}
      <[i + j := x]> (list_to_map (zip_with_indexN_from j xs)).
  Proof.
    elim: xs i j => [|y xs IH]; rewrite lengthN_simpl ?N.add_1_r; [lia|].
    elim/N.peano_ind => [j|i _ j]; rewrite zip_with_indexN_from_cons; first
      by rewrite insert_insert.
    rewrite -N.succ_lt_mono => Hlook.
    move: IH => /(_ i (N.succ j) Hlook); rewrite !N.add_succ_r !N.add_succ_l /= => IH.
    rewrite insert_commute; last lia.
    by rewrite list_insertN_insert N2Nat.inj_succ /= IH.
  Qed.

  Lemma list_to_map_insert_zip_with_indexN `{FinMap N M} (i : N) xs (x : A) :
    i < lengthN xs →
    list_to_map (<[i := (i, x)]> (zip_with_indexN xs)) =@{M A}
      <[i := x]> (list_to_map (zip_with_indexN xs)).
  Proof.
    have := Refine (list_to_map_insert_zip_with_indexN_from i 0 x xs).
    rewrite right_id_L. apply.
  Qed.

  Lemma lookupN_zip_with_indexN k k' j xs a :
    zip_with_indexN_from j xs !! k = Some (k', a) ↔
    j + k = k' ∧ xs !! k = Some a.
  Proof.
    rewrite /zip_with_indexN_from !list_lookupN_lookup.
    elim: xs j k => [|x xs IHxs] j k /=.
    { rewrite !lookup_nil. naive_solver. }
    rewrite lengthN_cons N.add_1_r seqN_S_start /= lookup_cons.
    destruct k using N.peano_ind => //=.
    { rewrite right_id_L. naive_solver. }
    clear IHk.
    rewrite N2Nat.inj_succ {}IHxs /=.
    by rewrite N.add_succ_r N.add_succ_l.
  Qed.

  Lemma lookup_zip_with_indexN_from j k (v : A) xs :
    zip_with_indexN_from j xs !! k = Some (j + k, v) ↔
    xs !! k = Some v.
  Proof.
    (* Using [zip_with_indexN_zip_with_index_from] and
    [lookup_zip_with_index_from] requires an ugly proof.
    Adapting [lookup_zip_with_index_from] is easier. *)
    rewrite !list_lookupN_lookup.
    elim: xs k j => [|x xs IH] k j /=;
      rewrite !(zip_with_indexN_from_nil, zip_with_indexN_from_cons) /=; [set_solver|].
    destruct k as [|k] using N.peano_ind; [|rewrite N2Nat.inj_succ]; csimpl.
    { rewrite right_id_L. naive_solver. }
    rewrite -(IH k (N.succ j)). by rewrite N.add_succ_l N.add_succ_r.
  Qed.

  Lemma not_elem_of_zip_with_indexN_from_lt i j (v : A) xs :
    i < j →
    (i, v) ∈ zip_with_indexN_from j xs ↔ False.
  Proof.
    elim: xs i j => [//|x xs IH] i j Hpos;
      rewrite !(zip_with_indexN_from_nil, zip_with_indexN_from_cons);
      [set_solver|].
    rewrite elem_of_cons; split_and!; last done.
    move=> [?|]. by simplify_eq; lia.
    apply IH. lia.
  Qed.

  Lemma not_elem_of_zip_with_indexN_from_succ j (v : A) xs :
    (j, v) ∈ zip_with_indexN_from (N.succ j) xs ↔ False.
  Proof. by apply not_elem_of_zip_with_indexN_from_lt; lia. Qed.

  (* XXX names? *)
  Lemma elem_of_zip_with_indexN_from_plus_equiv j k (v : A) xs :
    (j + k, v) ∈ zip_with_indexN_from j xs ↔
    zip_with_indexN_from j xs !! k = Some (j + k, v).
  Proof.
    elim: xs j k => [//|x xs IH] j k;
      rewrite !(zip_with_indexN_from_nil, zip_with_indexN_from_cons);
      [set_solver|].
    rewrite elem_of_cons; csimpl; rewrite !list_lookupN_lookup.

    destruct k as [|k] using N.peano_ind => [|{IHk}];
      [rewrite right_id_L|
      rewrite N.add_succ_r -?N.add_succ_l /= N2Nat.inj_succ].
    {
      trans (v = x); [split|]; [|naive_solver..].
      move=>[[] //|/not_elem_of_zip_with_indexN_from_lt []]; lia.
    }
    rewrite (IH (N.succ j)) {IH}. naive_solver eauto with lia.
  Qed.

  Lemma elem_of_zip_with_indexN_from_plus j k (v : A) xs :
    (j + k, v) ∈ zip_with_indexN_from j xs ↔ xs !! k = Some v.
  Proof.
    by rewrite -(lookup_zip_with_indexN_from j) elem_of_zip_with_indexN_from_plus_equiv.
  Qed.

  Lemma elem_of_zip_with_indexN_from i j (v : A) xs :
    j <= i →
    (i, v) ∈ zip_with_indexN_from j xs ↔ xs !! (i - j) = Some v.
  Proof.
    intros.
    rewrite -{1}(N.sub_add j i) // (comm_L N.add (i - j) j).
    apply elem_of_zip_with_indexN_from_plus.
  Qed.

  Lemma elem_of_zip_with_indexN_from_1 i j (v : A) xs :
    (i, v) ∈ zip_with_indexN_from j xs →
    xs !! (i - j) = Some v ∧ j ≤ i < j + lengthN xs.
  Proof.
    rewrite elem_of_list_lookup => -[k].
    rewrite list_lookup_lookupN lookupN_zip_with_indexN => -[<- Hlook].
    rewrite -Hlook; split_and!; first f_equal; try lia.
    apply lookup_lt_Some in Hlook.
    rewrite /lengthN; lia.
  Qed.

  Lemma elem_of_zip_with_indexN k v xs :
    (k, v) ∈ zip_with_indexN xs ↔ xs !! k = Some v.
  Proof. by rewrite elem_of_zip_with_indexN_from ?N.sub_0_r; last lia. Qed.

  Lemma fst_zip_with_indexN_from j xs :
    (zip_with_indexN_from j xs).*1 = seqN j (lengthN xs).
  Proof.
    rewrite /zip_with_indexN_from fst_zip //.
    by rewrite length_lengthN seqN_lengthN -length_lengthN.
  Qed.

  Lemma NoDup_fst_zip_with_indexN_from j xs :
    NoDup (zip_with_indexN_from j xs).*1.
  Proof. rewrite fst_zip_with_indexN_from. apply NoDup_seqN. Qed.

  Lemma map_to_list_to_map_zip_with_indexN_from j xs :
    map_to_list (list_to_map (zip_with_indexN_from j xs)) ≡ₚ
    zip_with_indexN_from j xs.
  Proof. rewrite !map_to_list_to_map //. exact: NoDup_fst_zip_with_indexN_from. Qed.

  Lemma list_to_map_zip_with_indexN_from_Some xs j k v :
    j ≤ k →
    list_to_map (M := gmap _ _) (zip_with_indexN_from j xs) !! k = Some v ↔
    xs !! (k - j) = Some v.
  Proof.
    rewrite -elem_of_list_to_map; last exact: NoDup_fst_zip_with_indexN_from.
    apply elem_of_zip_with_indexN_from.
  Qed.

  Lemma list_to_map_zip_with_indexN_from_Some_1 xs j k v :
    list_to_map (M := gmap _ _) (zip_with_indexN_from j xs) !! k = Some v →
    xs !! (k - j) = Some v ∧ j ≤ k < j + lengthN xs.
  Proof.
    rewrite -elem_of_list_to_map; last exact: NoDup_fst_zip_with_indexN_from.
    apply elem_of_zip_with_indexN_from_1.
  Qed.

  Lemma list_to_map_zip_with_indexN_Some xs k v :
    list_to_map (M := gmap _ _) (zip_with_indexN xs) !! k = Some v ↔
    xs !! k = Some v.
  Proof. by rewrite list_to_map_zip_with_indexN_from_Some // N.sub_0_r. Qed.

  Lemma list_to_map_zip_with_indexN_from xs j k :
    j ≤ k →
    list_to_map (M := gmap _ _) (zip_with_indexN_from j xs) !! k = xs !! (k - j).
  Proof.
    intros; destruct (xs !! (k - j)) eqn:Hlook. exact /list_to_map_zip_with_indexN_from_Some.
    move: Hlook.
    rewrite -not_elem_of_list_to_map fst_zip_with_indexN_from.
    rewrite elem_of_seqN.
    rewrite lookup_ge_None /lengthN. lia.
  Qed.

  Lemma list_to_map_zip_with_indexN xs k :
    list_to_map (M := gmap _ _) (zip_with_indexN xs) !! k = xs !! k.
  Proof. by rewrite list_to_map_zip_with_indexN_from // N.sub_0_r. Qed.

  Lemma dom_list_to_map_zip_with_indexN_from xs j :
    dom (M := gmap _ _) (list_to_map (zip_with_indexN_from j xs)) =
    list_to_set (seqN j (lengthN xs)).
  Proof.
    apply set_eq => k.
    rewrite elem_of_dom elem_of_list_to_set elem_of_seqN; split.
    by move=> [? /list_to_map_zip_with_indexN_from_Some_1]; lia.
    intros. rewrite list_to_map_zip_with_indexN_from -?lookupN_is_Some; lia.
  Qed.

  Lemma dom_list_to_map_zip_with_indexN xs :
    dom (M := gmap _ _) (list_to_map (zip_with_indexN xs)) =
    list_to_set (seqN 0 (lengthN xs)).
  Proof. apply dom_list_to_map_zip_with_indexN_from. Qed.
End zip_with_indexN_from.
