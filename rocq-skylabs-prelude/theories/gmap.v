(*
 * Copyright (c) 2021-2025 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Export stdpp.gmap.
Require Export stdpp.mapset.

Require Import skylabs.prelude.base.
Require Import skylabs.prelude.fin_sets.
Require Import skylabs.prelude.list_numbers.

(* To upstream to Iris: using [mapseq_eq] directly would unfold a TC opaque
definition and interfere with TC search. *)
Lemma gset_eq `{Countable A} (X1 X2 : gset A) : X1 = X2 ↔ ∀ x, x ∈ X1 ↔ x ∈ X2.
Proof. apply mapset_eq. Qed.

(** [set_map] specialized to [gset]; avoids awkward type annotations such as
[set_map (C := gset _) (D := gset _)].
*)
#[global] Notation gset_map := (set_map (C := gset _) (D := gset _)) (only parsing).

#[global] Notation gset_concat_map :=
  (set_concat_map (C := gset _) (D := gset _)) (only parsing).

Definition gmap_kvmap {A} `{Countable K1, Countable K2}
    (f : K1 -> A -> option (K2 * A))
    (m : gmap K1 A) : gmap K2 A :=
  list_to_map (omap (uncurry f) (map_to_list m)).

(** Variant of [kmap] for [gmap] only. *)
Definition gmap_okmap {A} `{Countable K1, Countable K2}
    (f : K1 -> option K2)
    (m : gmap K1 A) : gmap K2 A :=
  gmap_kvmap (fun k1 v => k2 ← f k1; Some (k2, v)) m.

Definition gmap_preimage `{Countable K, Countable A} : gmap K A -> gmap A (gset K) :=
  map_preimg.

(* Like [set_concat_map], but purely in terms of gsets.
*)
Section gset_bind.
  Context `{Countable A} `{Countable B}.

  Definition gset_bind (f : A → gset B) (xs : gset A) : gset B :=
    gset_concat_map (elements ∘ f) xs.

  Lemma gset_bind_empty f :
    gset_bind f ∅ = ∅.
  Proof. done. Qed.

  Lemma elem_of_gset_bind f b xs :
    b ∈ gset_bind f xs ↔ ∃ x, x ∈ xs ∧ b ∈ f x.
  Proof. set_solver. Qed.

  #[global] Instance set_unfold_gset_bind f b xs P Q :
    (∀ x, SetUnfoldElemOf x xs (P x)) → (∀ x, SetUnfoldElemOf b (f x) (Q x)) →
    SetUnfoldElemOf b (gset_bind f xs) (∃ x, P x ∧ Q x).
  Proof. constructor. rewrite elem_of_gset_bind. set_solver. Qed.

  Lemma gset_bind_union f xs1 xs2 :
    gset_bind f (xs1 ∪ xs2) =
    gset_bind f xs1 ∪ gset_bind f xs2.
  Proof. set_solver. Qed.

  Lemma gset_bind_singleton f a :
    gset_bind f {[ a ]} = f a.
  Proof. set_solver. Qed.
End gset_bind.

Section lookup_insert.

  Lemma lookup_insert_iff `{Countable K, A} (m : gmap K A) k k' a :
    <[ k := a ]> m !! k' = if bool_decide (k = k') then Some a else m !! k'.
  Proof. by case: bool_decide_reflect => [<-|?]; rewrite (lookup_insert, lookup_insert_ne). Qed.

End lookup_insert.

Lemma gmap_dom_empty {K V} `{Countable K} {m : gmap K V} :
  dom m = dom (empty (A := gmap K V)) -> m = ∅.
Proof. rewrite dom_empty_L. apply dom_empty_inv_L. Qed.

Lemma gmap_dom_insert {K V} `{Countable K} {k v} {m1 m2 : gmap K V}
  (Hm1 : m1 !! k = Some v)
  (Hm2 : m2 !! k = None)
  (Hdom : dom m1 = {[k]} ∪ dom m2) :
  ∃ m1', m1 = <[k := v]> m1' ∧ m1' !! k = None ∧ dom m1' = dom m2.
Proof.
  exists (delete k m1).
  have Hm1' : delete k m1 !! k = None by exact: lookup_delete.
  have Heq : m1 = <[k:=v]> (delete k m1) by rewrite insert_delete_insert insert_id.
  rewrite Heq dom_insert_L in Hdom. split_and! => // {Hm1 Heq}.
  move: m1 (delete _ _) Hm1' Hm2 Hdom => _ m1.
  move=>/not_elem_of_dom Hm1 /not_elem_of_dom Hm2.
  rewrite !set_eq.
  (* [set_solver] Works, but I found the faster manual proof first. *)
  move=> + k' => /(_ k').
  rewrite !elem_of_union elem_of_singleton.
  naive_solver.
Qed.

Lemma gmap_dom_insert' {K V} `{Countable K} (m1 : gmap K V) {k} {m2 : gmap K V}
  (Hm2 : m2 !! k = None)
  (Hdom : dom m1 = {[k]} ∪ dom m2) :
  ∃ v (m1' : gmap K V), m1 !! k = Some v ∧ m1 = <[k := v]> m1' ∧
    m1' !! k = None ∧ dom m1' = dom m2.
Proof.
  destruct (m1 !! k) as [v|] eqn:Hm1.
  { destruct (gmap_dom_insert Hm1 Hm2 Hdom) as [m1']. exists v, m1'. intuition. }
  exfalso. move: Hm1 => /not_elem_of_dom.
  set_solver.
Qed.
