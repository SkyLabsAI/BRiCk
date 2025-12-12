(*
 * Copyright (c) 2022 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(*
 * Some of the following code is derived from code original to the
 * stdpp project. That original code is
 *
 *	Copyright stdpp developers and contributors
 *
 * and used according to the following license.
 *
 *	SPDX-License-Identifier: BSD-3-Clause
 *
 * Original stdpp License:
 * https://gitlab.mpi-sws.org/iris/stdpp/-/blob/54252fbc10eaa88941ec1e157ce2c2e575e42604/LICENSE
 *)

Require Export stdpp.fin_maps.
Require Import bluerock.prelude.base.
Require Import bluerock.prelude.list_numbers.

(* TODO upstream to stdpp. *)
Section fin_maps.
  Context `{FinMap K M} {A : Type}.
  Implicit Type (m : M A).
  #[local] Set Default Proof Using "Type*".

  Lemma map_positive m1 m2 : m1 ∪ m2 = ∅ → m1 = ∅ ∧ m2 = ∅.
  Proof.
    intros Heq. pose proof map_positive_l _ _ Heq as ->.
    by rewrite ->left_id_L in Heq by apply _.
  Qed.

  Lemma map_positive_r m1 m2 : m1 ∪ m2 = ∅ → m2 = ∅.
  Proof. by intros [_ ?]%map_positive. Qed.

  (* Remaining lemmas use ssreflect.
  TODO: avoid if upstreaming to stdpp. *)
  Lemma map_union_difference (m1 m2 : M A) :
    (m1 ∪ m2) ∖ m1 = m2 ∖ m1.
  Proof.
    apply map_eq => i. apply option_eq => a.
    rewrite !lookup_difference_Some lookup_union_Some_raw.
    intuition congruence.
  Qed.

  Lemma map_difference_union_distr_l m1 m2 m3 : (m1 ∪ m2) ∖ m3 = m1 ∖ m3 ∪ m2 ∖ m3.
  Proof.
    apply map_eq => i. apply option_eq => a.
    rewrite !(lookup_difference_Some, lookup_difference_None, lookup_union_Some_raw).
    intuition try congruence; unfold is_Some in *; naive_solver.
  Qed.

  Lemma difference_map_disjoint (m1 m2 : M A) :
    m1 ##ₘ m2 → m2 ∖ m1 = m2.
  Proof.
    intros Hdisj. apply map_eq => i. apply option_eq => a.
    rewrite !lookup_difference_Some.
    intuition eauto using map_disjoint_Some_l.
  Qed.

  Lemma map_difference_union_distr_disj_l m1 m2 m3 :
    m1 ##ₘ m3 ->
    (m1 ∪ m2) ∖ m3 = m1 ∪ (m2 ∖ m3).
  Proof. intros. by rewrite map_difference_union_distr_l difference_map_disjoint. Qed.

  Lemma map_difference_insert_ne i j x y m (Hne : i ≠ j) :
    <[i:=x]> m ∖ {[j := y]} =
    <[i:=x]> (m ∖ {[j := y]}).
  Proof.
    rewrite !insert_union_singleton_l map_difference_union_distr_disj_l //.
    rewrite map_disjoint_singleton_l. exact: lookup_singleton_ne.
  Qed.

  Lemma map_insert_difference (m : M A) i x :
    <[i:=x]> m ∖ {[ i := x ]} = m ∖ {[ i := x ]}.
  Proof. by rewrite insert_union_singleton_l map_union_difference. Qed.

  Lemma map_fmap_difference {B} (f : A -> B) m a (i : K) :
    f <$> (m ∖ {[i := a]}) = (f <$> m) ∖ {[i := f a]}.
  Proof.
    rewrite !map_difference_filter map_filter_fmap /=. f_equiv.
    apply map_filter_ext => j r /= _.
    by rewrite !lookup_singleton_None.
  Qed.

  Lemma map_Forall_fmap {B} (m : M A) (f : A -> B) P :
    map_Forall (λ k _, P k) (f <$> m) <-> map_Forall (λ k _, P k) m.
  Proof.
    rewrite /map_Forall; setoid_rewrite lookup_fmap.
    split; intros Hin i d Hs. { eapply Hin. by rewrite Hs. }
    specialize (Hin i). destruct (m !! i); naive_solver.
  Qed.
End fin_maps.

Section list.
  (* Note: the RHS uses [map_lookup_total] *)
  Lemma list_lookup_total_nat_N `{Inhabited A} (xs : list A) (i : N) :
    xs !!! N.to_nat i = xs !!! i.
  Proof. by rewrite !lookup_total_alt list_lookup_total_alt. Qed.

  Lemma list_lookupN_total_fmap
    `{Inhabited A} `{Inhabited B}
    (f : A → B) (xs : list A) (i : N)
    (Hin : (i < lengthN xs)%N) :
    (f <$> xs) !!! i = f (xs !!! i).
  Proof.
    rewrite -!list_lookup_total_nat_N list_lookup_total_fmap //.
    rewrite /lengthN in Hin; lia.
  Qed.
End list.
