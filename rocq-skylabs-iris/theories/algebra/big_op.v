(*
 * Copyright (C) 2021-2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Export iris.algebra.big_op.
Require Export bluerock.iris.extra.algebra.monoid.

Require Import bluerock.prelude.numbers.
Require Import bluerock.prelude.list_numbers.
Require Import bluerock.prelude.fin_sets.

(** * Big ops *)

(** ** [set_seq] *)
Section set_seq.
  Lemma big_opS_set_seq `{Monoid M o} (f : nat -> M) start count :
    ([^o set] n ∈ set_seq start count, f n) ≡
    ([^o list] n ∈ seq start count, f n).
  Proof.
    rewrite big_op.big_opS_unseal /big_op.big_opS_def. by rewrite elements_set_seq.
  Qed.
End set_seq.

(** ** Powers and big ops *)
(**
Relate powers to big op encodings. The assertion [P ^^ n], for
example, is equivalent to [[** list] _ ∈ seqN 0 n, P].
*)

Section big_op.
  Import monoid_instances.
  Context `{Monoid M o}.
  #[local] Infix "`o`" := o (at level 50, left associativity).
  #[local] Arguments N.of_nat : simpl never.

  Lemma big_opL_gen_power (R : relation M) {A} (l : list A) (x : M) :
    Reflexive R ->
    Proper (R ==> R ==> R) o ->
    R ([^o list] _ ∈ l, x) (x ^^{o} N.of_nat (length l)).
  Proof.
    intros ? Hop. induction l; first done.
    cbn. rewrite Nat2N.inj_succ power_succ. by apply Hop.
  Qed.

  Lemma big_opL_power {A} (l : list A) (x : M) :
    ([^o list] _ ∈ l, x) ≡ x ^^{o} lengthN l.
  Proof. apply: big_opL_gen_power. Qed.

  Lemma big_opM_gen_power (R : relation M) `{Countable K} {A} (m : gmap K A) (x : M) :
    subrelation (≡) R -> PreOrder R ->
    Proper (R ==> R ==> R) o ->
    R ([^o map] _ ∈ m, x) (x ^^{o} N.of_nat (size m)).
  Proof.
    intros HR ? Hop. induction m as [|i a m Hi IH] using map_ind.
    { by rewrite big_opM_empty map_size_empty. }
    etrans; first by apply HR; rewrite big_opM_insert.
    rewrite map_size_insert_None // Nat2N.inj_succ power_succ. exact: Hop.
  Qed.

  Lemma big_opM_power `{Countable K} {A} (m : gmap K A) (x : M) :
    ([^o map] _ ∈ m, x) ≡ x ^^{o} N.of_nat (size m).
  Proof. exact: big_opM_gen_power. Qed.

  Lemma big_opS_gen_power (R : relation M) `{Countable A} (X : gset A) (x : M) :
    Reflexive R ->
    Proper (R ==> R ==> R) o ->
    R ([^o set] _ ∈ X, x) (x ^^{o} N.of_nat (size X)).
  Proof. rewrite big_op.big_opS_unseal. exact: big_opL_gen_power. Qed.

  Lemma big_opS_power `{Countable A} (X : gset A) (x : M) :
    ([^o set] _ ∈ X, x) ≡ x ^^{o} N.of_nat (size X).
  Proof. exact: big_opS_gen_power. Qed.

  Lemma big_opMS_gen_power (R : relation M) `{Countable A} (X : gmultiset A) (x : M) :
    Reflexive R ->
    Proper (R ==> R ==> R) o ->
    R ([^o mset] _ ∈ X, x) (x ^^{o} N.of_nat (size X)).
  Proof. rewrite big_op.big_opMS_unseal. exact: big_opL_gen_power. Qed.

  Lemma big_opMS_power `{Countable A} (X : gmultiset A) (x : M) :
    ([^o mset] _ ∈ X, x) ≡ x ^^{o} N.of_nat (size X).
  Proof. exact: big_opMS_gen_power. Qed.

  (** Example: We can easily relate various encodings of powers. *)

  Goal ∀ {A} `{Countable A} (m : M) (X : gset A),
    ([^o set] _ ∈ X, m) ≡
    ([^o list] _ ∈ seq 0 (size X), m).
  Proof.
    intros. by rewrite big_opS_power big_opL_power /lengthN length_seq.
  Qed.

End big_op.

Section map_seqZ.
  #[local] Open Scope Z_scope.

  Lemma big_sepM_map_seqZ `{Monoid A o} {B} (xs : list B) i f :
    ([^o map] k ↦ x ∈ map_seqZ i xs, f k x) ≡ [^o list] k ↦ x ∈ xs, f (i + Z.of_nat k) x.
  Proof.
    elim/rev_ind: xs i => [|x xs IH] i.
    - by rewrite /= big_opM_empty.
    -
      rewrite map_seqZ_snoc big_opL_snoc monoid_comm big_opM_insert.
      + by apply monoid_proper, IH.
      + apply map_seqZ_snoc_disjoint.
  Qed.

  Lemma big_sepM_map_seqZ0 `{Monoid A o} {B} (xs : list B) f :
    ([^o list] k ↦ x ∈ xs, f k x) ≡ ([^o map] k ↦ x ∈ map_seqZ 0 xs, f (Z.to_nat k) x).
  Proof.
    rewrite big_sepM_map_seqZ; f_equiv => i x.
    by rewrite Z.add_0_l Nat2Z.id.
  Qed.

End map_seqZ.

(** ** Powers encoded as big ops *)
(**
The following are intended to ease reasoning about various encodings
of powers.
*)

Section encodings.
  Context `{Monoid M o}.

  (** Powers encoded with [seqN] *)

  Lemma big_opL_seqN_power x n : ([^o list] _ ∈ seqN 0 n, x) ≡ x ^^{o} n.
  Proof. by rewrite big_opL_power seqN_lengthN. Qed.

  (** Powers encoded with [seq] *)

  Lemma big_opL_seq_power x n : ([^o list] _ ∈ seq 0 n, x) ≡ x ^^{o} N.of_nat n.
  Proof. by rewrite big_opL_power /lengthN length_seq. Qed.

  (** Powers encoded with [set_seq] *)

  Lemma big_opS_set_seq_power x n : ([^o set] _ ∈ set_seq 0 n, x) ≡ x ^^{o} N.of_nat n.
  Proof. by rewrite big_opS_set_seq big_opL_seq_power. Qed.

End encodings.
