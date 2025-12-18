(*
 * Copyright (c) 2020-2022 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import skylabs.prelude.zip_with_index.
Require Import skylabs.prelude.zip_with_indexN.

Require Export skylabs.iris.extra.algebra.big_op.
Require Export iris.bi.big_op.

Require Import skylabs.iris.extra.bi.prelude.
Require Import skylabs.iris.extra.bi.observe.
Require Import skylabs.iris.extra.proofmode.proofmode.
Import ChargeNotation.

(** ** Lists *)

Section big_op.
  Context `{Monoid M o}.
  Implicit Types P : M → Prop.
  Infix "`o`" := o (at level 50, left associativity).

  Section list.
    Context {A : Type}.
    Implicit Types xs : list A.
    Implicit Types f : nat → A → M.

    (** Any [P] compatible with the monoid and with [f] is compatible
        with [big_opL o f] *)
    Lemma big_opL_gen (P : M → Prop) f xs :
      P monoid_unit → (∀ x y, P x → P y → P (x `o` y)) →
      (∀ k x, xs !! k = Some x → P (f k x)) →
      P ([^o list] k↦x ∈ xs, f k x).
    Proof.
      intros ? Hop. elim: xs f => [ |x xs IH] f /= Hf; first done.
      apply Hop; first by apply Hf. apply IH=>k y Hk. by apply Hf.
    Qed.
  End list.
End big_op.

Section big_andL.
  Context {PROP : bi} {A : Type}.

  Lemma big_andL_frame (xs : list A) (Q Q' : nat → A → PROP) :
    (∀ i v, Q i v -* Q' i v) ⊢
    ([∧list] i ↦ x ∈ xs, Q i x) -∗ ([∧list] i ↦ x ∈ xs, Q' i x).
  Proof.
    iIntros "W L". iInduction xs as [|x xs] "IH" forall (Q Q'); simpl; first done.
    iApply (bi.and_parallel with "L"); iSplit; first by eauto.
    iApply "IH". iIntros (??). by iApply "W".
  Qed.

  Lemma bupd_big_andL `{BiBUpd PROP} (xs : list A) (P : nat → A → PROP) :
    (|==> [∧ list] i ↦ x ∈ xs, P i x) ⊢
    [∧ list] i ↦ x ∈ xs, |==> P i x.
  Proof.
    iIntros "Q". iInduction xs as [|x xs] "IH" forall (P); simpl; first done.
    rewrite bupd_and; iApply (bi.and_parallel with "Q"); eauto.
  Qed.

  Lemma fupd_big_andL `{BiFUpd PROP} {E1 E2} (xs : list A) (P : nat → A → PROP) :
    (|={E1, E2}=> [∧ list] i ↦ x ∈ xs, P i x) ⊢
    [∧ list] i ↦ x ∈ xs, |={E1, E2}=> P i x.
  Proof.
    iIntros "Q". iInduction xs as [|x xs] "IH" forall (P); simpl; first done.
    rewrite fupd_and; iApply (bi.and_parallel with "Q"); eauto.
  Qed.
End big_andL.

Section big_sepL.
  Context {PROP : bi} {A : Type}.
  Implicit Types xs : list A.
  Implicit Types f : nat → A → PROP.

  (** In contrast with [big_sepL_ne], the lists need not be equal. *)
  Lemma big_sepL_gen_ne {B} f g (l1 : list A) (l2 : list B) n :
    length l1 = length l2 →
    (∀ k y1 y2, l1 !! k = Some y1 → l2 !! k = Some y2 → f k y1 ≡{n}≡ g k y2) →
    ([∗ list] k↦y ∈ l1, f k y)%I ≡{n}≡ ([∗ list] k↦y ∈ l2, g k y)%I.
  Proof.
    intros ? Hf. apply big_opL_gen_proper_2; [done|by apply _| ].
    move=>k. destruct (l1 !! k) eqn:Hl1, (l2 !! k) eqn:Hl2.
    - exact: Hf.
    - apply lookup_lt_Some in Hl1. apply lookup_ge_None_1 in Hl2. lia.
    - apply lookup_ge_None_1 in Hl1. apply lookup_lt_Some in Hl2. lia.
    - done.
  Qed.

  (** In contrast with [big_sepL_proper], the lists need not be equal. *)
  Lemma big_sepL_gen_proper {B} f g (l1 : list A) (l2 : list B) :
    length l1 = length l2 →
    (∀ k y1 y2, l1 !! k = Some y1 → l2 !! k = Some y2 → f k y1 ≡ g k y2) →
    ([∗ list] k↦y ∈ l1, f k y) ⊣⊢ [∗ list] k↦y ∈ l2, g k y.
  Proof.
    intros ? Hf. apply big_opL_gen_proper_2; [done|by apply _| ].
    move=>k. destruct (l1 !! k) eqn:Hl1, (l2 !! k) eqn:Hl2.
    - exact: Hf.
    - apply lookup_lt_Some in Hl1. apply lookup_ge_None_1 in Hl2. lia.
    - apply lookup_ge_None_1 in Hl1. apply lookup_lt_Some in Hl2. lia.
    - done.
  Qed.

  (** In contrast with [big_sepL_mono], the lists need not be equal. *)
  Lemma big_sepL_gen_mono {B} f g (l1 : list A) (l2 : list B) :
    length l1 = length l2 →
    (∀ k y1 y2, l1 !! k = Some y1 → l2 !! k = Some y2 → f k y1 |-- g k y2) →
    ([∗ list] k↦y ∈ l1, f k y) ⊢ [∗ list] k↦y ∈ l2, g k y.
  Proof.
    intros ? Hf. apply big_opL_gen_proper_2; [done|by apply _| ].
    move=>k. destruct (l1 !! k) eqn:Hl1, (l2 !! k) eqn:Hl2.
    - exact: Hf.
    - apply lookup_lt_Some in Hl1. apply lookup_ge_None_1 in Hl2. lia.
    - apply lookup_ge_None_1 in Hl1. apply lookup_lt_Some in Hl2. lia.
    - done.
  Qed.

  (** Unlike [big_sepL_delete] and [big_sepL_delete'], this one uses [delete],
  but is restricted to comprehensions that do not use the list index.
  Unlike [big_sepL_difference_singleton], this works on lists with duplicates.
  TODO: This name would make more sense if the upstream lemmas were renamed, say,
  into [big_sepL_delete_{if,ne}].
  *)
  Lemma big_sepL_delete_delete xs i x (f : A → PROP)
    (Hl : xs !! i = Some x) :
    ([∗ list] k ∈ xs, f k) ⊣⊢ f x ∗ [∗ list] k ∈ delete i xs, f k.
  Proof.
    rewrite big_sepL_delete; last exact: Hl. f_equiv.
    elim: xs i Hl => [//|x' xs IHxs] [|i] /= Hl. {
      rewrite left_id. by apply big_sepL_proper.
    }
    f_equiv. rewrite -(IHxs i Hl). apply big_sepL_proper => k y Hl'.
    rewrite (decide_ext (S k = S i) (k = i)) //. lia.
  Qed.

  (** In contrast with [big_sepL_timeless], [big_sepL_persistent], and
      [big_sepL_affine], the following offer [xs !! k = Some x] in
      their premisses. *)
  Lemma big_sepL_gen_timeless `{!Timeless (emp%I : PROP)} f xs :
    (∀ k x, xs !! k = Some x → Timeless (f k x)) →
    Timeless ([∗ list] k↦x ∈ xs, f k x).
  Proof. apply big_opL_gen; apply _. Qed.
  Lemma big_sepL_gen_persistent f xs :
    (∀ k x, xs !! k = Some x → Persistent (f k x)) →
    Persistent ([∗ list] k↦x ∈ xs, f k x).
  Proof. apply big_opL_gen; apply _. Qed.
  Lemma big_sepL_gen_affine f xs :
    (∀ k x, xs !! k = Some x → Affine (f k x)) →
    Affine ([∗ list] k↦x ∈ xs, f k x).
  Proof. apply big_opL_gen; apply _. Qed.

  Lemma big_sepL_hd `{Inhabited A} f xs :
    xs <> [] ->
    ([∗ list] k↦x ∈ xs, f k x) ⊢ f 0 (hd inhabitant xs) ** True.
  Proof. case: xs => [//|x xs] _ /=. iIntros "[$ $]". Qed.

  Lemma bi_opL_sep_forall (P : A -> PROP) xs
    `{!Persistent1 P} `{!Affine1 P} :
    ([∗ list] x ∈ xs, P x) ⊣⊢ □ ∀ x, [| x ∈ xs |] -∗ P x.
  Proof.
    elim: xs => [//= |x xs /= -> ]. {
      iSplit; last by iIntros.
      iIntros "_ !>" (x []%elem_of_nil).
    }
    iSplit. {
      iIntros "[#P #W] !>" (? [->|?]%elem_of_cons);
        [ iApply "P" | by iApply "W"].
    }
    iIntros "#W". iSplitL; last iIntros "!>" (??).
    all: iApply ("W" with "[%]"); set_solver.
  Qed.

  Lemma bi_opL_sep_and (P : A -> PROP) xs
    `{BiAffine PROP} `{!Persistent1 P} :
    ([∗ list] x ∈ xs, P x) ⊣⊢ [∧list] x ∈ xs, P x.
  Proof.
    elim: xs => [//= |x xs /= -> ]. { by rewrite bi.True_emp. }
    iSplit; iIntros. { by rewrite bi.sep_and. }
    by rewrite bi.persistent_and_sep_1.
  Qed.
End big_sepL.

Lemma big_sepL_mono_elem {PROP : bi} {A : Type} (Φ Ψ : A → PROP) (l : list A):
  (∀ (y : A), y ∈ l -> Φ y ⊢ Ψ y)
  → ([∗ list] y ∈ l, Φ y) ⊢ ([∗ list] y ∈ l, Ψ y).
Proof.
  intros Hin. apply big_sepL_mono => k y Hl. eapply Hin, elem_of_list_lookup_2, Hl.
Qed.

Lemma big_sepL_difference_singleton {PROP : bi} `{EqDecision A} (x : A)
    (f : A -> PROP) (l : list A) :
  x ∈ l ->
  NoDup l ->
  ([∗ list] i ∈ l, f i) ⊣⊢ f x ∗ [∗ list] i ∈ list_difference l [x], f i.
Proof.
  intros [j Hl]%elem_of_list_lookup_1 HnoDup.
  by rewrite big_sepL_delete_delete // (list_difference_delete j).
Qed.

Lemma big_sepL_difference_two {PROP : bi} {A} `{EqDecision A} (f : A -> PROP) l x y:
  x <> y ->
  x ∈ l ->
  y ∈ l ->
  NoDup l -> (* we only need x to be not duplicated *)
  ([∗ list] i ∈ l, f i) ⊣⊢ f x ∗ f y ∗ [∗ list] i ∈ list_difference l [x; y], f i.
Proof.
  intros Hneq H1l H2l Hnd.
  rewrite (big_sepL_difference_singleton x) //.
  rewrite (big_sepL_difference_singleton y); [| set_solver | exact: NoDup_list_difference].
  by rewrite (list_difference_app_r l [x] [y]).
Qed.

(* This adjusts the initial index, but we pass the same arguments to [P] *)
Lemma big_sepL_seqN_shift {PROP : bi} (P : N -> PROP) (j : N) {n m : N} :
  (j <= n)%N ->
  ([∗list] i ∈ seqN n m, P i) ⊣⊢ [∗list] i ∈ seqN j m, P (n - j + i)%N.
Proof.
  intros Le.
  rewrite -[in seqN n m](N.sub_add _ _ Le) -fmap_add_seqN.
  apply big_sepL_fmap.
Qed.

Lemma big_sepL_seq_shift {PROP : bi} (P : nat -> PROP) (j : nat) {n m : nat} :
  j <= n ->
  ([∗list] i ∈ seq n m, P i) ⊣⊢ [∗list] i ∈ seq j m, P (n - j + i).
Proof.
  intros Le.
  rewrite -[in seq n m](Nat.sub_add _ _ Le) -fmap_add_seq.
  apply big_sepL_fmap.
Qed.

Lemma big_sepM_lookup_acc' {PROP : bi} `{Countable K} {A}
    (Φ : K -> A -> PROP) (m : gmap K A) (i : K) (x : A) :
  m !! i = Some x →
  ([∗ map] k↦y ∈ m, Φ k y)
  ⊢ Φ i x ∗ (Forall x', (Φ i x' -∗ ([∗ map] k↦y ∈ <[i:=x']> m, Φ k y))).
Proof.
  intros.
  rewrite big_sepM_delete=> //. apply bi.sep_mono_r.
  iIntros "map_without" (x') "Phi'".
  rewrite big_sepM_insert_delete.
  by iFrame.
Qed.

Lemma big_sepM2_lookup_acc' {PROP : bi} `{EqDecision K} `{Countable K} {A B}
    (Φ : K -> A -> B -> PROP) (m1 : gmap K A) (m2 : gmap K B) (i : K) (x : A) :
  m1 !! i = Some x →
  ([∗ map] k↦y;z ∈ m1;m2, Φ k y z)
  ⊢ (∃ y, ([| m2 !! i = Some y |] ∗ Φ i x y))
  ∗ (∀ x' y',
      (Φ i x' y' -∗ ([∗ map] k↦x;y ∈ <[i:=x']> m1; <[i:=y']> m2, Φ k x y))).
Proof.
  intros.
  rewrite big_sepM2_delete_l=> //.
  iIntros "(% & % & Ha & Hb)".
  iSplitL "Ha".
  - iExists _; by iFrame.
  - iIntros (x' y') "HΦ".
    rewrite big_sepM2_insert_delete; iFrame.
Qed.

(** ** Powers in BIs *)
(**
Overview:

- Notation [P ^^ n := P ^^{bi_sep} n]

- Monotonicity, timelessness, etc of the assertion [P ^^{o} n] for [o
∈ bi_sep, bi_and, bi_or]
*)

Notation "P ^^ n" := (P ^^{bi_sep} n) : bi_scope.

Section power.
  Context {PROP : bi}.
  Implicit Types (P : PROP).
  #[local] Notation "(⊢)" := (⊢@{PROP}) (only parsing).
  #[local] Open Scope N_scope.

  #[local] Notation MONO R op :=
    (Proper (R%signature ==> eq ==> R) (power op)) (only parsing).

  #[global] Instance power_sep_mono : MONO (⊢) bi_sep.
  Proof. apply: power_proper. Qed.
  #[global] Instance power_and_mono : MONO (⊢) bi_and.
  Proof. apply: power_proper. Qed.
  #[global] Instance power_or_mono : MONO (⊢) bi_or.
  Proof. apply: power_proper. Qed.

  #[global] Instance power_sep_flip_mono : MONO (flip (⊢)) bi_sep.
  Proof. apply: power_proper. Qed.
  #[global] Instance power_and_flip_mono : MONO (flip (⊢)) bi_and.
  Proof. apply: power_proper. Qed.
  #[global] Instance power_or_flip_mono : MONO (flip (⊢)) bi_or.
  Proof. apply: power_proper. Qed.

  (**
   * Avoid exotic goals like [Timeless emp], [Affine True] when [n] a
   * non-zero constructor.
   *)
  #[local] Lemma power_closed' `{Monoid M o} (P : M -> Prop) x n :
    TCOr (NNonZero n) (P monoid_unit) ->
    Proper (equiv ==> iff) P ->
    (∀ x1 x2, P x1 -> P x2 -> P (o x1 x2)) ->
    P x -> P (x ^^{o} n).
  Proof.
    destruct 1; intros. exact: power_closed_nonzero. exact: power_closed.
  Qed.

  #[local] Notation CLOSED R o :=
    (∀ (P : PROP) n, R P -> R (P ^^{o} n)) (only parsing).
  #[local] Notation CLOSED' R u o :=
    (∀ P n, TCOr (NNonZero n) (R (u : PROP)) -> R P -> R (P ^^{o} n)) (only parsing).

  #[global] Instance power_sep_timeless : CLOSED' Timeless emp bi_sep.
  Proof. intros. apply: power_closed'. Qed.
  #[global] Instance power_and_timeless : CLOSED Timeless bi_and.
  Proof. intros. apply: power_closed. Qed.
  #[global] Instance power_or_timeless : CLOSED Timeless bi_or.
  Proof. intros. apply: power_closed. Qed.

  #[global] Instance power_sep_persistent : CLOSED Persistent bi_sep.
  Proof. intros. apply: power_closed. Qed.
  #[global] Instance power_and_persistent : CLOSED Persistent bi_and.
  Proof. intros. apply: power_closed. Qed.
  #[global] Instance power_or_persistent : CLOSED Persistent bi_or.
  Proof. intros. apply: power_closed. Qed.

  #[global] Instance power_sep_affine : CLOSED Affine bi_sep.
  Proof. intros. apply: power_closed. Qed.
  #[global] Instance power_and_affine : CLOSED' Affine True%I bi_and.
  Proof. intros. apply: power_closed'. Qed.
  #[global] Instance power_or_affine : CLOSED Affine bi_or.
  Proof. intros. apply: power_closed. Qed.

  Lemma power_sep_emp n : emp ⊣⊢@{PROP} emp ^^ n.
  Proof. by rewrite power_unit. Qed.
End power.

Section zip_with_index.
  Context {A : Type}.
  Context {PROP : bi}.

  Implicit Types (x : A) (xs : list A) (i j : nat).

  Section big_sepL.
    Implicit Type (f : nat → A → PROP).

    Lemma big_sepL_zip_with_index_from j xs f :
      ([∗ list] k ↦ x ∈ xs, f (k + j) x) ⊣⊢ [∗ list] kx ∈ zip_with_index_from j xs, f kx.1 kx.2.
    Proof.
      elim: xs j => [|x xs IHxs] j //=. f_equiv. rewrite -(IHxs (S j)).
      apply big_sepL_proper => k y _. by rewrite Nat.add_succ_r.
    Qed.

    Lemma big_sepL_zip_with_index xs f :
      ([∗ list] k ↦ x ∈ xs, f k x) ⊣⊢ [∗ list] kx ∈ zip_with_index xs, f kx.1 kx.2.
    Proof.
      rewrite -big_sepL_zip_with_index_from. apply big_sepL_proper => k y _. by rewrite right_id_L.
    Qed.
  End big_sepL.

  Section big_sepL_sepM.
    Implicit Type (f : nat * A → PROP).

    Lemma big_sepL_sepM_zip_with_index_from j xs f :
      ([∗ list] kx ∈ zip_with_index_from j xs, f kx) ⊣⊢
      ([∗ map] k ↦ x ∈ list_to_map (M := gmap nat A) (zip_with_index_from j xs), f (k, x)).
    Proof.
      elim: xs j => [|x xs IHxs] j /=. by rewrite big_sepM_empty.
      rewrite /= big_sepM_insert ? {}IHxs //. apply not_elem_of_list_to_map_1.
      rewrite fst_zip ?length_seq //. set_solver by lia.
    Qed.

    Lemma big_sepL_sepM_zip_with_index xs f :
      ([∗ list] kx ∈ zip_with_index xs, f kx) ⊣⊢
      ([∗ map] k ↦ x ∈ list_to_map (zip_with_index xs), f (k, x)).
    Proof. apply big_sepL_sepM_zip_with_index_from. Qed.
  End big_sepL_sepM.
End zip_with_index.

Section zip_with_indexN_from.
  #[local] Open Scope N_scope.
  Context {A : Type}.
  Context {PROP : bi}.
  Implicit Types (x : A) (xs : list A) (i j : N).

  Section big_sepL.
    Lemma big_sepL_zip_with_indexN xs (f : nat → A → PROP) :
      ([∗ list] k ↦ x ∈ xs, f k x) ⊣⊢ [∗ list] kx ∈ zip_with_indexN xs, f (N.to_nat kx.1) kx.2.
    Proof.
      apply big_sepL_gen_proper. by rewrite length_zip_with_indexN.
      move => k a1 [k2 a2] /=.
      rewrite !list_lookup_lookupN lookupN_zip_with_indexN => ? -[<- ?]; simplify_eq.
      by rewrite left_id_L !Nat2N.id.
    Qed.
  End big_sepL.

  Section big_sepL_sepM.
    Implicit Type (f : N * A → PROP).

    Lemma big_sepL_sepM_zip_with_indexN_from xs j f :
      ([∗ list] kx ∈ zip_with_indexN_from j xs, f kx) ⊣⊢
      [∗ map] k ↦ x ∈ list_to_map (M := gmap N A) (zip_with_indexN_from j xs), f (k, x).
    Proof.
      elim: xs j => [|x xs IHxs] j /=. by rewrite big_sepM_empty.
      rewrite zip_with_indexN_from_cons /= big_sepM_insert ? {}IHxs //. apply not_elem_of_list_to_map_1.
      rewrite fst_zip. set_solver by lia.
      rewrite length_lengthN seqN_lengthN -length_lengthN //.
    Qed.

    Lemma big_sepL_sepM_zip_with_indexN xs f :
      ([∗ list] kx ∈ zip_with_indexN xs, f kx) ⊣⊢
      [∗ map] k ↦ x ∈ list_to_map (M := gmap N A) (zip_with_indexN xs), f (k, x).
    Proof. apply big_sepL_sepM_zip_with_indexN_from. Qed.
  End big_sepL_sepM.
End zip_with_indexN_from.
