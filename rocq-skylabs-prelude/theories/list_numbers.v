(*
 * Copyright (C) 2022-2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.prelude.base.
Require Export skylabs.prelude.list.
Require Export skylabs.prelude.numbers.
Require skylabs.prelude.under_rel_proper.

#[global] Instance set_unfold_elem_of_seq (n start len : nat) P :
  SetUnfold (start ≤ n < start + len)%nat P →
  SetUnfoldElemOf n (seq start len) P.
Proof. constructor. rewrite elem_of_seq. set_solver. Qed.

Lemma insert_seq (i j k : nat) :
  <[ k := i + k ]> (seq i j) = seq i j.
Proof.
  destruct (decide (k < j)).
  by rewrite list_insert_id // lookup_seq_lt.
  by rewrite list_insert_ge // length_seq; lia.
Qed.

Lemma fmap_add_seq_0 j n :
  Nat.add j <$> seq 0 n = seq j n.
Proof. by rewrite fmap_add_seq Nat.add_0_r. Qed.

#[local] Open Scope N_scope.

Definition seqN (from count : N) : list N :=
  N.of_nat <$> seq (N.to_nat from) (N.to_nat count).
#[global] Arguments seqN : simpl never.

Definition replicateN {A} (count : N) (x : A) : list A :=
  replicate (N.to_nat count) x.
#[global] Arguments replicateN : simpl never.
#[deprecated(since="2021-05-26",note="use [replicateN].")]
Notation repeatN := (flip replicateN) (only parsing).

Definition dropN {A} n := drop (A := A) (N.to_nat n).
Definition takeN {A} n := take (A := A) (N.to_nat n).
Definition lengthN {A} xs := N.of_nat (length (A := A) xs).
Definition resizeN {A} n := resize (A := A) (N.to_nat n).
Definition rotateN {A} n xs :=
  dropN (A := A) (n mod lengthN xs) xs ++ takeN (A := A) (n mod lengthN xs) xs.

#[global] Instance list_lookupN {A}: Lookup N A (list A) | 10 :=
  fun i xs => lookup (N.to_nat i) xs.
#[global] Notation lookupN := (lookup (K := N)) (only parsing).

(** Instead of lifting the [list_lookup] theory to [list_lookupN] we provide an unfolding lemma. *)
Lemma list_lookupN_lookup {A} (xs : list A) (n : N) :
  xs !! n = xs !! N.to_nat n.
Proof. done. Qed.
(** Folding lemma. *)
Lemma list_lookup_lookupN {A} (xs : list A) (n : nat) :
  xs !! n = xs !! N.of_nat n.
Proof. by rewrite list_lookupN_lookup Nat2N.id. Qed.

#[global] Instance list_insertN {A} : Insert N A (list A) | 10 :=
  fun i x xs => <[N.to_nat i := x]> xs.
#[global] Notation insertN := (insert (K := N)) (only parsing).

(* Instead of lifting the [list_insert] theory to [list_insertN] we provide an unfolding lemma. *)
Lemma list_insertN_insert {A} (i : N) (x : A) (xs : list A) :
  <[i := x]> xs = <[N.to_nat i := x]> xs.
Proof. done. Qed.
(** Folding lemma. *)
Lemma list_insert_insertN {A} (i : nat) (x : A) (xs : list A) :
  <[i := x]> xs = <[N.of_nat i := x]> xs.
Proof. by rewrite list_insertN_insert Nat2N.id. Qed.

#[global] Instance list_alterN {A} : Alter N A (list A) | 10 :=
  fun f i xs => alter f (N.to_nat i) xs.
#[global] Notation alterN := (alter (K := N)) (only parsing).

(* Instead of lifting the [list_alter] theory to [list_alterN] we provide an unfolding lemma. *)
Lemma list_alterN_alter {A} (i : N) (xs : list A) f :
  alter f i xs = alter f (N.to_nat i) xs.
Proof. done. Qed.

(** Folding lemma. *)
Lemma list_alter_alterN {A} (i : nat) (xs : list A) f :
  alter f i xs = alter f (N.of_nat i) xs.
Proof. by rewrite list_alterN_alter Nat2N.id. Qed.

Lemma fmap_lengthN {A B} (f : A → B) (l : list A) :
  lengthN (f <$> l) = lengthN l.
Proof. by rewrite /lengthN length_fmap. Qed.

Lemma list_lookupN_fmap {A B} (f : A -> B) (l : list A) (i : N) :
  (f <$> l) !! i = f <$> (l !! i).
Proof. by rewrite -list_lookup_fmap. Qed.

Lemma list_ne_lengthN {A} (xs : list A) : lengthN xs ≠ 0 -> xs <> [].
Proof. by move=> ? /(f_equal lengthN). Qed.

Lemma fmap_dropN {A B} (f : A -> B) (l : list A) (i : N) :
  f <$> dropN i l = dropN i (f <$> l).
Proof. by rewrite /dropN fmap_drop. Qed.

Section seqN.
  Lemma seqN_0 n : seqN n 0 = [].
  Proof. done. Qed.

  Lemma cons_seqN len start :
    start :: seqN (N.succ start) len = seqN start (N.succ len).
  Proof. by rewrite /seqN !N2Nat.inj_succ -cons_seq fmap_cons N2Nat.id. Qed.

  (** More natural version of [cons_seqN]. *)
  Lemma seqN_S_start start len :
    seqN start (N.succ len) = start :: seqN (N.succ start) len.
  Proof. apply symmetry, cons_seqN. Qed.

  (** [seqN_S_start], but without matching against [N.succ]. *)
  Lemma seqN_S_start' start len (Hpos : 0 < len) :
    seqN start len = start :: seqN (N.succ start) (N.pred len).
  Proof. by rewrite -{1}(N.succ_pred_pos len) // seqN_S_start. Qed.

  (* Lifts stdpp's [seq_S] aka stdlib's [seq_S] *)
  Lemma seqN_S_end_app start len :
    seqN start (N.succ len) = seqN start len ++ [start + len].
  Proof.
    rewrite /seqN !N2Nat.inj_succ seq_S fmap_app /=.
    by rewrite -N2Nat.inj_add N2Nat.id.
  Qed.

  (** [seqN_S_end_app], but without matching against [N.succ]. *)
  Lemma seqN_S_end_app' start len (Hpos : 0 < len) :
    seqN start len = seqN start (N.pred len) ++ [start + N.pred len].
  Proof. by rewrite -{1}(N.succ_pred_pos len) // seqN_S_end_app. Qed.

  Lemma seqN_lengthN len start : lengthN (seqN start len) = len.
  Proof. by rewrite /seqN fmap_lengthN /lengthN length_seq N2Nat.id. Qed.

  Lemma NoDup_seqN j n : NoDup (seqN j n).
  Proof. apply /NoDup_fmap_2 /NoDup_seq. Qed.

  Lemma elem_of_seqN (len start n : N) :
    n ∈ seqN start len ↔ start <= n < start + len.
  Proof.
    rewrite /seqN -{1} (N2Nat.id n) elem_of_list_fmap_inj.
    rewrite elem_of_seq. lia.
  Qed.

  #[global] Instance set_unfold_elem_of_seqN (n start len : N) P :
    SetUnfold (start ≤ n < start + len)%N P →
    SetUnfoldElemOf n (seqN start len) P.
  Proof. constructor. rewrite elem_of_seqN. set_solver. Qed.
  #[global] Typeclasses Opaque seqN.

  Lemma Forall_seqN P i n :
    Forall P (seqN i n) ↔ (∀ j : N, i <= j < i + n → P j).
  Proof. rewrite Forall_forall. by setoid_rewrite elem_of_seqN. Qed.

  Lemma fmap_add_seqN (j j' n : N) :
    N.add j <$> seqN j' n = seqN (j + j') n.
  Proof.
    elim /N.peano_ind: n j j' => [| n IHn] j j'.
    - by rewrite !seqN_0.
    - by rewrite !seqN_S_start -N.add_succ_r -IHn.
  Qed.

  Lemma fmap_add_seqN_0 j n :
    N.add j <$> seqN 0 n = seqN j n.
  Proof. by rewrite fmap_add_seqN N.add_0_r. Qed.

  (* Lifts stdpp's [fmap_S_seq] aka stdlib's [seq_shift] *)
  Lemma fmap_S_seqN len start :
    N.succ <$> (seqN start len) = seqN (N.succ start) len.
  Proof.
    rewrite /seqN N2Nat.inj_succ -fmap_S_seq -!list_fmap_compose.
    apply list_fmap_ext; intros; clear. cbn; lia.
  Qed.

  Lemma seqN_sublist (i j n m : N) :
    n <= i -> i + j <= n + m ->
    seqN i j `sublist_of` seqN n m.
  Proof.
    generalize dependent n; generalize dependent j; generalize dependent i.
    induction m using N.peano_ind=> i j n Hni Hijnm.
    - by assert (j = 0) as -> by lia.
    - rewrite seqN_S_start.
      assert (i = n \/ n < i) as [-> | Hni'] by lia.
      + destruct j using N.peano_ind;
          first by rewrite seqN_0; apply sublist_nil_l.
        rewrite seqN_S_start.
        apply sublist_skip.
        by apply IHm; [done | lia].
      + destruct j using N.peano_ind;
          [by rewrite seqN_0; apply sublist_nil_l | clear IHj].
        apply sublist_cons_r; left.
        apply IHm; [lia | lia].
  Qed.

  Lemma dropN_seqN j n m :
    dropN m (seqN j n) = seqN (j + m) (n - m).
  Proof. by rewrite /dropN/seqN -!fmap_drop drop_seq N2Nat.inj_add N2Nat.inj_sub. Qed.

  Lemma dropN_seqN_cons i n :
    i < n ->
    dropN i (seqN 0 n) = i :: dropN (i + 1) (seqN 0 n).
  Proof.
    move=>?.
    rewrite dropN_seqN N.add_0_l (_ : (n - i = N.succ (N.pred (n - i)))); first by
      rewrite seqN_S_start dropN_seqN N.add_0_l; repeat f_equal; lia.
    rewrite (N.lt_succ_pred 0) //; lia.
  Qed.

End seqN.

Lemma repeatN_replicateN {A} (x : A) n :
  repeat x (N.to_nat n) = replicateN n x.
Proof. apply repeat_replicate. Qed.

Lemma repeat_replicateN {A} (x : A) n :
  repeat x n = replicateN (N.of_nat n) x.
Proof. by rewrite repeat_replicate /replicateN Nat2N.id. Qed.

Lemma replicateN_0 {A} (x : A) : replicateN 0 x = [].
Proof. done. Qed.

Lemma replicateN_S {A} (x : A) n : replicateN (N.succ n) x = x :: replicateN n x.
Proof. by rewrite /replicateN/= N2Nat.inj_succ. Qed.

Lemma replicateN_plus {A} (x : A) n m : replicateN (n + m) x = replicateN n x ++ replicateN m x.
Proof. unfold replicateN; rewrite N2Nat.inj_add; apply replicate_add. Qed.

Lemma elem_of_replicateN {A} (count : N) (b a : A) : a ∈ replicateN count b → b = a.
Proof. by intros [-> _]%elem_of_replicate. Qed.

Lemma reverse_nil_iff {A} (xs : list A) : reverse xs = [] <-> xs = [].
Proof.
  case: xs => [|x xs];
    rewrite !(reverse_nil,reverse_cons,app_nil) //;
    intuition; discriminate.
Qed.

(* Outside [Section listN] to generalize over [A]. *)
Lemma length_lengthN {A} (xs : list A) :
  length xs = N.to_nat (lengthN xs).
Proof. by rewrite /lengthN Nat2N.id. Qed.

Section listN.
  Context {A : Type}.

  Implicit Type (x : A) (xs : list A) (i n m k : N).

  Lemma N2Nat_inj_le n m :
    n ≤ m ->
    (N.to_nat n <= N.to_nat m)%nat.
  Proof. lia. Qed.

  Lemma replicateN_zero x :
    replicateN 0 x = [].
  Proof. reflexivity. Qed.

  Lemma replicateN_succ n x :
    replicateN (n + 1) x = x :: replicateN n x.
  Proof. by rewrite /replicateN N.add_1_r N2Nat.inj_succ/=. Qed.

  Lemma replicateN_succ' n x :
    replicateN (n + 1) x = replicateN n x ++ [x].
  Proof.
    elim/N.peano_ind: n=> [|n IH]//.
    rewrite -N.add_1_r replicateN_succ {2}replicateN_succ/=.
    by rewrite IH.
  Qed.

  Definition replicateN_simpl :=
    (@replicateN_zero, @replicateN_succ).

  Lemma replicateN_cons n x :
    0 < n ->
    replicateN n x = x :: replicateN (n - 1) x.
  Proof.
    rewrite /replicateN N2Nat.inj_sub. elim/N.case_analysis: n=> [|n']// _.
    by rewrite N2Nat.inj_succ/= Nat.sub_0_r.
  Qed.

  (* Lift all theory about [drop] and [replicate] interaction. *)
  Lemma dropN_replicateN n m x :
    dropN n (replicateN m x) = replicateN (m - n) x.
  Proof. by rewrite /dropN /replicateN drop_replicate N2Nat.inj_sub. Qed.

  Lemma dropN_replicateN_plus n m x :
    dropN n (replicateN (n + m) x) = replicateN m x.
  Proof. by rewrite /dropN /replicateN N2Nat.inj_add drop_replicate_add. Qed.

  Lemma dropN_replicateN_succ n m x :
    n < m -> dropN n (replicateN m x) = x :: dropN (n + 1)%N (replicateN m x).
  Proof.
    move=>?; rewrite !dropN_replicateN (N.sub_add_distr) replicateN_cons //. lia.
  Qed.

  (* Lift all theory about [take] and [replicate] interaction. *)
  Lemma takeN_replicateN n m x :
    takeN n (replicateN m x) = replicateN (n `min` m) x.
  Proof. by rewrite /takeN /replicateN take_replicate N2Nat.inj_min. Qed.

  Lemma takeN_replicateN_plus n m x :
    takeN n (replicateN (n + m) x) = replicateN n x.
  Proof. by rewrite /takeN /replicateN N2Nat.inj_add take_replicate_add. Qed.

  Lemma takeN_map {B} n (f : A -> B) (xs : list A) :
    takeN n (map f xs) = map f (takeN n xs).
  Proof. by rewrite /takeN firstn_map. Qed.

  Lemma takeN_fmap {B} n (f : A -> B) (xs : list A) :
    takeN n (fmap f xs) = fmap f (takeN n xs).
  Proof. by rewrite /takeN firstn_map. Qed.

  Lemma dropN_map {B} n (f : A -> B) (xs : list A) :
    dropN n (map f xs) = map f (dropN n xs).
  Proof. by rewrite /dropN skipn_map. Qed.

  Lemma dropN_fmap {B} n (f : A -> B) (xs : list A) :
    dropN n (fmap f xs) = fmap f (dropN n xs).
  Proof. by rewrite /dropN skipn_map. Qed.

  Lemma takeN_reverse n (xs : list A) :
    takeN n (reverse xs) = reverse (dropN (lengthN xs - n)%N xs).
  Proof.
    rewrite /lengthN/takeN/dropN take_reverse; do 2 f_equiv.
    lia.
  Qed.

  Lemma dropN_reverse n (xs : list A) :
    dropN n (reverse xs) = reverse (takeN (lengthN xs - n)%N xs).
  Proof.
    rewrite /lengthN/takeN/dropN drop_reverse; do 2 f_equiv.
    lia.
  Qed.

  Lemma to_nat_lengthN xs :
    N.to_nat (lengthN xs) = length xs.
  Proof. by rewrite length_lengthN. Qed.

  Lemma lengthN_length (xs : list A) :
    lengthN xs = N.of_nat (length xs).
  Proof. by []. Qed.

  (* TODO: conflicting naming scheme *)
  Lemma lengthN_fold xs :
    N.of_nat (length xs) = lengthN xs.
  Proof. by rewrite lengthN_length. Qed.

  Lemma lengthN_nil :
    lengthN (A := A) [] = 0.
  Proof. reflexivity. Qed.

  Lemma lengthN_cons x xs :
    lengthN (x :: xs) = (lengthN xs) + 1.
  Proof. rewrite N.add_1_r /lengthN/=. by case: (length xs). Qed.

  Lemma lengthN_eq_0_iff_nil (xs : list A) :
    lengthN xs = 0 <-> xs = [].
  Proof.
    split.
    - case: xs => [//| x xs ].
      rewrite lengthN_cons; lia.
    - by move => ->; rewrite lengthN_nil.
  Qed.

  Lemma lengthN_one x :
    lengthN [x] = 1.
  Proof. reflexivity. Qed.

  Lemma lengthN_app xs1 xs2 :
    lengthN (xs1 ++ xs2) = lengthN xs1 + lengthN xs2.
  Proof. by rewrite /lengthN length_app Nat2N.inj_add. Qed.

  Lemma lengthN_map {B} (f : A -> B) xs :
    lengthN (map f xs) = lengthN xs.
  Proof. by rewrite /lengthN length_map. Qed.

  Lemma lengthN_dropN k xs :
    lengthN (dropN k xs) = lengthN xs - k.
  Proof. by rewrite /lengthN/dropN length_drop Nat2N.inj_sub N2Nat.id. Qed.

  Lemma length_dropN (k : N) xs :
    (length (dropN k xs) = length xs - (N.to_nat k))%nat.
  Proof. by rewrite /dropN length_drop. Qed.

  Lemma lengthN_takeN k xs :
    lengthN (takeN k xs) = k `min` lengthN xs.
  Proof. by rewrite /lengthN/takeN length_take Nat2N.inj_min N2Nat.id. Qed.

  Lemma length_takeN (k : N) xs :
    (length (takeN k xs) = (N.to_nat k) `min` length xs)%nat.
  Proof. by rewrite /takeN length_take. Qed.

  Lemma lengthN_rotateN k xs :
    lengthN (rotateN k xs) = lengthN xs.
  Proof. rewrite /rotateN lengthN_app lengthN_dropN lengthN_takeN. lia. Qed.

  Lemma lengthN_replicateN n x :
    lengthN (replicateN n x) = n.
  Proof. by rewrite /lengthN/replicateN length_replicate N2Nat.id. Qed.

  Lemma lengthN_insertN i x xs :
    lengthN (<[i:=x]> xs) = lengthN xs.
  Proof. rewrite /lengthN. f_equal. by apply: length_insert. Qed.

  Lemma lengthN_reverse (xs : list A) : lengthN (reverse xs) = lengthN xs.
  Proof.
    elim: xs => [|x xs IH];
      by rewrite !(reverse_cons,reverse_nil,lengthN_app,lengthN_cons,lengthN_nil,N.add_0_l) // IH.
  Qed.

  Definition lengthN_simpl :=
    (@lengthN_fold,
     @lengthN_nil, @lengthN_cons,
     @lengthN_app, @lengthN_map,
     @lengthN_dropN, @lengthN_takeN,
     @lengthN_rotateN, @lengthN_replicateN,
     @lengthN_reverse ).

  Lemma lengthN_zip {B} xs (ys : list B) :
    lengthN (zip xs ys) = (lengthN xs) `min` (lengthN ys).
  Proof.
    move: ys; induction xs; first
      by move=>?; rewrite /= !lengthN_nil N.min_0_l.
    move=>ys; move: xs IHxs; induction ys; first done.
    by rewrite /lengthN=>xs IH; rewrite //= !Nat2N.inj_succ -N.succ_min_distr IH.
  Qed.

  Lemma length_zip_with_le {B C} {f : A -> B -> C} (xs : list A) (ys : list B)
    (Hlen : (length xs <= length ys)%nat) :
    length (zip_with f xs ys) = length xs.
  Proof.
    elim: xs ys Hlen => [|x xs IH] - [|y ys] //= Hlen.
    - lia.
    - by move: Hlen => /le_S_n /IH ->.
  Qed.

  Lemma lengthN_zip_with_le {B C} {f : A -> B -> C} (xs : list A) (ys : list B)
    (Hlen : (lengthN xs <= lengthN ys)%N) :
    lengthN (zip_with f xs ys) = lengthN xs.
  Proof.
    move: Hlen; rewrite /lengthN => /N_of_nat_le_mono ?.
    by rewrite length_zip_with_le.
  Qed.

  Lemma zip_with_app_if_length_eq {B C} {f : A -> B -> C} (xs xs' : list A) (ys ys' : list B)
    (Hlen : length xs = length ys) :
    zip_with f (xs ++ xs') (ys ++ ys') = zip_with f xs ys ++ zip_with f xs' ys'.
  Proof.
    move: Hlen => /inj_iff.
    by elim: xs ys
        => [| x xs IH] - [| y ys ] //= [=] /IH ->.
  Qed.

  Lemma zip_with_app_if_lengthN_eq {B C} {f : A -> B -> C} (xs xs' : list A) (ys ys' : list B)
    (Hlen : lengthN xs = lengthN ys) :
    zip_with f (xs ++ xs') (ys ++ ys') = zip_with f xs ys ++ zip_with f xs' ys'.
  Proof.
    move: Hlen; rewrite /lengthN => /(inj _ _ _).
    apply zip_with_app_if_length_eq.
  Qed.

  Lemma eq_singleton_if_lengthN_eq_one (xs : list A) :
    lengthN xs = 1%N <-> ∃ x, xs = [x].
  Proof.
    split.
    - case: xs => [|x xs]; rewrite (lengthN_nil,lengthN_cons) //.
      rewrite N.add_1_r -[1%N]/(0 + 1)%N N.add_1_r inj_iff.
      rewrite lengthN_eq_0_iff_nil => ->; by eexists.
    - by move => [x ->]; rewrite lengthN_one.
  Qed.

  Lemma resizeN_spec l n x :
    resizeN n x l = takeN n l ++ replicateN (n - lengthN l) x.
  Proof.
    by rewrite /resizeN /replicateN resize_spec !N2Nat.inj_sub Nat2N.id.
  Qed.

  Lemma resizeN_all l x : resizeN (lengthN l) x l = l.
  Proof. by rewrite /resizeN /lengthN Nat2N.id resize_all. Qed.

  Lemma resizeN_0 l x : resizeN 0 x l = [].
  Proof. by rewrite /resizeN resize_0. Qed.

  Lemma resizeN_lengthN l n x :
    lengthN (resizeN n x l) = n.
  Proof. by rewrite /lengthN /resizeN /= length_resize N2Nat.id. Qed.

  Lemma resizeN_nil n x : resizeN n x [] = replicateN n x.
  Proof. apply resize_nil. Qed.

  Lemma resizeN_replicateN x n m:
    resizeN n x (replicateN m x) = replicateN n x.
  Proof. by rewrite /resizeN /replicateN resize_replicate. Qed.

  Lemma resizeN_idemp l n x :
    resizeN n x (resizeN n x l) = resizeN n x l.
  Proof. apply resize_idemp. Qed.

  Lemma resizeN_plusN l n m x :
    resizeN (n + m) x l = resizeN n x l ++ resizeN m x (dropN n l).
  Proof. by rewrite /resizeN /dropN N2Nat.inj_add resize_add. Qed.

  Lemma resizeN_takeN_eq l n x :
    resizeN n x (takeN n l) = resizeN n x l.
  Proof. apply resize_take_eq. Qed.

  Lemma resizeN_le l n x :
    n <= lengthN l ->
    resizeN n x l = takeN n l.
  Proof. move=> /N2Nat_inj_le. rewrite to_nat_lengthN. apply resize_le. Qed.

  Lemma resizeN_takeN_le l n m x :
    (n <= m) → resizeN n x (takeN m l) = resizeN n x l.
  Proof. move=> /N2Nat_inj_le. apply resize_take_le. Qed.

  Lemma dropN_lengthN n xs :
    lengthN xs <= n -> dropN n xs = [].
  Proof.
    rewrite /lengthN/dropN=> /N2Nat_inj_le. rewrite Nat2N.id.
    by apply: drop_ge.
  Qed.

  Lemma dropN_zero xs :
    dropN 0 xs = xs.
  Proof. reflexivity. Qed.

  Lemma dropN_one x xs :
    dropN 1 (x :: xs) = xs.
  Proof. reflexivity. Qed.

  Lemma dropN_tail xs :
    dropN 1 xs = tail xs.
  Proof. by case: xs. Qed.

  Lemma dropN_dropN n m xs :
    dropN n (dropN m xs) = dropN (n + m) xs.
  Proof.
    rewrite /dropN N2Nat.inj_add Nat.add_comm. by apply: drop_drop.
  Qed.

  Lemma dropN_nil n :
    dropN (A := A) n [] = [].
  Proof. rewrite /dropN. by case: (N.to_nat _). Qed.

  Lemma dropN_cons_succ x xs i :
    dropN (i + 1) (x :: xs) = dropN i xs.
  Proof. by rewrite -dropN_dropN dropN_one. Qed.

  Lemma dropN_cons_succ' x xs i :
    dropN (N.succ i) (x :: xs) = dropN i xs.
  Proof. by rewrite -N.add_1_r dropN_cons_succ. Qed.

  Lemma dropN_app n xs1 xs2 :
    dropN n (xs1 ++ xs2) = dropN n xs1 ++ dropN (n - lengthN xs1) xs2.
  Proof.
    rewrite /dropN/lengthN N2Nat.inj_sub Nat2N.id. by apply: skipn_app.
  Qed.

  Lemma dropN_takeN n m xs :
    dropN n (takeN m xs) = takeN (m - n) (dropN n xs).
  Proof.
    rewrite /dropN/takeN N2Nat.inj_sub. by apply: skipn_firstn_comm.
  Qed.

  Lemma dropN_resizeN_plus l m n x :
    dropN n (resizeN (n + m) x l) = resizeN m x (dropN n l).
  Proof. by rewrite /dropN /resizeN N2Nat.inj_add drop_resize_add. Qed.

  Lemma dropN_resizeN_le l n m x :
    n <= m →
    dropN n (resizeN m x l) = resizeN (m - n) x (dropN n l).
  Proof.
    move=> /N2Nat_inj_le Hle.
    by rewrite /dropN /resizeN drop_resize_le // N2Nat.inj_sub.
  Qed.

  Lemma dropN_lookupN i xs x__i :
    xs !! i = Some x__i ->
    dropN i xs = x__i :: dropN (i + 1) xs.
  Proof.
    rewrite /lookup/list_lookupN/dropN/= N.add_1_r N2Nat.inj_succ.
    elim: (N.to_nat i) xs=> {i} [|i IH] [|x xs]//=.
    - by case=> ->.
    - by apply: IH.
  Qed.

  Lemma dropN_insertN_ge i n x xs :
    (i >= n)%N ->
    dropN n (<[i:=x]> xs) = <[(i - n)%N:=x]> (dropN n xs).
  Proof.
    move/N.ge_le/N2Nat_inj_le. rewrite /insert/list_insertN N2Nat.inj_sub.
    by apply: drop_insert_le.
  Qed.

  Lemma dropN_insertN_lt i n x xs :
    (i < n)%N ->
    dropN n (<[i:=x]> xs) = dropN n xs.
  Proof. move=> H. apply: drop_insert_gt. lia. Qed.

  Lemma takeN_zero xs :
    takeN 0 xs = [].
  Proof. reflexivity. Qed.

  Lemma takeN_one x xs :
    takeN 1 (x :: xs) = [x].
  Proof. reflexivity. Qed.

  Lemma takeN_lengthN n xs :
    lengthN xs <= n -> takeN n xs = xs.
  Proof.
    rewrite /lengthN/takeN=> /N2Nat_inj_le. rewrite Nat2N.id.
    by apply: take_ge.
  Qed.

  Lemma takeN_singleton' x i :
    takeN (N.succ i) [x] = [x].
  Proof. rewrite takeN_lengthN // lengthN_one. lia. Qed.

  Lemma takeN_singleton x i :
    takeN (i + 1) [x] = [x].
  Proof. by rewrite N.add_1_r takeN_singleton'. Qed.

  Lemma takeN_app n xs1 xs2 :
    takeN n (xs1 ++ xs2) = takeN n xs1 ++ takeN (n - lengthN xs1) xs2.
  Proof.
    rewrite /takeN/lengthN N2Nat.inj_sub Nat2N.id. by apply: firstn_app.
  Qed.

  Lemma takeN_nil n :
    takeN (A := A) n [] = [].
  Proof. rewrite /takeN. by case: (N.to_nat _). Qed.

  Lemma takeN_cons_succ x xs i :
    takeN (i + 1) (x :: xs) = x :: takeN i xs.
  Proof. by rewrite -/([x] ++ xs) takeN_app lengthN_one takeN_singleton/= N.add_sub. Qed.

  Lemma takeN_cons_succ' x xs i :
    takeN (N.succ i) (x :: xs) = x :: takeN i xs.
  Proof. by rewrite -N.add_1_r takeN_cons_succ. Qed.

  (** Analog to [take_S_r] using [N.succ n]. *)
  Lemma takeN_S_r' x xs n :
    xs !! n = Some x ->
    takeN (N.succ n) xs = takeN n xs ++ [x].
  Proof. intros; rewrite /takeN N2Nat.inj_succ. exact: take_S_r. Qed.

  (** Analog to [take_S_r] using [n + 1]. *)
  Lemma takeN_S_r x xs n :
    xs !! n = Some x ->
    takeN (n + 1) xs = takeN n xs ++ [x].
  Proof. rewrite N.add_1_r. apply takeN_S_r'. Qed.

  Lemma takeN_takeN n m xs :
    takeN n (takeN m xs) = takeN (n `min` m) xs.
  Proof.
    rewrite /takeN N2Nat.inj_min. by apply: take_take.
  Qed.

  (** Analog to [take_drop]. *)
  Lemma takeN_dropN i xs : takeN i xs ++ dropN i xs = xs.
  Proof. apply take_drop. Qed.

  (** Analog to [take_drop_commute]. *)
  Lemma takeN_dropN_commute n m xs :
    takeN n (dropN m xs) = dropN m (takeN (m + n) xs).
  Proof.
    rewrite /dropN/takeN N2Nat.inj_add. by apply: take_drop_commute.
  Qed.

  Lemma takeN_resizeN_eq l n x :
    takeN n (resizeN n x l) = resizeN n x l.
  Proof. apply take_resize_eq. Qed.

  Lemma takeN_resizeN l n m x :
    takeN n (resizeN m x l) = resizeN (n `min` m) x l.
  Proof. by rewrite /takeN /resizeN take_resize N2Nat.inj_min. Qed.

  Lemma takeN_resizeN_plus l n m x :
    takeN n (resizeN (n + m) x l) = resizeN n x l.
  Proof. by rewrite /takeN /resizeN N2Nat.inj_add take_resize_add. Qed.

  Lemma takeN_resizeN_le l n m x :
    n ≤ m →
    takeN n (resizeN m x l) = resizeN n x l.
  Proof. move=> /N2Nat_inj_le. apply take_resize_le. Qed.

  Lemma takeN_insertN_ge i n x xs :
    (i >= n)%N ->
    takeN n (<[i:=x]> xs) = takeN n xs.
  Proof. move/N.ge_le/N2Nat_inj_le. by apply: take_insert. Qed.

  Lemma takeN_insertN_lt i n x xs :
    (i < n)%N ->
    takeN n (<[i:=x]> xs) = <[i:=x]> (takeN n xs).
  Proof. move=> H. apply: take_insert_lt. lia. Qed.

  Lemma rotateN_fold k xs :
    rotate (N.to_nat k) xs = rotateN k xs.
  Proof.
    rewrite /rotateN/dropN/takeN/rotate.
    by rewrite !N2Nat.inj_mod to_nat_lengthN.
  Qed.

  Definition head_list {A} (xs : list A) := option_list (hd_error xs).

  Lemma tail_drop xs : tail xs = drop 1 xs.
  Proof. reflexivity. Qed.

  Lemma head_list_take xs : head_list xs = take 1 xs.
  Proof. by case: xs. Qed.

  Lemma rotateN_iter k xs :
    rotateN k xs = N.iter k (fun xs => tail xs ++ head_list xs) xs.
  Proof.
    elim/N.peano_ind: k xs=> [|k IH] xs.
    { by rewrite /rotateN/rotate/= app_nil_r. }
    rewrite N.iter_succ//= -IH -N.add_1_r.
    rewrite -!rotateN_fold /rotate tail_drop head_list_take.
    case: xs=> [|x1 xs]; first by do !rewrite drop_nil take_nil.
    case: xs=> [|x2 xs]; first by rewrite !Nat.mod_1_r/=.
    set n := length (x1 :: x2 :: xs).
    have ?: (n <> 0)%nat by rewrite /n/=.
    have ?: (1 < n)%nat by rewrite /n/=; lia.
    have ?: (N.to_nat k `mod` n < n)%nat by apply: Nat.mod_upper_bound=> //.
    have ?: (1 <= n - (N.to_nat k `mod` n))%nat by lia.
    rewrite drop_app_le; last by rewrite length_drop -/n.
    rewrite take_app_le; last by rewrite length_drop -/n.
    rewrite drop_drop -app_assoc take_take_drop.
    rewrite N2Nat.inj_add -[N.to_nat 1]/1%nat -Nat.Div0.add_mod_idemp_l//.
    case/decide: (N.to_nat k `mod` n + 1 = n)%nat=> E.
    - rewrite E Nat.Div0.mod_same//= drop_all firstn_all.
      by rewrite app_nil_l app_nil_r.
    - rewrite Nat.mod_small//. lia.
  Qed.

  Lemma rotateN_nil k :
      rotateN (A := A) k [] = [].
  Proof. by rewrite /rotateN/rotate/= dropN_nil takeN_nil. Qed.

  Lemma rotateN_singleton k x :
    rotateN k [x] = [x].
  Proof. by rewrite -rotateN_fold. Qed.

  Lemma rotateN_zero xs :
    rotateN 0 xs = xs.
  Proof.
    case: xs=> [|x xs]; first by rewrite rotateN_nil.
    by rewrite -rotateN_fold /= /rotate /= Nat.sub_diag /= app_nil_r.
  Qed.

  Lemma rotateN_one x xs :
    rotateN 1 (x :: xs) = xs ++ [x].
  Proof.
    rewrite -rotateN_fold /rotate [length (x :: xs)]/=.
    set n := S _. case/Nat.lt_eq_cases: (ltac:(lia) : (1 <= n)%nat)=> H.
    - by rewrite Nat.mod_1_l.
    - rewrite -H/= app_nil_r. subst n. case: xs H=> [|??]//=.
  Qed.

  Lemma rotateN_lengthN k xs :
    k = lengthN xs ->
    rotateN k xs = xs.
  Proof.
    move=> -> {k}. rewrite -rotateN_fold /rotate /lengthN Nat2N.id.
    case: xs=> [|x xs]//. by rewrite Nat.Div0.mod_same//= app_nil_r.
  Qed.

  Lemma rotateN_modulo k xs :
    rotateN (k `mod` lengthN xs) xs = rotateN k xs.
  Proof.
    case: xs=> [|x xs]; first by rewrite !rotateN_nil.
    rewrite -!rotateN_fold /rotate/lengthN.
    rewrite N2Nat.inj_mod// Nat2N.id.
    by rewrite Nat.Div0.mod_mod//.
  Qed.

  Lemma rotateN_modulo' k xs :
    rotateN (Z.to_N (k `mod` lengthN xs)) xs = rotateN k xs.
  Proof.
    case/N.eq_0_gt_0_cases: (lengthN xs)=> H.
    - case: xs H=> //. by rewrite !rotateN_nil.
    - rewrite Z2N.inj_mod ?N2Z.id; try by lia.
      by rewrite rotateN_modulo.
  Qed.

  Lemma rotateN_plus k1 k2 xs :
    rotateN (k1 + k2) xs = rotateN k1 (rotateN k2 xs).
  Proof. by rewrite !rotateN_iter N.iter_add. Qed.

  Lemma rotateN_succ k x xs :
    rotateN (k + 1) (x :: xs) = rotateN k (xs ++ [x]).
  Proof. by rewrite rotateN_plus rotateN_one. Qed.

  Lemma rotateN_index k xs :
    k <= lengthN xs ->
    rotateN k xs = dropN k xs ++ takeN k xs.
  Proof.
    case/N.le_lteq=> [H|->]; first by rewrite /rotateN N.mod_small//.
    by rewrite rotateN_lengthN// dropN_lengthN// takeN_lengthN//.
  Qed.

  Lemma rotateN_mid k xs zs :
    exists xs' zs', forall y, rotateN k (xs ++ [y] ++ zs) = xs' ++ [y] ++ zs'.
  Proof.
    elim/N.peano_ind: k xs zs=> [|k IH] xs zs.
    - exists xs. exists zs. move=> y. by rewrite rotateN_zero.
    - rewrite -N.add_1_r. case: xs=> [|x xs].
      + case/(_ zs []): IH=> [xs' [zs' IH]].
        exists xs'. exists zs'. move=> y.
        rewrite app_nil_l/= rotateN_succ.
        by apply: IH.
      + case/(_ xs (zs ++ [x])): IH=> [xs' [zs' IH]].
        exists xs'. exists zs'. move=> y.
        rewrite -app_comm_cons rotateN_succ -2!app_assoc.
        by apply: IH.
  Qed.

  Lemma rotateN_replicateN k n x :
    rotateN k (replicateN n x) = replicateN n x.
  Proof. by rewrite -rotateN_fold /replicateN rotate_replicate. Qed.

  Definition rotateN_simpl :=
    (@rotateN_zero, @rotateN_one, @rotateN_succ,
     @rotateN_modulo, @rotateN_singleton, @rotateN_replicateN).

  Lemma lookupN_fold {A'} i (xs : list A') :
    xs !! N.to_nat i = lookupN i xs.
  Proof. reflexivity. Qed.

  Lemma lookupN_nil i :
    lookupN i [] = @None A.
  Proof. rewrite -lookupN_fold. by apply: lookup_nil. Qed.

  Lemma lookupN_cons_zero x xs :
    lookupN 0 (x :: xs) = Some x.
  Proof. reflexivity. Qed.

  Lemma lookupN_cons_Nsucc x xs i :
    lookupN (N.succ i) (x :: xs) = lookupN i xs.
  Proof. by rewrite -!lookupN_fold N2Nat.inj_succ -lookup_tail. Qed.

  Lemma lookupN_cons_succ x xs i :
    lookupN (i + 1) (x :: xs) = lookupN i xs.
  Proof. by rewrite N.add_1_r lookupN_cons_Nsucc. Qed.

  Lemma lookupN_dropN xs k i :
    lookupN i (dropN k xs) = lookupN (k + i) xs.
  Proof. rewrite -!lookupN_fold /dropN N2Nat.inj_add. by apply: lookup_drop. Qed.

  Lemma lookupN_takeN xs k i :
    i < k ->
    lookupN i (takeN k xs) = lookupN i xs.
  Proof. rewrite -!lookupN_fold /takeN=> H. by apply: lookup_take; lia. Qed.

  Lemma lookupN_is_Some xs i :
    i < lengthN xs <-> is_Some (lookupN i xs).
  Proof. rewrite -lookupN_fold /lengthN lookup_lt_is_Some. lia. Qed.

  Lemma lookupN_is_None {A'} (xs : list A') i :
    i >= lengthN xs <-> lookupN i xs = None.
  Proof. rewrite -lookupN_fold /lengthN lookup_ge_None. lia. Qed.

  Lemma lookupN_bound xs i :
    is_Some (xs !! i) -> i < lengthN xs.
  Proof. by rewrite lookupN_is_Some. Qed.

  Lemma lookupN_replicateN n x i :
    lookupN i (replicateN n x) = Some x <-> i < n.
  Proof.
    rewrite -lookupN_fold /replicateN lookup_replicate. split; [|split=> //]; lia.
  Qed.

  Lemma lookupN_head xs :
    lookupN 0 xs = head xs.
  Proof. by case: xs. Qed.

  Lemma dropN_S xs (n : N) v:
    xs !! n = Some v ->
    dropN n xs = v :: dropN (N.succ n) xs.
  Proof.
    elim: xs n v => [// | x xs IHxs].
    elim /N.peano_ind => [|n IHn] v.
    { by rewrite dropN_zero lookupN_head /= dropN_one => -[->]. }
    rewrite lookupN_cons_Nsucc !dropN_cons_succ'. exact: IHxs.
  Qed.

  Lemma lookupN_tail xs i :
    lookupN i (tail xs) = lookupN (i + 1) xs.
  Proof. rewrite -!lookupN_fold N.add_1_r N2Nat.inj_succ. by apply: lookup_tail. Qed.

  Lemma lookupN_app_l xs1 xs2 i :
    i < lengthN xs1 ->
    lookupN i (xs1 ++ xs2) = lookupN i xs1.
  Proof.
    rewrite -!lookupN_fold /lengthN=> H. by apply: lookup_app_l; lia.
  Qed.

  Lemma lookupN_app_r xs1 xs2 i :
    i >= lengthN xs1 ->
    lookupN i (xs1 ++ xs2) = lookupN (i - lengthN xs1) xs2.
  Proof.
    rewrite -!lookupN_fold /lengthN N2Nat.inj_sub Nat2N.id=> H.
    by apply: lookup_app_r; lia.
  Qed.

  Lemma lookupN_insertN_eq i x xs :
    (i < lengthN xs)%N ->
    <[i:=x]> xs !! i = Some x.
  Proof. rewrite /lengthN. move=> H. apply: list_lookup_insert. lia. Qed.

  Lemma lookupN_insertN_neq i j x xs :
    i <> j ->
    <[i:=x]> xs !! j = xs !! j.
  Proof. move=> H. apply: list_lookup_insert_ne. lia. Qed.

  Lemma lookupN_nth_error {A'} i (xs : list A') :
    lookupN i xs = nth_error xs (N.to_nat i).
  Proof.
    elim/N.peano_ind: i xs=> [|i IH]//=; case=> [|x xs]//=.
    - rewrite -lookupN_fold lookup_nil. by case: (N.to_nat).
    - rewrite N2Nat.inj_succ/= -lookupN_fold N2Nat.inj_succ -lookup_tail/=.
      by apply: IH.
  Qed.

  Lemma lookupN_map {B} (f : A -> B) xs i :
    lookupN i (map f xs) = if lookupN i xs is Some x then Some (f x) else None.
  Proof.
    set n := lengthN xs.
    case/decide: (i < n)=> [/lookupN_is_Some[x]/[dup]|/[dup]/lookupN_is_None].
    - by rewrite !lookupN_nth_error=> /(map_nth_error f _ _)=> -> ->.
    - by rewrite /n -(lengthN_map f)=> -> /lookupN_is_None ->.
  Qed.

  Lemma lookupN_rotateN xs k i :
    i < lengthN xs ->
    lookupN i (rotateN k xs) = lookupN ((k + i) mod lengthN xs) xs.
  Proof.
    rewrite -!lookupN_fold -rotateN_fold /lengthN=> H.
    rewrite lookup_rotate_r /rotate_nat_add; last by lia.
    f_equal. rewrite !N_nat_Z -N2Z.inj_add -nat_N_Z -N2Z.inj_mod.
    by rewrite -Z_N_nat N2Z.id.
  Qed.

  Lemma lookupN_any i xs :
    A (* nonempty *) ->
    (forall x, exists y, x <> y :> A) ->
    (forall x, lookupN i xs = Some x) ->
    False.
  Proof.
    move=> x0 H. case: (lookupN i xs)=> [y|].
    - case/(_ y): H=> x + /(_ x) []. by apply.
    - by move/(_ x0).
  Qed.

  Lemma lookupN_mid i xs zs :
    A (* nonempty *) ->
    (forall x, exists y, x <> y :> A) ->
    (forall y, lookupN i (xs ++ [y] ++ zs) = Some y) ->
    lengthN xs = i.
  Proof.
    move=> x0 H. elim/N.peano_ind: i xs zs=> [|i IH] xs zs.
    - case: xs=> [|x xs]//.
      move/(_ x): H=> [y H].
      move/(_ y). rewrite lookupN_cons_zero=> - [].
      by [].
    - rewrite -N.add_1_r. case: xs=> [|x xs].
      + move=> H'. exfalso. apply: (lookupN_any i zs x0 H).
        move=> y. move/(_ y): H'=> /=. by rewrite lookupN_cons_succ.
      + move/(_ xs zs): IH=> IH. rewrite lengthN_cons.
        move=> H'. f_equal. apply: IH. move=> y. rewrite -H'.
        by rewrite -[(x :: xs) ++ _]app_comm_cons lookupN_cons_succ.
  Qed.

  Lemma lookupN_explode xs x i :
    xs !! i = Some x ->
    xs = takeN i xs ++ [x] ++ dropN (i + 1) xs.
  Proof.
    elim/N.peano_ind: i xs=> [|i IH]; case=> [|x0 xs]//.
    - by rewrite -[0+1]/1 lookupN_head/= dropN_one=> - [->].
    - rewrite -N.add_1_r/= lookupN_cons_succ. move/IH=> {1}-> {IH}.
      by rewrite takeN_cons_succ dropN_cons_succ/=.
  Qed.

  Definition lookupN_simpl :=
    (@lookupN_nil, @lookupN_cons_zero, @lookupN_cons_succ,
     @lookupN_dropN, @lookupN_takeN,
     @lookupN_is_Some, @lookupN_is_None,
     @lookupN_replicateN,
     @lookupN_tail, @lookupN_head,
     @lookupN_app_l, @lookupN_app_r,
     @lookupN_map,
     @lookupN_rotateN).

  Lemma lookupN_ge_None xs i :
    xs !! i = None ↔ lengthN xs <= i.
  Proof. rewrite list_lookupN_lookup /lengthN lookup_ge_None; lia. Qed.

  Lemma lookupN_seqN_ge j n i : n ≤ i → seqN j n !! i = None.
  Proof.
    intros. rewrite /seqN list_lookupN_lookup list_lookup_fmap.
    rewrite lookup_seq_ge //; lia.
  Qed.
  Lemma lookupN_seqN_lt j n i : i < n → seqN j n !! i = Some (j + i).
  Proof.
    intros. rewrite /seqN list_lookupN_lookup list_lookup_fmap.
    rewrite lookup_seq_lt //=; [f_equiv|]; lia.
  Qed.
  Lemma lookupN_seqN : ∀ j n i j', seqN j n !! i = Some j' ↔ j' = j + i ∧ i < n.
  Proof.
    intros. rewrite /seqN list_lookupN_lookup list_lookup_fmap.
    trans (seq (N.to_nat j) (N.to_nat n) !! N.to_nat i = Some (N.to_nat j')); first last.
    { rewrite lookup_seq //=; lia. }
    split; last by move ->; rewrite /= N2Nat.id.
    rewrite !fmap_Some. intros (x' & ? & ->). by rewrite Nat2N.id.
  Qed.

  Lemma takeN_zip_with {B C} (f : A -> B -> C) n xs ys :
    takeN n (zip_with f xs ys) = zip_with f (takeN n xs) (takeN n ys).
  Proof. by rewrite /takeN zip_with_take. Qed.

  Lemma dropN_zip_with {B C} (f : A -> B -> C) n xs ys :
    dropN n (zip_with f xs ys) = zip_with f (dropN n xs) (dropN n ys).
  Proof. by rewrite /dropN zip_with_drop. Qed.

  Lemma zip_with_lookupN_Some {B C} (f : A -> B -> C) x (y : B) xs (ys : list B) i :
    xs !! i = Some x
    -> ys !! i = Some y
    -> zip_with f xs ys !! i = Some (f x y).
  Proof. by rewrite !list_lookupN_lookup lookup_zip_with => -> ->. Qed.

  Lemma zip_lookupN_Some {B} x (y : B) xs (ys : list B) i :
    xs !! i = Some x
    -> ys !! i = Some y
    -> zip xs ys !! i = Some (x, y).
  Proof. apply zip_with_lookupN_Some. Qed.

  Lemma insertN_seqN (i j k : N) :
    <[ k := (i + k)%N ]> (seqN i j) = seqN i j.
  Proof.
    rewrite list_insertN_insert; destruct (decide (k < j)%N).
    by rewrite list_insert_id // -list_lookupN_lookup lookupN_seqN_lt.
    by rewrite list_insert_ge // length_lengthN seqN_lengthN; lia.
  Qed.

  Lemma insertN_id i x xs :
    xs !! i = Some x ->
    <[i:=x]> xs = xs.
  Proof. by apply: list_insert_id. Qed.

  Lemma insertN_nil i x :
    <[i:=x]> [] = [].
  Proof. reflexivity. Qed.

  Lemma insertN_cons_zero x x' xs :
    <[0%N:=x']> (x :: xs) = x' :: xs.
  Proof. reflexivity. Qed.

  Lemma insertN_cons_succ i x x' xs :
    <[(i + 1)%N:=x']> (x :: xs) = x :: <[i:=x']> xs.
  Proof. by rewrite /insert/list_insertN N.add_1_r N2Nat.inj_succ. Qed.

  Lemma insertN_lengthN i x xs :
    (i >= lengthN xs)%N ->
    <[i:=x]> xs = xs.
  Proof. move/N.ge_le/N2Nat_inj_le. rewrite /lengthN Nat2N.id. by apply: list_insert_ge. Qed.

  Lemma insertN_insertN i x x' xs :
    <[i:=x']> (<[i:=x]> xs) = <[i:=x']> xs.
  Proof. by apply: list_insert_insert. Qed.

  Lemma insertN_comm i j x x' xs :
  i <> j ->
  <[i:=x]> (<[j:=x']> xs) = <[j:=x']> (<[i:=x]> xs).
  Proof. move=> H. apply: list_insert_commute. lia. Qed.

  Lemma insertN_app_l i x xs1 xs2 :
    (i < lengthN xs1)%N ->
    <[i:=x]> (xs1 ++ xs2) = <[i:=x]> xs1 ++ xs2.
  Proof. rewrite /lengthN. move=> H. apply: insert_app_l. lia. Qed.

  Lemma insertN_app_r i x xs1 xs2 :
    (i >= lengthN xs1)%N ->
    <[i:=x]> (xs1 ++ xs2) = xs1 ++ <[(i - lengthN xs1)%N:=x]> xs2.
  Proof.
    move/N.ge_le/N2Nat_inj_le. rewrite /insert/list_insertN/lengthN N2Nat.inj_sub Nat2N.id.
    by apply: insert_app_r_alt.
  Qed.

  Lemma map_insertN {B} (f : A -> B) i x xs :
    f <$> (<[i:=x]> xs) = <[i:=f x]> (f <$> xs).
  Proof. by apply: list_fmap_insert. Qed.

  Lemma insertN_replicateN i n x :
    <[i:=x]> (replicateN n x) = replicateN n x.
  Proof. rewrite /replicateN. by apply: insert_replicate. Qed.

  Lemma insertN_explode xs x i :
    i < lengthN xs ->
    <[i:=x]> xs = takeN i xs ++ [x] ++ dropN (i + 1) xs.
  Proof.
    elim/N.peano_ind: i xs=> [|i IH]; case=> [|x0 xs]//; rewrite -N.add_1_r !lengthN_simpl.
    - lia.
    - rewrite insertN_cons_succ takeN_cons_succ dropN_cons_succ.
      by rewrite -N.add_lt_mono_r=> /IH ->.
  Qed.

  Lemma insertN_takeN_dropN (l : list A) (i : N) (x : A) (Hl : (i < lengthN l)%N) :
    <[i:=x]> l = (takeN i l ++ x :: dropN (i + 1) l).
  Proof.
    move: Hl; rewrite /lengthN -{1}(N2Nat.id i) => /N_of_nat_lt_mono => Hlt.
    rewrite /insertN /list_insertN /takeN /dropN N.add_1_r N2Nat.inj_succ.
    rewrite insert_take_drop //.
  Qed.

  Lemma list_alterN_insertN xs i f :
    alter f i xs = if xs !! i is Some x then <[i:=f x]> xs else xs.
  Proof. by rewrite list_alterN_alter list_alter_insert. Qed.

  Lemma alterN_explode xs x i f :
    xs !! i = Some x ->
    alter f i xs = takeN i xs ++ [f x] ++ dropN (i + 1) xs.
  Proof.
    move=> H. rewrite list_alterN_insertN H.
    by rewrite insertN_explode; last by rewrite lookupN_is_Some H.
  Qed.

  Definition insertN_simpl :=
    (@insertN_nil, @insertN_cons_zero, @insertN_cons_succ).
End listN.

(* Not necessarily restricted to [Finite] *)
Lemma nat_fin_iter_lt (c : nat) (P : nat -> Prop) :
  Forall P (seq 0 c) ->
  forall i, (i < c)%nat -> P i.
Proof. move=>/Forall_seq /= F. eauto with lia. Qed.

Lemma nat_fin_iter_le (c : nat) (P : nat -> Prop) :
  Forall P (seq 0 (S c)) ->
  forall i, (i <= c)%nat -> P i.
Proof. move=> F i Hle. eapply nat_fin_iter_lt; [done | lia]. Qed.

Lemma N_fin_iter_lt (c : N) (P : N -> Prop) :
  Forall P (seqN 0 c) ->
  forall i, i < c -> P i.
Proof.
  move=> F i Hle. rewrite -(N2Nat.id i).
  apply (nat_fin_iter_lt (N.to_nat c) (P ∘ N.of_nat)); [| lia] => {i Hle}.
  rewrite -Forall_fmap. apply F.
Qed.

Lemma N_fin_iter_le (c : N) (P : N -> Prop) :
  Forall P (seqN 0 (N.succ c)) ->
  forall i, i <= c -> P i.
Proof. move=> F i Hle. eapply N_fin_iter_lt; [done | lia]. Qed.

(* Given [n < k] for some constant value [k], asserts that
 * [(n = 0) \/ (n = 1) \/ ... (n = k - 1)]; for example, [n < 3] gives
 * [(n = 0) \/ (n = 1) \/ (n = 2)]. *)
Lemma N_enumerate n m :
  n < m -> N.recursion False (fun k H => (n = k) \/ H) m.
Proof.
  elim/N.peano_ind: m=> [|m']//=; first by move/N.nlt_0_r.
  rewrite N.recursion_succ// N.lt_succ_r N.lt_eq_cases=> IH.
  case=> [{} /IH IH|H]; by [right|left].
Qed.

#[global] Notation lengthZ x := (Z.of_N (lengthN x)).
#[global] Notation replicateZ n := (replicateN (Z.to_N n)).

Section listZ.
  #[local] Open Scope Z_scope.

  Lemma lengthZ_eq_sub_iff {A} (m n : Z) (xs : list A) :
    lengthZ xs = m - n <-> lengthN xs = Z.to_N (m - n) ∧ n ≤ m.
  Proof. lia. Qed.

  Fixpoint list_lookupZ {A} : Lookup Z A (list A) :=
    fun k xs =>
    match xs with
    | [] => None
    | x :: xs' =>
        match Z.compare k 0 with
        | Lt => None
        | Eq => Some x
        | Gt => xs' !! (Z.pred k)
        end
    end.
  #[global] Existing Instance list_lookupZ | 20.

  #[global] Instance list_insertZ {A} : Insert Z A (list A) | 20 :=
    fun k a l =>
    if bool_decide (0 ≤ k)
      then <[ Z.to_nat k := a ]> l
      else l.

  Definition takeZ {A} (n : Z) := (takeN (A := A) (Z.to_N n)).
  #[global] Hint Opaque takeZ : typeclass_instances sl_opacity.
  Definition dropZ {A} (n : Z) := (dropN (A := A) (Z.to_N n)).
  #[global] Hint Opaque dropZ : typeclass_instances sl_opacity.

  Lemma insertZ_eq_insertN {A} (k : Z) x (xs : list A) :
    <[ k := x ]> xs =
      if bool_decide (0 ≤ k)
        then <[ Z.to_N k := x ]> xs
        else xs.
  Proof. by rewrite /insert /list_insertZ /list_insertN Z_N_nat. Qed.

  Lemma insertZ_cons_iff {A} x x' (xs : list A) (k : Z) :
    <[ k := x' ]> (x :: xs) =
      if bool_decide (k = 0)
        then x' :: xs
        else x :: <[ k - 1 := x']> xs.
  Proof.
    rewrite /insert /list_insertZ.
    case: bool_decide_reflect; first last.
    { move => ?; rewrite !bool_decide_eq_false_2 //; lia. }
    move => /Zle_lt_or_eq []; first last.
    - by move => /symmetry_iff -> /=.
    - move => ?.
      have ? : k <> 0 by lia.
      have ? : (0 ≤ k - 1) by lia.
      rewrite bool_decide_eq_false_2 // bool_decide_eq_true_2 //.
      rewrite -{1}[k]Z.succ_pred Z2Nat.inj_succ //.
  Qed.

  Lemma insertZ_cons_z {A} x x' (xs : list A) :
    <[ 0 := x' ]> (x :: xs) = x' :: xs.
  Proof. by rewrite insertZ_cons_iff bool_decide_eq_true_2. Qed.

  Lemma insertZ_cons_nz {A} x x' (xs : list A) (k : Z) (Hk : k <> 0) :
    <[ k := x' ]> (x :: xs) = x :: <[ k - 1 := x']> xs.
  Proof. by rewrite insertZ_cons_iff bool_decide_eq_false_2. Qed.

  Lemma insertZ_app_iff {A} x' (xs xs' : list A) (k : Z) :
    <[ k := x' ]> (xs ++ xs') =
      if bool_decide (k < lengthZ xs)
        then ((<[ k := x' ]> xs) ++ xs')
        else (xs ++ <[ k - lengthZ xs := x']> xs').
  Proof.
    case: bool_decide_reflect => [|/Z.nlt_ge/Z.ge_le_iff] Hlt.
    - rewrite /insert /list_insertZ.
      case: bool_decide_reflect => Hk //.
      have ? : (Z.to_nat k < length xs)%nat by move: Hlt; rewrite /lengthN; lia.
      by rewrite insert_app_l.
    - rewrite /insert /list_insertZ.
      have ? : (0 ≤ k) by lia.
      have Hk : (0 ≤ k - lengthZ xs) by lia.
      have ? : (0 ≤ k - length xs) by move: Hk; rewrite /lengthN; lia.
      have ? : (0 ≤ lengthZ xs) by lia.
      have ? : (0 ≤ length xs) by lia.
      rewrite !bool_decide_eq_true_2 // -insert_app_r //.
      rewrite /lengthN nat_N_Z // -[X in (X + _)%nat]Nat2Z.id -Z2Nat.inj_add // Zplus_minus //.
  Qed.

  Lemma insertZ_app_l {A} x' (xs xs' : list A) (k : Z) (Hk : k < lengthZ xs) :
    <[ k := x' ]> (xs ++ xs') = ((<[ k := x' ]> xs) ++ xs').
  Proof. by rewrite insertZ_app_iff bool_decide_eq_true_2. Qed.

  Lemma insertZ_app_r {A} x' (xs xs' : list A) (k : Z) (Hk : lengthZ xs ≤ k) :
    <[ k := x' ]> (xs ++ xs') =
      (xs ++ <[ k - lengthZ xs := x']> xs').
  Proof. by rewrite insertZ_app_iff bool_decide_eq_false_2 // Z.nlt_ge. Qed.

  #[local] Lemma bool_decide_refl `{HR : Reflexive A R} (x : A) `{!Decision (R x x)} :
    bool_decide (R x x) = true.
  Proof. by apply bool_decide_eq_true_2. Qed.

  #[local] Lemma bool_decide_sub_move_0_r (x y : Z) :
    bool_decide (x - y = 0) = bool_decide (x = y).
  Proof. by apply bool_decide_ext, Z.sub_move_0_r. Qed.

  #[local] Lemma bool_decide_lt_irrefl (x : Z) :
    bool_decide (x < x) = false.
  Proof. by apply bool_decide_eq_false_2, Z.lt_irrefl. Qed.

  (** [Zarith_simpl] simplifies arithmetic expressions of the form:
   *    - [x - x]
   *    - [0 - x]
   *    - [x - 0]
   *    - [bool_decide (x - y = 0)] (it becomes [bool_decide (x = y)])
   *    - [x + 0]
   *    - [0 + x]
   *    - [x `min` x]
   *    - [x `min` y = x]
   *    - [x `min` y = y]
   *    - [x `max` x]
   *    - [x `max` y = x]
   *    - [bool_decide (R x x)] for any reflexive relation [R]
   *    - [bool_decide (x < x)]
   *
   * Those lemmas, in combination with definition by case of [insertZ] and [lookupZ],
   * help normalize the list indices and conditions about list indices.
   *)
  Definition Zarith_simpl :=
    (Z.sub_diag, Z.sub_0_l, Z.sub_0_r,
     @bool_decide_sub_move_0_r,
     Z.add_0_l, Z.add_0_r,
     Z.min_id, Z.min_l_iff, Z.min_r_iff,
     Z.max_id, Z.max_l_iff, Z.max_r_iff,
     @bool_decide_refl,
     @bool_decide_lt_irrefl
    ).

  Lemma takeZ_map {A B} n (f : A -> B) (xs : list A) :
    takeZ n (map f xs) = map f (takeZ n xs).
  Proof. by rewrite /takeZ takeN_map. Qed.

  Lemma takeZ_fmap {A B} n (f : A -> B) (xs : list A) :
    takeZ n (fmap f xs) = fmap f (takeZ n xs).
  Proof. by rewrite /takeZ takeN_map. Qed.

  Lemma dropZ_map {A B} n (f : A -> B) (xs : list A) :
    dropZ n (map f xs) = map f (dropZ n xs).
  Proof. by rewrite /dropZ dropN_map. Qed.

  Lemma dropZ_fmap {A B} n (f : A -> B) (xs : list A) :
    dropZ n (fmap f xs) = fmap f (dropZ n xs).
  Proof. by rewrite /dropZ dropN_map. Qed.

  Lemma takeZ_reverse {A} n (xs : list A) :
    takeZ n (reverse xs) = reverse (dropZ (lengthZ xs - n)%Z xs).
  Proof.
    rewrite /takeZ/dropZ.
    have [Hn|Hn] : (n ≤ 0 ∨ 0 ≤ n)%Z by lia.
    { have Hn' : Z.to_N n = 0%N by lia.
      rewrite Hn' takeN_zero dropN_lengthN //; lia. }
    rewrite takeN_reverse; do 2 f_equiv.
    lia.
  Qed.

  Lemma dropZ_reverse {A} n (xs : list A) :
    dropZ n (reverse xs) = reverse (takeZ (lengthZ xs - n)%Z xs).
  Proof.
    rewrite -[X in takeZ _ X]reverse_involutive takeZ_reverse reverse_involutive.
    by rewrite lengthN_reverse Z.sub_sub_distr Z.sub_diag Z.add_0_l.
  Qed.

  Lemma insertZ_nil {A} (i : Z) (x : A) : <[i:=x]>[] = [].
  Proof. rewrite /insert /list_insertZ; case: bool_decide_reflect => //. Qed.

  Lemma lengthN_insertZ {A} (i : Z) (x : A) (xs : list A) :
    lengthN (<[i:=x]> xs) = lengthN xs.
  Proof.
    rewrite /lengthN /insert /list_insertZ.
    case: bool_decide_reflect => [Hnneg|//].
    by rewrite length_insert.
  Qed.

  Lemma insertZ_oob {A} (i : Z) (x : A) (xs : list A) (Hi : (i < 0 ∨ lengthZ xs ≤ i)) :
    <[i:=x]> xs = xs.
  Proof.
    rewrite /insert /list_insertZ.
    case: Hi => [/Zlt_not_le|] Hi.
    - by rewrite bool_decide_eq_false_2.
    - move: Hi; rewrite /lengthN => Hi.
      rewrite list_insert_ge; last lia.
      by case: bool_decide_reflect.
  Qed.

  Definition insertZ_simpl :=
    (@insertZ_nil, @lengthN_insertZ, @insertZ_cons_iff, @insertZ_app_iff, Zarith_simpl).

  Definition lengthN_simplZ :=
    (@lengthN_insertZ, @lengthN_simpl, Zarith_simpl).

  Lemma lookupZ_Some_to_nat {A} (xs : list A) (k : Z) x :
    xs !! k = Some x <-> (0 ≤ k) ∧ xs !! Z.to_nat k = Some x.
  Proof.
    rewrite {1}/lookup.
    elim: xs k => [|x0 xs IH] k /=.
    - rewrite lookup_nil. by intuition.
    - rewrite lookup_cons.
      case: Z.compare_spec => Hk.
      + rewrite Hk/=; by intuition.
      + rewrite Z2Nat.nonpos; last lia.
        intuition => //; lia.
      + rewrite {}IH.
        rewrite {4}[k]Zsucc_pred Z2Nat.inj_succ; last lia.
        f_equiv; split; lia.
  Qed.

  Lemma lookupZ_Some_to_N {A} (xs : list A) (k : Z) x :
    xs !! k = Some x <-> (0 ≤ k) ∧ xs !! Z.to_N k = Some x.
  Proof. by rewrite lookupZ_Some_to_nat /lookupN /list_lookupN Z_N_nat. Qed.

  Lemma and_ex {A} (P : Prop) (Q : A -> Prop) : P ∧ ex Q ↔ ∃ x, P ∧ Q x.
  Proof. firstorder. Qed.

  Lemma lookupZ_None {A} (xs : list A) (k : Z) :
    xs !! k = None <-> (k < 0 ∨ lengthZ xs ≤ k).
  Proof.
    rewrite -[X in _ <-> X]dec_stable_iff eq_None_not_Some/is_Some.
    apply not_iff_compat.
    etrans; first apply Morphisms_Prop.ex_iff_morphism => a.
    { apply lookupZ_Some_to_N. }
    rewrite not_or Z.nlt_ge Z.nle_gt.
    rewrite -and_ex -[ex _]lookupN_is_Some.
    split; lia.
  Qed.

  Lemma lookupZ_None_inv {A} (xs : list A) (k : Z) :
    None = xs !! k <-> (k < 0 ∨ lengthZ xs ≤ k).
  Proof. by rewrite [X in X ↔ _]symmetry_iff lookupZ_None. Qed.

  Lemma lookupZ_is_Some {A} (xs : list A) (k : Z) :
    is_Some (xs !! k) <-> (0 ≤ k < lengthZ xs).
  Proof. by rewrite -not_eq_None_Some lookupZ_None not_or Z.nlt_ge Z.nle_gt. Qed.

  Lemma lookupZ_nil {A} (k : Z) :
    @nil A !! k = None.
  Proof.
    by rewrite /lookup /list_lookupZ /=.
  Qed.

  Lemma lookupZ_app {A} (xs xs' : list A) (k : Z) :
    (xs ++ xs') !! k =
      if bool_decide (k < lengthZ xs)
        then xs !! k
        else xs' !! (k - lengthZ xs).
  Proof.
    rewrite option_eq => x.
    rewrite lookupZ_Some_to_N.
    case: bool_decide_reflect => [|] Hk.
    - rewrite lookupZ_Some_to_N; apply and_proper_r => Hnneg.
      rewrite lookupN_app_l //; lia.
    - have ? : (Z.to_N k >= lengthN xs)%N by lia.
      have ? : (0 ≤ lengthZ xs) by lia.
      rewrite lookupZ_Some_to_N lookupN_app_r //.
      rewrite Z2N.inj_sub // N2Z.id.
      f_equiv; lia.
  Qed.

  Lemma lookupZ_cons {A} x (xs : list A) (k : Z) :
    (x :: xs) !! k =
      if bool_decide (k = 0)
        then Some x
        else xs !! (k - 1).
  Proof.
    case: bool_decide_reflect => [->|?].
    - rewrite lookupZ_Some_to_nat //=.
    - rewrite option_eq => x'.
      have Hiff : (0 ≤ k <-> 0 ≤ k - 1) by lia.
      rewrite !lookupZ_Some_to_nat Hiff -{2}[k]Z.succ_pred.
      apply and_proper_r => Hk.
      rewrite Z2Nat.inj_succ //.
  Qed.

  Lemma list_lookupZ_eq_list_lookup {A} (xs : list A) (i : Z) :
    xs !! i = if bool_decide (0 ≤ i)%Z then xs !! (Z.to_nat i) else None.
  Proof.
    apply option_eq => b.
    rewrite lookupZ_Some_to_nat.
    rewrite -[X in X ∧ _]bool_decide_eq_true.
    case: bool_decide; intuition; discriminate.
  Qed.

  Lemma list_lookupZ_fmap {A B} (f : A -> B) (xs : list A) (i : Z) :
    (f <$> xs) !! i = f <$> xs !! i.
  Proof.
    rewrite 2!list_lookupZ_eq_list_lookup list_lookup_fmap.
    by case bool_decide.
  Qed.

  Ltac simpl_decide :=
    repeat
      lazymatch goal with
      | H : ?P |- context [ bool_decide ?P ] =>
          rewrite (bool_decide_eq_true_2 _ H)
      | H : ¬ ?P |- context [ bool_decide ?P ] =>
          rewrite (bool_decide_eq_false_2 _ H)
      end.

  Ltac simpl_decide_with tac :=
    repeat
      match goal with
      | |- context [ bool_decide ?P ] =>
          let H := fresh in
          first
            [ assert (H : P) ;
              [ tac | rewrite (bool_decide_eq_true_2 _ H) {H} ]
            | assert (H : ¬ P) ;
              [ tac | rewrite (bool_decide_eq_false_2 _ H) {H} ] ]
      end.

  Lemma lookupZ_snoc {A} x (xs : list A) (k : Z) :
    (xs ++ [x]) !! k =
      if bool_decide (k = lengthZ xs)
        then Some x
        else xs !! k.
  Proof.
    rewrite lookupZ_app lookupZ_cons lookupZ_nil.
    case: (Z.lt_total k (lengthZ xs)) => [Hk_len|[Hk_len|Hk_len]].
    - by simpl_decide_with lia.
    - by simpl_decide_with lia.
    - simpl_decide_with lia.
      rewrite symmetry_iff lookupZ_None; lia.
  Qed.

  Lemma elem_of_if_lookupZ_Some {A} {x : A} {xs : list A} (k : Z) : xs !! k = Some x -> x ∈ xs.
  Proof. rewrite lookupZ_Some_to_nat => - [?]; apply elem_of_list_lookup_2. Qed.

  Lemma lookupZ_is_Some_iff {A} x (xs : list A) : (∃ k : Z, xs !! k = Some x) <-> x ∈ xs.
  Proof.
    split.
    - move => [k]; apply elem_of_if_lookupZ_Some.
    - move => /elem_of_list_lookup [i Hxs].
      exists (Z.of_nat i); rewrite lookupZ_Some_to_nat Nat2Z.id.
      by split; [lia |].
  Qed.

  Lemma lookupZ_insertZ {A} x (xs : list A) (k k' : Z) :
    <[ k' := x ]> xs !! k =
      if bool_decide (k = k' ∧ 0 ≤ k < lengthZ xs)
        then Some x
        else xs !! k.
  Proof.
    case: bool_decide_reflect.
    - rewrite /lengthN => - [] <- [? ?].
      rewrite /insert /list_insertZ lookupZ_Some_to_nat.
      rewrite bool_decide_eq_true_2 // list_lookup_insert //.
      lia.
    - rewrite !not_and_l Z.nlt_ge insertZ_eq_insertN.
      case: bool_decide_reflect => // ? [Hk|[Hneg|Hlen]].
      + rewrite option_eq => x'; rewrite 2!lookupZ_Some_to_N.
        apply and_proper_r => Hk0.
        have ? :  Z.to_N k' ≠ Z.to_N k by lia.
        by rewrite lookupN_insertN_neq.
      + rewrite option_eq => x'; rewrite 2!lookupZ_Some_to_N.
        apply and_proper_r => Hk0.
        have ? :  Z.to_N k' ≠ Z.to_N k by lia.
        by rewrite lookupN_insertN_neq.
      + rewrite option_eq => x'; rewrite 2!lookupZ_Some_to_nat.
        move: Hlen; rewrite -lengthN_fold => Hlen.
        rewrite !(lookup_ge_None_2, length_insert) //; lia.
  Qed.

  Lemma lookupZ_insertZ_eq {A} x (xs : list A) (k : Z)
       (Hk : 0 ≤ k < lengthZ xs) :
    <[ k := x ]> xs !! k = Some x.
  Proof. rewrite lookupZ_insertZ bool_decide_eq_true_2 //. Qed.

  Lemma lookupZ_insertZ_neq {A} x (xs : list A) (k k' : Z)
        (Hkk' : k ≠ k') :
    <[ k := x ]> xs !! k' = xs !! k'.
  Proof. by rewrite lookupZ_insertZ bool_decide_eq_false_2 // not_and_l; left. Qed.

  Lemma insertZ_id {A} (xs : list A) (i : Z) x (Hx : xs !! i = Some x) :
    <[ i := x ]> xs = xs.
  Proof.
    move: Hx; rewrite lookupZ_Some_to_nat /insert /list_insertZ => - [Hi Hx].
    by rewrite bool_decide_eq_true_2 // list_insert_id.
  Qed.

  Lemma lookupZ_singleton_Some {A} (x y : A) (k : Z) :
    [x] !! k = Some y <-> x = y ∧ k = 0.
  Proof.
    rewrite !(lookupZ_cons, lookupZ_nil).
    case: bool_decide_reflect.
    - move => ->; rewrite inj_iff; split => [|[]] //.
    - split => [|[]] //.
  Qed.

  Definition lookupZ_simpl :=
    (@lookupZ_singleton_Some, @lookupZ_cons, @lookupZ_app, @lookupZ_nil, @lookupZ_insertZ,
       @lookupZ_None, @lookupZ_None_inv, @lookupZ_is_Some, Zarith_simpl).

End listZ.

Section rangeZ.
  #[local] Open Scope Z_scope.

  #[local] Definition rangeZ' (from : Z) (to : N) : list Z :=
    N.peano_rect _
      (fun from => [])
      (fun n' rangeZ' from => from :: rangeZ' (from + 1))
      to from.

  Definition rangeZ (from : Z) (to : Z) : list Z :=
    rangeZ' from (Z.to_N (to - from)).

  Lemma rangeZ_oob from to (Hlt : (to <= from)) : rangeZ from to = [].
  Proof. rewrite /rangeZ Z_to_N_eq_0 //; lia. Qed.

  Lemma rangeZ_nil from : rangeZ from from = [].
  Proof. by rewrite rangeZ_oob. Qed.

  Lemma rangeZ_cons from to (Hlt : (from < to)) :
    rangeZ from to = from :: rangeZ (from + 1) to.
  Proof.
    have ? : 0 ≤ Z.pred (to - from) by lia.
    by rewrite /rangeZ -[(to - from)]Z.succ_pred /rangeZ' !(Z2Nat.inj_succ, Z.sub_succ_r, Z2N.inj_succ, N.peano_rect_succ).
  Qed.

  Lemma rangeZ_app {from} mid {to} (Hfrom_mid : (from ≤ mid)) (Hmid_to : (mid ≤ to)) :
    (rangeZ from mid ++ rangeZ mid to) = rangeZ from to.
  Proof.
    rewrite /rangeZ.
    have {}Hfrom_mid :  (0 ≤ (mid - from)) by lia.
    have {}Hmid_to :  (0 ≤ (to - mid)) by lia.
    have [n Hn] : exists n, n = Z.to_N (mid - from) by exists (Z.to_N (mid - from)).
    have [m Hm] : exists n, n = Z.to_N (to - mid) by exists (Z.to_N (to - mid)).
    have Hmn : (n + m)%N = Z.to_N (to - from) by lia.
    have Hmid : mid = (from + Z.of_N n) by lia.
    rewrite -{}Hmn -{}Hn -{}Hm {}Hmid {mid to Hfrom_mid Hmid_to}.
    elim/N.peano_ind: n from => [|n IH] from /=.
    - by rewrite /= Z.add_0_r.
    - have Hseq_succ x : rangeZ' from (N.succ x) = from :: rangeZ' (from + 1) x
        by rewrite /rangeZ' N.peano_rect_succ.
      rewrite N.add_succ_l !{}Hseq_succ -{}IH.
      by rewrite N2Z.inj_succ -Z.add_1_l Z.add_assoc.
  Qed.

  Lemma rangeZ_snoc from to (Hlt : (from < to)) :
    rangeZ from to = (rangeZ from (to - 1) ++ [to - 1]).
  Proof.
    have ? :  (from ≤ to - 1) by lia.
    have ? :  (to - 1 ≤ to)   by lia.
    have ? :  (to - 1 < to)   by lia.
    by rewrite -(rangeZ_app (to - 1)) // !(rangeZ_cons (to - 1), Z.sub_add, rangeZ_nil).
  Qed.

  Lemma lengthN_rangeZ from to :
    lengthN (rangeZ from to) = Z.to_N (to - from).
  Proof.
    have [Hle|Hle] : (to <= from ∨ from ≤ to) by lia.
    - have ? : (to - from <= 0) by lia.
      by rewrite !(rangeZ_oob, Z_to_N_eq_0, lengthN_nil).
    - elim/Zlt_lower_bound_ind: Hle => {}to IH Hle.
      have {Hle} [<-|Hlt] : from = to ∨ (from < to) by lia.
      { rewrite rangeZ_nil Z.sub_diag lengthN_nil //. }
      have ? : (from <= to - 1 < to) by lia.
      rewrite rangeZ_snoc // !lengthN_simplZ {}IH // -[1%N] /(Z.to_N 1).
      lia.
  Qed.

  Lemma lookupZ_rangeZ i j k x : rangeZ i k !! j = Some x <-> (i ≤ x < k ∧ x = i + j)%Z.
  Proof.
    case: (Z.le_ge_cases k i).
    { move => Hji; rewrite rangeZ_oob // lookupZ_nil; split; [discriminate | lia]. }
    move => Hle.
    elim/Zlt_lower_bound_ind: Hle j => {}k IH Hle j.
    move: (Zle_lt_or_eq _ _ Hle) => /or_comm [|Hlt].
    { move => <-. rewrite rangeZ_nil lookupZ_nil; split; [discriminate | lia]. }
    rewrite rangeZ_snoc // lookupZ_snoc lengthN_rangeZ Z2N.id; last lia.
    case: bool_decide_reflect.
    - move => ->; rewrite inj_iff; lia.
    - move => Hj; rewrite IH; lia.
  Qed.

  Import under_rel_proper.

  Lemma elem_of_rangeZ x i j : x ∈ rangeZ i j <-> (i ≤ x < j).
  Proof.
    rewrite -lookupZ_is_Some_iff.
    under Morphisms_Prop.ex_iff_morphism => k
      do rewrite lookupZ_rangeZ.
    split; [case| exists (x - i)]; lia.
  Qed.

  Lemma NoDup_rangeZ i j : NoDup (rangeZ i j).
  Proof.
    case: (Z.le_ge_cases j i).
    { move => Hji; rewrite rangeZ_oob // elem_of_nil; lia. }
    move => Hle.
    elim/Zlt_lower_bound_ind: Hle => {}j IH Hle.
    move: (Zle_lt_or_eq _ _ Hle) => /or_comm [|Hlt].
    { move => <-; rewrite rangeZ_nil //. }
    rewrite rangeZ_snoc // Permutation_app_comm /=.
    constructor.
    - rewrite elem_of_rangeZ; lia.
    - apply: IH; lia.
  Qed.

  Lemma rangeZ_nil_inv i j : rangeZ i j = [] <-> j ≤ i.
  Proof.
    split.
    - case: (Z.lt_ge_cases i j) => Hij.
      + by rewrite rangeZ_cons // => [=].
      + by rewrite rangeZ_oob.
    - by move => Hrng; rewrite rangeZ_oob.
  Qed.

  Lemma rangeZ_cons_inv i j x xs : rangeZ i j = x :: xs <-> i < j ∧ i = x ∧ rangeZ (i+1) j = xs.
  Proof.
    split.
    - case: (Z.lt_ge_cases i j) => Hij.
      + by rewrite rangeZ_cons // => [=].
      + by rewrite rangeZ_oob.
    - move => - [Hij [] Hxi Hrng].
      by rewrite rangeZ_cons // -Hxi Hrng.
  Qed.

  Lemma rangeZ_app_inv i j xs0 xs1 :
    rangeZ i j = xs0 ++ xs1 <->
    j < i ∧ xs0 = [] ∧ xs1 = [] ∨
    ∃ k, i ≤ k ∧ rangeZ i k = xs0 ∧
         k ≤ j ∧ rangeZ k j = xs1.
  Proof.
    elim: xs0 i => [|x xs0 IH] i.
    - cbn; split.
      + intros Hxs1.
        case: (Z.lt_ge_cases j i) => Hij; [left|right].
        { move: Hxs1; rewrite rangeZ_oob //; lia. }
        exists i; rewrite rangeZ_nil Hxs1 //.
      + move => [[Hoob [] ? ->] | [k [] Hik [] Hrng_ik [] Hkj <-]].
        * rewrite rangeZ_oob //; lia.
        * move: Hrng_ik; rewrite rangeZ_nil_inv => Hki.
          by have <- : i = k by lia.
    - rewrite /= rangeZ_cons_inv {}IH.
      split.
      + move => [?] [?] [?|]; first lia.
        move => [k] [Hik] [Hrng_ik] [Hkj Hrng_kj].
        right; exists k. rewrite rangeZ_cons_inv Hrng_ik Hrng_kj.
        repeat split; lia.
      + move => [[?] [//] | [k] [Hik] [+] [Hkj Hrng_kj]].
        rewrite rangeZ_cons_inv => - [{}Hik] [<-] Hrng_ik.
        split; [lia| split; [done|right]].
        exists k. rewrite Hrng_kj Hrng_ik; split => //; lia.
  Qed.

End rangeZ.

Section sliceZ.
  #[local] Open Scope Z_scope.

  Definition sliceZ {A} (base i j : Z) (xs : list A) : list A :=
    dropN (Z.to_N (i - base)) (takeN (Z.to_N (j - base)) xs).

  Lemma sliceZ_crop_l {A} (base i j : Z) (xs : list A) :
    sliceZ base i j xs = sliceZ base (i `max` base) j xs.
  Proof.
    rewrite /sliceZ -Z.sub_max_distr_r Z.sub_diag Z2N.inj_max /= N.max_0_r; f_equal.
  Qed.

  Lemma sliceZ_crop_r {A} (base i j : Z) (xs : list A) :
    sliceZ base i j xs = sliceZ base i (j `min` (base + lengthN xs)) xs.
  Proof.
    rewrite /sliceZ; f_equal.
    rewrite -Z.sub_min_distr_r Z.add_simpl_l Z2N.inj_min N2Z.id -takeN_takeN.
    rewrite (takeN_lengthN (lengthN xs)) //.
  Qed.

  Lemma sliceZ_crop {A} (base i j : Z) (xs : list A) :
    sliceZ base i j xs = sliceZ base (i `max` base) (j `min` (base + lengthN xs)) xs.
  Proof. by rewrite sliceZ_crop_l sliceZ_crop_r. Qed.

  Lemma lengthN_sliceZ {A} (base i j : Z) (xs : list A)
       (Hi : base ≤ i)
       (Hj : j - base ≤ lengthN xs) :
    lengthN (sliceZ base i j xs) = Z.to_N (j - i).
  Proof.
    have ? : (Z.to_N (j - base) ≤ lengthN xs)%N by lia.
    have ? : 0 <= i - base by lia.
    rewrite /sliceZ lengthN_dropN lengthN_takeN N.min_l // -Z2N.inj_sub //.
    lia.
  Qed.

  Lemma sliceZ_self {A} (base i j : Z) (xs : list A) (Hi : i <= base) (Hj : lengthZ xs ≤ j - base) :
    sliceZ base i j xs = xs.
  Proof.
    have Hi_base : (Z.to_N (i - base)) = 0%N by lia.
    rewrite /sliceZ Hi_base dropN_zero takeN_lengthN //.
    lia.
  Qed.

  Lemma sliceZ_nil {A} (base i j : Z) (xs : list A)
    (Hij : j ≤ i) :
    sliceZ base i j xs = [].
  Proof.
    rewrite /sliceZ; apply dropN_lengthN.
    rewrite lengthN_takeN. lia.
  Qed.

  Lemma insertZ_preserves_sliceZ {A} x (base i j : Z) k (xs : list A)
    (Hx : ¬ i ≤ base + k < j) :
    sliceZ base i j (<[k := x]> xs) = sliceZ base i j xs.
  Proof.
    rewrite /sliceZ.
    case: (Z.le_gt_cases (j - base) k) => [/Z.ge_le_iff Hj_le_k|Hk_lt_j].
    { rewrite insertZ_eq_insertN.
      case: bool_decide_reflect => [Hnneg|//].
      rewrite takeN_insertN_ge //; lia. }
    rewrite insertZ_eq_insertN.
    case: bool_decide_reflect => [Hnneg|//].
    have ? :  (Z.to_N k < Z.to_N (j - base))%N by lia.
    rewrite takeN_insertN_lt //.
    have ? : (Z.to_N k < Z.to_N (i - base))%N by lia.
    rewrite dropN_insertN_lt //; lia.
  Qed.

  Lemma sliceZ_cons {A} x (base i j : Z) (xs : list A)
    (Hi : base <= i)
    (Hij : i < j)
    (Hx : xs !! (i - base) = Some x) :
    sliceZ base i j xs = x :: sliceZ base (i + 1) j xs.
  Proof.
    have Hplus_one : Z.to_N (i + 1 - base) = (Z.to_N (i - base) + 1)%N by lia.
    rewrite /sliceZ Hplus_one -dropN_lookupN //.
    move: Hx; rewrite lookupZ_Some_to_N lookupN_takeN //.
    - by case.
    - lia.
  Qed.

  Lemma sliceZ_snoc {A} x (base i j : Z) (xs : list A)
    (Hbase_j : base < j)
    (Hij : i < j)
    (Hx : xs !! (j - 1 - base) = Some x) :
    sliceZ base i j xs = sliceZ base i (j - 1) xs ++ [x].
  Proof.
    rewrite !(sliceZ_crop_l _ i).
    have {}Hij : i `max` base < j by lia.
    move: (i `max` base) (Z.le_max_r i base) Hij => {}i Hbase_i Hij.
    have ? : 0 ≤ i - base by lia.
    rewrite /sliceZ !dropN_takeN -takeN_S_r.
    - f_equal; lia.
    - move: Hx; rewrite lookupZ_Some_to_N => - [] ? Hx.
      rewrite lookupN_dropN -Hx.
      f_equal; lia.
  Qed.

  Lemma sliceZ_cons_insertZ {A} x (base i j : Z) (xs : list A)
    (Hbase_i : base <= i)
    (Hij : i < j)
    (Hi_len : i < base + lengthZ xs) :
    sliceZ base i j (<[ i - base := x ]> xs) = x :: sliceZ base (i + 1) j xs.
  Proof.
    have ? : (Z.to_N (i - base) < lengthN xs)%N by lia.
    have ? :  ¬ i + 1 ≤ base + (i - base) < j by lia.
    have ? : 0 ≤ i - base < lengthZ xs by lia.
    rewrite (sliceZ_cons x) ?(insertZ_preserves_sliceZ, lookupZ_insertZ_eq) //.
  Qed.

  Lemma sliceZ_snoc_insertZ {A} x (base i j : Z) (xs : list A)
    (Hij : i < j)
    (Hbase_j : base < j)
    (Hj_len : j ≤ base + lengthZ xs) :
    sliceZ base i j (<[ j - 1 - base := x ]> xs) = sliceZ base i (j - 1) xs ++ [x].
  Proof.
    have ? : (j - 1 - base < lengthZ xs) by lia.
    have ? : ¬ i ≤ base + (j - 1 - base) < j - 1 by lia.
    have ? : 0 ≤ j - 1 - base < lengthZ xs by lia.
    rewrite (sliceZ_snoc x) // ?(insertZ_preserves_sliceZ, lookupZ_insertZ_eq) //.
  Qed.

  Lemma sliceZ_app {A} (base i j k : Z) (xs : list A)
    (Hij : i <= j)
    (Hjk : j ≤ k) :
    (sliceZ base i j xs ++ sliceZ base j k xs) = sliceZ base i k xs.
  Proof.
    rewrite !(sliceZ_crop_l _ i) !(sliceZ_crop_r _ _ k).
    case: (Z.le_ge_cases j (i `max` base)) => [Hij'|].
    { rewrite (sliceZ_nil _ _ j) //= (sliceZ_crop_l _ j).
      f_equal; lia. }
    move: (i `max` base) (Z.le_max_r i base) => {}i Hbase_i {}Hij.
    case: (Z.le_ge_cases (k `min` (base + lengthZ xs)) j) => [Hjk'|].
    { rewrite (sliceZ_nil _ j) // app_nil_r (sliceZ_crop_r _ _ j).
      f_equal; lia. }
    move: (k `min` (base + lengthZ xs)) (Z.le_min_r k (base + lengthZ xs)) => {}k Hk_len {}Hjk.

    elim/Zlt_lower_bound_ind: Hjk Hk_len => {}k IH Hjk Hk_len.
    case: (Zle_lt_or_eq _ _ Hjk) IH => [{}Hjk IH | <- _]; first last.
    - by rewrite [X in _ ++ X] sliceZ_nil // app_nil_r.
    - have Hlt : (0 ≤ k - 1 - base < lengthZ xs) by lia.
      move: (Hlt) => /lookupZ_is_Some [x Hx].
      have ? :  base < k by lia.
      have ? :  j ≤ k - 1 < k by lia.
      have ? :  i < k by lia.
      have ? :  k - 1 ≤ base + lengthZ xs by lia.
      rewrite [X in _ ++ X] (sliceZ_snoc x) // assoc IH // -(sliceZ_snoc x) //.
  Qed.

  Lemma sliceZ_explode {A} x (base i j k : Z) (xs : list A)
    (Hx : xs !! (j - base) = Some x)
    (Hbase_j : base ≤ j)
    (Hij : i ≤ j)
    (Hjk : j < k) :
    (sliceZ base i j xs ++ [x] ++ sliceZ base (j + 1) k xs) = sliceZ base i k xs.
  Proof. rewrite /= -sliceZ_cons // sliceZ_app //; lia. Qed.

  Lemma sliceZ_explode_insert {A} x (base i j k : Z) (xs : list A)
    (Hbase_j : base ≤ j)
    (Hij : i ≤ j)
    (Hjk : j < k)
    (Hj_len : j < base + lengthZ xs) :
    (sliceZ base i j xs ++ [x] ++ sliceZ base (j + 1) k xs) = sliceZ base i k (<[ j - base := x]> xs).
  Proof.
    have ? : ((j - base) < lengthZ xs) by lia.
    have ? : ¬ j + 1 ≤ base + (j - base) < k by lia.
    have ? : ¬ i ≤ base + (j - base) < j by lia.
    have ? : 0 ≤ j - base < lengthZ xs by lia.
    rewrite -(sliceZ_explode x _ i j k) ?(lookupZ_insertZ_eq) // !insertZ_preserves_sliceZ //.
  Qed.

  Lemma sliceZ_max_r {A} base i j (xs : list A) :
    sliceZ base i (i `max` j) xs = sliceZ base i j xs.
  Proof.
    case: (Z.le_ge_cases i j) => Hij.
    - rewrite Z.max_r //.
    - rewrite Z.max_l // !sliceZ_nil //.
  Qed.

  Lemma sliceZ_min_l {A} base i j (xs : list A) :
    sliceZ base (i `min` j) j xs = sliceZ base i j xs.
  Proof.
    case: (Z.le_ge_cases i j) => Hij.
    - rewrite Z.min_l //.
    - rewrite Z.min_r // !sliceZ_nil //.
  Qed.

  Lemma takeN_sliceZ {A} base i j k (xs : list A) (Hbase_i : (base ≤ i)) :
    takeN (Z.to_N (j - i)) (sliceZ base i k xs) = sliceZ base i (j `min` k) xs.
  Proof.
    have ? : (0 ≤ i - base) by lia.
    have ? :  (0 ≤ (j - i) `max` 0) by lia.
    have Hi_cancel : ((i - base) + (j - i) = j - base) by lia.
    rewrite -(sliceZ_max_r _ _ k) -(sliceZ_max_r _ _ (j `min` k)) /sliceZ.
    rewrite takeN_dropN_commute takeN_takeN -(Z_to_N_max_0 (j - i)) -Z2N.inj_add //.
    rewrite -Z.add_max_distr_l Hi_cancel Z.add_0_r Z.sub_max_distr_r -Z2N.inj_min.
    by rewrite Z.sub_min_distr_r Z.max_min_distr Z.max_comm.
  Qed.

  Lemma dropN_sliceZ {A} base i j k (xs : list A) (Hbase_i : (base ≤ i)) :
    dropN (Z.to_N (j - i)) (sliceZ base i k xs) = sliceZ base (i `max` j) k xs.
  Proof.
    have ? : (0 ≤ i - base) by lia.
    have Hi_cancel : (j - i + (i - base) = j - base) by lia.
    have ? :  (0 ≤ (j - i) `max` 0) by lia.
    rewrite [X in _ = X]sliceZ_crop_l  /sliceZ dropN_dropN.
    rewrite -!Z.sub_max_distr_r Z.sub_diag Z_to_N_max_0.
    by rewrite -(Z_to_N_max_0 (j - i)) -Z2N.inj_add // -Z.add_max_distr_r Z.add_0_l Hi_cancel Z.max_comm.
  Qed.

  Lemma sliceZ_insertN {A} base i j k (xs : list A) x
          (Hbase_i : (base ≤ i))
          (Hij : (i ≤ j))
          (Hjk : (j < k))
          (Hk_len : (k ≤ base + lengthZ xs)) :
    sliceZ base i k (<[ j - base := x ]> xs) = <[ j - i := x ]> (sliceZ base i k xs).
  Proof.
    have ? :  ¬ (i ≤ base + (j - base) < j) by lia.
    have ? : (i ≤ j + 1) by lia.
    have ? : (j ≤ k) by lia.
    have ? : (0 ≤ j - i) by lia.
    have ? : (Z.to_N (j - i) < Z.to_N (k - i))%N by lia.
    have ? : (base ≤ j) by lia.
    have ? : (j < base + lengthZ xs) by lia.
    have ? : (j - base < lengthZ xs) by lia.
    have ? : (k - base ≤ lengthZ xs) by lia.
    rewrite -(sliceZ_app _ _ j) // insertZ_preserves_sliceZ // sliceZ_cons_insertZ //.
    rewrite insertZ_eq_insertN insertN_takeN_dropN ?lengthN_sliceZ //.
    rewrite N.add_1_r -Z2N.inj_succ // Zminus_succ_l -Z.add_1_r.
    rewrite takeN_sliceZ // dropN_sliceZ // Z.min_l // Z.max_r //.
    by rewrite bool_decide_eq_true_2.
  Qed.

  Lemma lengthN_sliceZ_le {A} (base i j : Z) (xs : list A) :
    (lengthN (sliceZ base i j xs) ≤ lengthN xs)%N.
  Proof. rewrite sliceZ_crop lengthN_sliceZ; lia. Qed.

  Lemma lengthZ_sliceZ_iff {A} (base i j : Z) (xs : list A) :
    lengthZ (sliceZ base i j xs) = j - i <-> i = j ∨ base ≤ i ∧ i < j ∧ j ≤ base + lengthN xs.
  Proof.
    split => [|[]].
    - move => Hlen.
      move: Hlen; rewrite sliceZ_crop Z.min_comm.
      case: (Z.max_spec i base);
        case: (Z.min_spec (base + lengthZ xs) j)
          => - [] Hj_len -> [] Hbase_i ->;
            rewrite lengthN_sliceZ //; try lia.
    - move => <-.
      rewrite Z.sub_diag sliceZ_crop lengthN_sliceZ; [|lia|lia].
      rewrite Z_of_N_Zto_N_eq_max Z.max_r // Z.le_sub_0.
      trans i => //; [apply Z.le_min_l | apply Z.le_max_l].
    - move => [Hbase_i] [Hij Hj_len].
      have ? : j - base ≤ lengthZ xs by lia.
      have ? : 0 ≤ j - i by lia.
      rewrite lengthN_sliceZ // Z2N.id //.
  Qed.

End sliceZ.

#[global] Hint Opaque sliceZ : typeclass_instances sl_opacity.
