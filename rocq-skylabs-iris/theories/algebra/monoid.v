(*
 * Copyright (C) 2021-2022 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Export iris.algebra.monoid.

Require Import skylabs.prelude.reserved_notation.
Require Import skylabs.prelude.numbers.

(** * Powers in monoids *)
(** Overview:

- [monoid_instances] importable hints

- [power o x n], with notation [x ^^{o} n], for any declared monoid
operation [o : M -> M -> M], [x : M], [n : N]

Elsewhere, we relate powers to big ops, make [P ^^ n] notation for
powers using [**], and relate [P q ^^ n] to [P (q * n)] for fractional
assertions [P].

*)

(** Importable hints *)

Module Import monoid_instances.

  #[export] Hint Resolve
    monoid_ne monoid_proper
    monoid_assoc monoid_comm
    monoid_left_id monoid_right_id
  : typeclass_instances.

End monoid_instances.

(** Powers *)

Definition power `{Monoid M o} (x : M) (n : N) : M := N.iter n (o x) monoid_unit.
#[global] Arguments power {_ _} o {_} _ !_ / : assert.
#[global] Instance: Params (@power) 4 := {}.
#[global] Hint Opaque power : typeclass_instances sl_opacity.

#[global] Notation "x ^^{ o } n" := (power o x n) : stdpp_scope.

#[local] Notation "R≡" := (X in _ ≡ X)%pattern.

Section power.
  Context `{Monoid M o}.
  Implicit Types (x : M) (n : N).
  #[local] Infix "`o`" := o (at level 50, left associativity).
  #[local] Open Scope N_scope.

  Lemma power_0 x : x ^^{o} 0 = monoid_unit.
  Proof. done. Qed.

  Lemma power_1 x : x ^^{o} 1 ≡ x.
  Proof. exact: right_id. Qed.

  Lemma power_succ x n : x ^^{o} N.succ n = x `o` x ^^{o} n.
  Proof. rewrite /power. by rewrite N.iter_succ. Qed.

  Lemma power_proper (R : relation M) :
    Reflexive R ->
    Proper (R ==> R ==> R) o ->
    Proper (R ==> eq ==> R) (power o).
  Proof.
    intros ? Hop x1 x2 ? n ? <-. elim/N.peano_ind: n =>// n ?.
    rewrite !power_succ. by apply Hop.
  Qed.

  #[global] Instance power_ne (n : SI) : Proper (dist n ==> eq ==> dist n) (power o).
  Proof. apply: power_proper. Qed.
  #[global] Instance power_proper' : Proper (equiv ==> eq ==> equiv) (power o).
  Proof. apply: power_proper. Qed.

  Lemma power_closed (P : M -> Prop) x n :
    P monoid_unit -> (∀ x1 x2, P x1 -> P x2 -> P (x1 `o` x2)) ->
    P x -> P (x ^^{o} n).
  Proof.
    intros ? Hop ?. induction n using N.peano_ind; first done.
    rewrite power_succ. exact: Hop.
  Qed.

  Lemma power_closed_nonzero (P : M -> Prop) x n :
    Proper (equiv ==> iff) P ->
    n <> 0 ->
    (∀ x1 x2, P x1 -> P x2 -> P (o x1 x2)) ->
    P x -> P (x ^^{o} n).
  Proof.
    intros ? Hnz Hop ?. destruct n as [|p]; [done|clear Hnz].
    induction p using Pos.peano_ind; first by rewrite power_1.
    rewrite -N.succ_pos_pred Pos.pred_N_succ power_succ. exact: Hop.
  Qed.

  Lemma power_unit n : monoid_unit ^^{o} n ≡ monoid_unit.
  Proof. elim/N.peano_ind: n => //= n IH. by rewrite power_succ IH right_id. Qed.

  Lemma power_add x n1 n2 : x ^^{o} (n1 + n2) ≡ x ^^{o} n1 `o` x ^^{o} n2.
  Proof.
    induction n1 as [|n1 IH] using N.peano_ind.
    - by rewrite left_id_L /= left_id.
    - rewrite N.add_succ_l !power_succ. by rewrite IH assoc.
  Qed.

  Lemma power_op x y n : (x `o` y) ^^{o} n ≡ (x ^^{o} n) `o` (y ^^{o} n).
  Proof.
    induction n as [|n IH] using N.peano_ind.
    - by rewrite !power_0 left_id.
    - rewrite !power_succ IH. rewrite [y `o` _]comm -!assoc.
      by do 2!rewrite [(_ ^^{o} _) `o` _ in R≡]comm -assoc.
  Qed.

  Lemma power_mul n1 n2 x : x ^^{o} (n1 * n2) ≡ (x ^^{o} n1) ^^{o} n2.
  Proof.
    revert n2. induction n1 as [|n1 IH] using N.peano_ind=>n2.
    - by rewrite left_absorb_L !power_0 power_unit.
    - rewrite N.mul_succ_l power_add.
      rewrite IH -power_op. by rewrite comm -power_succ.
  Qed.

End power.
