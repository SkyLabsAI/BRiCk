(*
 * Copyright (C) 2020-2022 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bluerock.iris.extra.bi.prelude.
Require Import bluerock.iris.extra.bi.big_op.
Require Import bluerock.iris.extra.proofmode.proofmode.
Import ChargeNotation.

#[local] Set Primitive Projections.
#[local] Open Scope N_scope.

(** * Spec building block: Contender tokens *)

(**
Contender tokens enable verified code to limit the number of
contenders racing to call some method. Contender tokens are relevant
to, e.g., ticket locks with finitely many tickets.
*)

(**
[P n] represents [n] contender tokens. It's important that we use [n :
N] rather than [n : nat] for specs that cough up, e.g., [contender γ
INT_MAX].
*)
Class ContenderToken {PROP : bi} (P : N → PROP) : Prop := {
  #[global] contender_timeless n :: Timeless (P n);
  #[global] contender_affine   n :: Affine (P n);

  (**
  [contender_op] or the derived rule [contender_alloc] are used to
  split off individual contender tokens.

  _Example:_ Suppose there are 8 cores and ticket lock tickets occupy
  16 bits. When an initializing core A allocates a lock, it gets a
  bunch of contender tokens, written [contender γ (2 ^ 16 - 1)]. When
  A informs some other core B about this lock, A has [n ≠ 0] tokens
  left and peels off a single token using [contender_alloc]. A passes
  [contender γ 1] to B and keeps the remaining [n - 1] tokens. After
  doling out a token per core in this way, A can discard the remaining
  [2 ^ 16 - 9] tokens.
  *)
  contender_op n1 n2 : P (n1 + n2) -|- P n1 ** P n2;
}.

Section with_contender.
  Context {PROP : bi} {P : N -> PROP} `{CT : !ContenderToken P}.
  #[local] Set Default Proof Using "CT".

  Lemma contender_alloc (n : N) :
    n ≠ 0 → P n -|- P (N.pred n) ** P 1.
  Proof.
    intros. have {1}-> : (n = N.pred n + 1)%N by lia. exact: contender_op.
  Qed.

  Lemma contender_allocN (tk c : N) :
    (tk <= c)%N ->
    P c -|- P (c - tk) ** P tk.
  Proof.
    intros. have {1}->: (c = (c - tk) + tk)%N by lia. exact: contender_op.
  Qed.

  Lemma contender_split (n : N) :
    P n -|- P 0 ** P 1 ^^ n.
  Proof.
    induction n as [|n IH] using N.peano_ind.
    - by rewrite power_0 right_id.
    - by rewrite -N.add_1_r contender_op power_add power_1 IH assoc.
  Qed.

  Lemma contender_split_leaking_0 (n : N) :
    P n |-- P 1 ^^ n.
  Proof. rewrite contender_split. iIntros "[? $]". Qed.

  (** Proof mode *)
  #[global] Instance contender_into_sep n1 n2 :
    IntoSep (P (n1 + n2)) (P n1) (P n2).
  Proof. by rewrite /IntoSep contender_op. Qed.
  #[global] Instance contender_from_sep n1 n2 :
    FromSep (P (n1 + n2)) (P n1) (P n2).
  Proof. by rewrite /FromSep contender_op. Qed.
  #[global] Instance contender_combine_sep_as n1 n2 :
    CombineSepAs (P n1) (P n2) (P (n1 + n2)).
  Proof. by rewrite /CombineSepAs contender_op. Qed.

End with_contender.

#[global] Instance ContenderToken_sep {PROP : bi} (P Q : N -> PROP) :
  ContenderToken P -> ContenderToken Q ->
  ContenderToken (funI n => P n ** Q n).
Proof.
  constructor; [apply _..|].
  intros n1 n2. trans ((P n1 ** P n2) ** (Q n1 ** Q n2)).
  - by rewrite !contender_op.
  - rewrite !bi.sep_assoc. rewrite -(bi.sep_assoc (P n1) (P n2) (Q n1)).
    rewrite (bi.sep_comm (P n2) (Q n1)). by rewrite bi.sep_assoc.
Qed.
