(*
 * Copyright (c) 2022 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bluerock.iris.extra.bi.split_frac.

(**
[Split q q1 q2] succeeds if [SplitFrac q] outputs [q1], [q2].
*)
Class Split (q q1 q2 : Qp) : Prop := split : SplitFrac q q1 q2.
#[global] Hint Mode Split + + + : typeclass_instances.
#[global] Instance split_frac q q'1 q'2 q1 q2 :
  SplitFrac q q'1 q'2 -> TCEq q1 q'1 -> TCEq q2 q'2 -> Split q q1 q2 | 10.
Proof. by rewrite !TCEq_eq=>? ->->. Qed.

Section split.

  (** Base cases *)

  Lemma add p q : Split (p + q) p q.
  Proof. apply _. Abort.
  Lemma mul_2 q : Split (2 * q) q q.
  Proof. apply _. Abort.
  Lemma mul_2 q : Split (q * 2) q q.
  Proof. apply _. Abort.
  Lemma mul_4 q : Split (4 * q) (2 * q) (2 * q).
  Proof. apply _. Abort.
  Lemma mul_4 q : Split (q * 4) (q * 2) (q * 2).
  Proof. apply _. Abort.

  (** Splitting on subterms of [*] *)

  Lemma mul_l p1 p2 q : Split ((p1 + p2) * q) (p1 * q) (p2 * q).
  Proof. apply _. Abort.
  Lemma mul_r p q1 q2 : Split (p * (q1 + q2)) (p * q1) (p * q2).
  Proof. apply _. Abort.
  Lemma mul_prefer_l p1 p2 q1 q2 :
    Split ((p1 + p2) * (q1 + q2)) (p1 * (q1 + q2)) (p2 * (q1 + q2)).
  Proof. apply _. Abort.

  Lemma mul_default p q : Split (p * q) ((p * q)/2) ((p * q)/2).
  Proof. apply _. Abort.

  (** Splitting on subterms of [/] *)

  Lemma div_l p1 p2 q : Split ((p1 + p2) / q) (p1 / q) (p2 / q).
  Proof. apply _. Abort.
  Lemma div_r_default p q1 q2 :
    Split (p / (q1 + q2)) (p / ((q1 + q2) * 2)) (p / ((q1 + q2) * 2)).
  Proof. apply _. Abort.
  Lemma div_l_example p1 p2 q1 q2 :
    Split ((p1 + p2) / (q1 + q2)) (p1 / (q1 + q2)) (p2 / (q1 + q2)).
  Proof. apply _. Abort.

  Lemma div_default p q : Split (p / q) (p / (q * 2)) (p / (q * 2)).
  Proof. apply _. Abort.

  (** Division by two *)

  Lemma default : Split 1 (1/2) (1/2).
  Proof. apply _. Abort.
  Lemma default q : Split q (q/2) (q/2).
  Proof. apply _. Abort.
  Lemma default : Split (1/2) (1/4) (1/4).
  Proof. apply _. Abort.
  Lemma default q : Split (q/2) (q/4) (q/4).
  Proof. apply _. Abort.

End split.

(**
[Combine q1 q2 q] succeeds if [CombineFrac q1 q2] outputs [q].
*)
Class Combine (q1 q2 q : Qp) : Prop := combine : CombineFrac q1 q2 q.
#[global] Hint Mode Combine + + + : typeclass_instances.
#[global] Instance combine_frac q1 q2 q' q :
  CombineFrac q1 q2 q' -> TCEq q q' -> Combine q1 q2 q | 10.
Proof. by rewrite TCEq_eq=>? ->. Qed.

Section combine.

  Lemma diag q : Combine q q (2 * q).
  Proof. apply _. Abort.
  Lemma diag q p : Combine (q/p) (q/p) (2 * (q/p)).
  Proof. apply _. Abort.
  Lemma diag : Combine (1/2) (1/2) 1.
  Proof. apply _. Abort.
  Lemma diag q : Combine (q/2) (q/2) q.
  Proof. apply _. Abort.
  Lemma diag : Combine (1/4) (1/4) (1/2).
  Proof. apply _. Abort.
  Lemma diag q : Combine (q/4) (q/4) (q/2).
  Proof. apply _. Abort.
  Lemma diag : Combine 1 1 2.
  Proof. apply _. Abort.
  Lemma diag : Combine 2 2 4.
  Proof. apply _. Abort.

  Lemma special : Combine (1/4) (3/4) 1.
  Proof. apply _. Abort.
  Lemma special : Combine (3/4) (1/4) 1.
  Proof. apply _. Abort.
  Lemma special : Combine (1/3) (2/3) 1.
  Proof. apply _. Abort.
  Lemma special : Combine (2/3) (1/3) 1.
  Proof. apply _. Abort.

  Lemma div_2 p q : Combine (q/(2*p)) (q/(2*p)) (q/p).
  Proof. apply _. Abort.
  Lemma div_2 p q : Combine (q/(2*p)) (q/(p*2)) (q/p).
  Proof. apply _. Abort.
  Lemma div_2 p q : Combine (q/(p*2)) (q/(2*p)) (q/p).
  Proof. apply _. Abort.
  Lemma div_2 p q : Combine (q/(p*2)) (q/(p*2)) (q/p).
  Proof. apply _. Abort.

  Lemma mul p q1 q2 : Combine (p * q1) (p * q2) (p * (q1 + q2)).
  Proof. apply _. Abort.
  Lemma mul p q1 q2 : Combine (q1 * p) (q2 * p) ((q1 + q2) * p).
  Proof. apply _. Abort.

  Lemma div q1 q2 p : Combine (q1/p) (q2/p) ((q1 + q2)/p).
  Proof. apply _. Abort.

  Lemma default p q : Combine p q (p + q).
  Proof. apply _. Abort.

End combine.
