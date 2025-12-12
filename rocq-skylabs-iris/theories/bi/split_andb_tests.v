(*
 * Copyright (c) 2022 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bluerock.prelude.base.
Require Import bluerock.iris.extra.bi.split_andb.

(**
[Split b b1 b2] succeeds if [SplitAndB b] outputs [b1], [b2].
*)
Class Split (b b1 b2 : bool) : Prop := split : SplitAndB b b1 b2.
#[global] Hint Mode Split + + + : typeclass_instances.
#[global] Instance split_instance b b'1 b'2 b1 b2 :
  SplitAndB b b'1 b'2 -> TCEq b1 b'1 -> TCEq b2 b'2 -> Split b b1 b2 | 10.
Proof. by rewrite !TCEq_eq=>? ->->. Qed.

Section split.

  Lemma split_andb b1 b2 : Split (b1 && b2) b1 b2.
  Proof. apply _. Abort.

  Lemma split_x b : Split b b b.
  Proof. apply _. Abort.

End split.

(**
[Combine b1 b2 b] succeeds if [CombineAndB b1 b2] outputs [b].
*)
Class Combine (b1 b2 b : bool) : Prop := combine : CombineAndB b1 b2 b.
#[global] Hint Mode Combine + + + : typeclass_instances.
#[global] Instance combine_instance b1 b2 b' b :
  CombineAndB b1 b2 b' -> TCEq b b' -> Combine b1 b2 b | 10.
Proof. by rewrite TCEq_eq=>? ->. Qed.

Section combine.

  Lemma combine_00 : Combine false false false.
  Proof. apply _. Abort.
  Lemma combine_01 : Combine false true false.
  Proof. apply _. Abort.
  Lemma combine_10 : Combine true false false.
  Proof. apply _. Abort.
  Lemma combine_11 : Combine true true true.
  Proof. apply _. Abort.

  Lemma combine_0x b : Combine false b false.
  Proof. apply _. Abort.
  Lemma combine_x0 b : Combine b false false.
  Proof. apply _. Abort.

  Lemma combine_1x b : Combine true b b.
  Proof. apply _. Abort.
  Lemma combine_x1 b : Combine b true b.
  Proof. apply _. Abort.

  Lemma combine_xx b1 b2 : Combine b1 b2 (b1 && b2).
  Proof. apply _. Abort.

End combine.
