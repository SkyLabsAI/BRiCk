(*
 * Copyright (c) 2022 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bluerock.prelude.numbers.

(** * Splitting and combining booleans on [&&] *)
(**
Overview:

- [SplitAndB], [CombineAndB] split and combine boolean expressions
built up from constants and [&&]. They simplify their outputs.
*)

(**
Our rules are syntactic: In principle, all definitions appearing in
input positions should to be opaque for typeclass resolution. That
means [andb].

Marking something pervasive like [andb] TC opaque can cause problems
elsewhere, so we leave it alone.

This is not likely to have a great performance impact because very few
of our combining and splitting rules actually mention [andb]:

- [split_andb.split_andb] (below)

- [combine_frac.fold_add] (in ../cpp/bi/split_cv.v)

*)

#[local] Notation Cut := TCNoBackTrack.

(**
[SplitAndB b b1 b2] splits boolean [b] into [b1], [b2] s.t. [b = b1 &&
b2], adjusting the outputs [b1], [b2] for readability.
*)
Class SplitAndB (b b1 b2 : bool) : Prop := split_andb : b = b1 && b2.
#[global] Hint Mode SplitAndB + - - : typeclass_instances.
#[global] Arguments SplitAndB : simpl never.
#[global] Arguments split_andb _ {_ _ _} : assert.

Module split_andb.

  (**
  We use this auxiliary judgment to [Cut] in [SplitAndB].
  *)
  Class Split (b b1 b2 : bool) : Prop := split : b = b1 && b2.
  #[global] Hint Mode Split + - - : typeclass_instances.
  #[global] Arguments Split : simpl never.
  #[global] Arguments split _ {_ _ _} : assert.
  Notation SPLIT b b1 b2 := (Cut (Split b b1 b2)) (only parsing).

  #[global] Instance split_andb b1 b2 : Split (b1 && b2) b1 b2 | 10.
  Proof. done. Qed.

  #[global] Instance split_diag b : Split b b b | 50.
  Proof. rewrite /Split. by rewrite andb_diag. Qed.

End split_andb.

#[global] Instance split_split b b1 b2 :
  split_andb.SPLIT b b1 b2 -> SplitAndB b b1 b2 | 10.
Proof. by case. Qed.

(**
[CombineAndB b1 b2 b] combines booleans [b1], [b2] into [b = b1 &&
b2], adjusting the output [b] for readability.
*)
Class CombineAndB (b1 b2 b : bool) : Prop := combine_andb : b1 && b2 = b.
#[global] Hint Mode CombineAndB + + - : typeclass_instances.
#[global] Arguments CombineAndB : simpl never.
#[global] Arguments combine_andb _ _ {_ _} : assert.

Module combine_andb.

  (**
  We use this auxiliary judgment to [Cut] in [CombineAndB].
  *)
  Class Combine (b1 b2 b : bool) : Prop := combine : b1 && b2 = b.
  #[global] Hint Mode Combine + + - : typeclass_instances.
  #[global] Arguments Combine : simpl never.
  #[global] Arguments combine _ _ {_ _} : assert.
  Notation COMBINE q1 q2 q := (Cut (Combine q1 q2 q)) (only parsing).

  (** [false] absorbing *)
  #[global] Instance combine_0x b : Combine false b false | 10.
  Proof. done. Qed.
  #[global] Instance combine_x0 b : Combine b false false | 15.
  Proof. rewrite /Combine. by rewrite right_absorb_L. Qed.

  (** [true] an identity *)
  #[global] Instance combine_1x b : Combine true b b | 10.
  Proof. done. Qed.
  #[global] Instance combine_x1 b : Combine b true b | 15.
  Proof. rewrite /Combine. by rewrite right_id_L. Qed.

  (** [b && b --> b] *)
  #[global] Instance combine_diag b : Combine b b b| 50.
  Proof. rewrite /Combine. by rewrite andb_diag. Qed.

  #[global] Instance combine_xx b1 b2 : Combine b1 b2 (b1 && b2) | 51.
  Proof. done. Qed.

End combine_andb.

#[global] Instance combine_andb_combine b b1 b2 :
  combine_andb.COMBINE b b1 b2 -> CombineAndB b b1 b2 | 10.
Proof. by case. Qed.
