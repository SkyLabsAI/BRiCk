(*
 * Copyright (c) 2022 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bluerock.prelude.base.
Require Import bluerock.lang.cpp.bi.split_cfrac.

#[local] Set Printing Coercions.

(**
[Split q q1 q2] succeeds if [SplitCFrac q] outputs [q1], [q2].
*)
Class Split (q q1 q2 : cQp.t) : Prop := split : SplitCFrac q q1 q2.
#[global] Hint Mode Split + + + : typeclass_instances.
#[global] Instance split_cfrac q q'1 q'2 q1 q2 :
  SplitCFrac q q'1 q'2 -> TCEq q1 q'1 -> TCEq q2 q'2 -> Split q q1 q2 | 10.
Proof. by rewrite !TCEq_eq=>? ->->. Qed.

Section split.

  (** Splitting on [cQp.add] is immediate *)

  Lemma immediate p q : Split (p + q) p q.
  Proof. apply _. Abort.
  Lemma immediate p q : Split (cmra.op p q) p q.
  Proof. apply _. Abort.

  (** Splitting on [cQp.scale q] preserves the factor [q] *)

  Lemma subterm q q1 q2 :
    Split (cQp.scale q (q1 + q2))
      (cQp.scale q q1)
      (cQp.scale q q2).
  Proof. apply _. Abort.

  Lemma subterm p q q1 q2 :
    Split (cQp.scale p (cQp.scale q (q1 + q2)))
      (cQp.scale p (cQp.scale q q1))
      (cQp.scale p (cQp.scale q q2)).
  Proof. apply _. Abort.

  (**
  Otherwise, splitting works componentwise.

  See ../../bi/split_andb_tests.v and ../../bi/split_frac_tests.v for
  more examples of the underlying splits.
  *)

  Lemma const q1 q2 : Split (q1 + q2)$c q1$c q2$c.
  Proof. apply _. Abort.

  Lemma mut q1 q2 : Split (q1 + q2)$m q1$m q2$m.
  Proof. apply _. Abort.

  Lemma general c1 c2 q1 q2 :
    Split (cQp.mk (c1 && c2) (q1 + q2)) (cQp.mk c1 q1) (cQp.mk c2 q2).
  Proof. apply _. Abort.

  Lemma mk c q :
    let half := cQp.mk c (q / 2) in
    Split (cQp.mk c q) half half.
  Proof. cbn. apply _. Abort.

  Lemma var cq :
    let half := cQp.mk (cQp.is_const cq) (cQp.frac cq / 2) in
    Split cq half half.
  Proof. cbn. apply _. Abort.

  Lemma scale_var q cq :
    let half := cQp.scale q (cQp.mk (cQp.is_const cq) (cQp.frac cq / 2)) in
    Split (cQp.scale q cq) half half.
  Proof. cbn. apply _. Abort.

End split.

(**
[Combine q1 q2 q] succeeds if [CombineCFrac q1 q2] outputs [q].
*)
Class Combine (q1 q2 q : cQp.t) : Prop := combine : CombineCFrac q1 q2 q.
#[global] Hint Mode Combine + + + : typeclass_instances.
#[global] Instance combine_frac q1 q2 q' q :
  CombineCFrac q1 q2 q' -> TCEq q q' -> Combine q1 q2 q | 10.
Proof. by rewrite TCEq_eq=>? ->. Qed.

Section combine.

  (**
  Combining terms of the form [cQp.scale q _] preserves that
  structure.
  *)

  Lemma scale q q1 q2 :
    Combine (cQp.scale q q1) (cQp.scale q q2) (cQp.scale q (q1 + q2)).
  Proof. apply _. Abort.
  Lemma scale p q q1 q2 :
    Combine
      (cQp.scale p (cQp.scale q q1))
      (cQp.scale p (cQp.scale q q2))
      (cQp.scale p (cQp.scale q (q1 + q2))).
  Proof. apply _. Abort.

  Lemma scale_mut q q1 q2 :
    Combine (cQp.scale q q1$m) (cQp.scale q q2$m) (cQp.scale q (q1 + q2)$m).
  Proof. apply _. Abort.

  (**
  Otherwise, combining works componentwise and then folds [cQp.add]
  and eta reduces [cQp.mk].

  See ../../bi/split_andb_tests.v and ../../bi/split_frac_tests.v for
  more examples of how components combine.
  *)

  Lemma var q : Combine q q (q + q).
  Proof. apply _. Abort.
  Lemma var q1 q2 : Combine q1 q2 (q1 + q2).
  Proof. apply _. Abort.

  Lemma const q1 q2 : Combine q1$c q2$c (q1 + q2)$c.
  Proof. apply _. Abort.

  Lemma mut q1 q2 : Combine q1$m q2$m (q1 + q2)$m.
  Proof. apply _. Abort.

  Lemma general c1 c2 q1 q2 :
    Combine (cQp.mk c1 q1) (cQp.mk c2 q2) (cQp.mk (c1 && c2) (q1 + q2)).
  Proof. apply _. Abort.

  Lemma mk c q :
    let half := cQp.mk c (q / 2) in
    Combine half half (cQp.mk c q) .
  Proof. cbn. apply _. Abort.

  Lemma var cq :
    let half := cQp.mk (cQp.is_const cq) (cQp.frac cq / 2) in
    Combine half half cq.
  Proof. cbn. apply _. Abort.

  Lemma scale_var q cq :
    let half := cQp.scale q (cQp.mk (cQp.is_const cq) (cQp.frac cq / 2)) in
    Combine half half (cQp.scale q cq).
  Proof. cbn. apply _. Abort.

End combine.
