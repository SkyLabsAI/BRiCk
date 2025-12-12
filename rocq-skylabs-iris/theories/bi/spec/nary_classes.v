(*
 * Copyright (C) 2021-2023 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bluerock.iris.extra.bi.derived_laws.
Require Import bluerock.iris.extra.bi.observe.
Require Import bluerock.iris.extra.bi.fractional.
Require Import bluerock.iris.extra.bi.monpred.
(**
NOTE: The preceding modules include inner modules "nary" to enable the
following exports, which in turn keep this module backwards compatible
with an earlier incarnation.

We cannot simply export the preceding modules (specifically
their effects on canonical structures) without potentially changing
canonical structure inference for our clients. Consider the following
test involving two files:

<<
  (* prelude.v *)
  Require Export bluerock.lang.cpp.logic.pred.
  Require Export bluerock.iris.extra.bi.spec.nary_classes.

  (** test.v *)
  Require Import prelude.
  Print Canonical Projections bi_bi_later_mixin.
>>

The test is supposed to print

<<
uPred_bi_later_mixin <- bi_bi_later_mixin ( uPredI )
monPred_bi_later_mixin <- bi_bi_later_mixin ( monPredI )
>>

Were we to simply export the upstream modules, the test would instead
print

<<
uPred_bi_later_mixin <- bi_bi_later_mixin ( uPredI )
monPred_bi_later_mixin <- bi_bi_later_mixin ( RepI )
>>

The switch from [monPredI] to [RepI] is simply wrong.
*)

Export derived_laws.nary.	(** [PersistentN], [AffineN], [AbsorbingN], [TimelessN] *)
Export observe.nary.	(** [Agree1], [LaterAgreeN] *)
Export fractional.nary.	(** [FractionalN], [AsFractionalN], [AgreeF1] *)
Export monpred.nary.	(** [ObjectiveN] *)
