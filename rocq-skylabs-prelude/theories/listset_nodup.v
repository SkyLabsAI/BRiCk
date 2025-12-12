(*
 * Copyright (C) 2020-21 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Export stdpp.listset_nodup.
Require Import bluerock.prelude.base.

#[global] Instance listset_nodup_elem_of_dec `{EqDecision A} : RelDecision (∈@{listset_nodup A}).
Proof.
  refine (λ x X, cast_if (decide (x ∈ listset_nodup_car X))); done.
Defined.
