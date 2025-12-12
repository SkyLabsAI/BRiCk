(*
 * Copyright (c) 2020-21 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Export stdpp.relations.
Require Import bluerock.prelude.base.

#[global] Instance sc_reflexive `(Reflexive A R) : Reflexive (sc R).
Proof. intros a. exact: sc_lr. Qed.
#[global] Instance tc_reflexive `(Reflexive A R) : Reflexive (tc R).
Proof. intros a. exact: tc_once. Qed.
#[global] Instance tc_symmetric `(Symmetric A R) : Symmetric (tc R).
Proof.
  induction 1 as [?? IH%symmetry|??? Hyz%symmetry _ IHyz].
  exact: tc_once.
  etrans => //.
  exact: tc_once.
Qed.
