(*
 * Copyright (C) 2020-2022 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bluerock.iris.extra.bi.prelude.
Require Import bluerock.iris.extra.bi.observe.
Require Import bluerock.iris.extra.bi.spec.knowledge.
Import ChargeNotation.

#[local] Set Primitive Projections.

(** * Spec building block: logical constants *)
(**
The judgment [Constant I P] means "under invariant [I], [P] is a
logical constant"; specifically, there exists a unique [x : A] such
that [P x], where [P x] itself is timeless, affine, and persistent.

Warning: [Constant] should be avoided when simpler things work. It
exists to track values that arise _dynamically_.
*)

Class Constant {A} {PROP : bi} (I : PROP) (P : A → PROP) : Prop := {
  #[global] constant_inv_knowledge :: Knowledge I;
  #[global] constant_exist :: Observe (Exists x, P x) I;

  #[global] constant_unique x y :: Observe2 [| x = y |] (P x) (P y);
  #[global] constant_knowledge x :: Knowledge (P x);
  #[global] constant_timeless x :: Timeless (P x);
}.
Arguments constant_exist {_ _} (_ _)%_I {_} : assert.
Arguments constant_unique {_ _} (_ _)%_I {_} _ _ : assert.
