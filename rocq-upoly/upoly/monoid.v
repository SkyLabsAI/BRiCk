(*
 * Copyright (C) 2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import skylabs.upoly.prelude.

(** * Monoid operations *)
(**
NOTE: We do not define this class in base.v or export this module from
<<skylabs.upoly.upoly>> to minimize conflicts with Iris' monoid class.
*)

Class Monoid@{*u | } (A : Type@{u}) : Type@{u} := {
  monoid_unit : A;
  monoid_op : A -> A -> A;
}.
#[global] Hint Mode Monoid ! : typeclass_instances.
#[global] Instance monoid_unit_params : Params (@monoid_unit) 2 := {}.
#[global] Instance monoid_op_params : Params (@monoid_op) 2 := {}.
#[global] Hint Opaque monoid_unit monoid_op : typeclass_instances.
