(*
 * Copyright (C) 2023-2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import skylabs.upoly.prelude.

(** * Some universe polymorphic datatypes *)

(** [UTypes.prod] *)

Record prod@{*uA *uB |} {A : Type@{uA}} {B : Type@{uB}} : Type@{max(uA,uB)} := pair {
  fst : A;
  snd : B;
}.
Add Printing Constructor prod.
Add Printing Let prod.
#[global] Arguments prod : clear implicits.
#[global] Arguments pair {_ _} _ _ : assert.
#[global] Hint Resolve pair : core.

(** [UTypes.sum] *)

Variant sum@{*uA *uB | } {A : Type@{uA}} {B : Type@{uB}} : Type@{max(uA,uB)} :=
| inl (a : A)
| inr (b : B).
#[global] Arguments sum : clear implicits.
#[global] Arguments inl {_ _} _, [_] _ _ : assert.
#[global] Arguments inr {_ _} _, _ [_] _ : assert.

(** [UTypes.option] *)

Variant option@{*u | } {A : Type@{u}} : Type@{u} :=
| None
| Some (x : A).
#[global] Arguments option : clear implicits.

(** [UTypes.list] *)

Inductive list@{*u | } {A : Type@{u}} : Type@{u} :=
| nil
| cons (x : A) (l : list).
#[global] Arguments list : clear implicits.
