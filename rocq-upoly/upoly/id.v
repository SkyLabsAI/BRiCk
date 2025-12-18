(*
 * Copyright (C) 2023-2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import skylabs.upoly.prelude.
Require Import skylabs.upoly.base.
Import UPoly.

(** ** Identity monad *)
(**
This module is not meant to be <<Import>>ed.
*)

Record M@{*u | } {A : Type@{u}} := mk { run : A }.
Add Printing Constructor M.
#[global] Arguments M _ : clear implicits, assert.
#[global] Arguments mk {_} _ : assert.
#[global] Arguments run {_} & _ : assert.

#[global] Instance map : FMap M := fun _ _ f a => mk $ f (run a).
#[global] Arguments map {_ _} _ & _ : assert.

#[global] Instance ret : MRet M := @mk.
#[global] Arguments ret {_} & _ : assert.

#[global] Instance bind : MBind M := fun _ _ f a => f (run a).
#[global] Arguments bind {_ _} _ & _ : assert.

#[global] Instance join : MJoin M := fun _ a => run a.
#[global] Arguments join {_} & _ : assert.

Definition ap : Ap M := _.
#[global] Arguments ap {_ _} & _ _ : assert.

#[global] Instance traverse : Traverse M := fun _ _ _ _ _ _ f a => mk <$> f (run a).
#[global] Arguments traverse {_ _ _ _ _ _} & _ _ : assert.
