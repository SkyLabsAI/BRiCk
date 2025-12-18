(*
 * Copyright (C) 2023-2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import skylabs.upoly.prelude.
Require Import skylabs.upoly.base.
Import UPoly.

(** * Reader monad *)
(**
This module is not meant to be <<Import>>ed.
*)

Record M@{*uS *uA | } {S : Type@{uS}} {A : Type@{uA}} := mk { run : S -> A }.
Add Printing Constructor M.
#[global] Arguments M : clear implicits.
#[global] Arguments mk {_ _} _ : assert.
#[global] Arguments run _ _ _ & _ : assert.

Section reader.
  Universes uS.
  Context {S : Type@{uS}}.
  #[local] Notation M := (M S).

  #[global] Instance map : FMap M := fun _ _ f x =>
    mk $ fun s => f $ run x s.
  #[global] Arguments map {_ _} _ & _ : assert.

  #[global] Instance ret : MRet M := fun _ x =>
    mk $ const x.
  #[global] Arguments ret {_} & _ : assert.

  #[global] Instance bind : MBind M := fun _ _ f c =>
    mk $ fun s => run (f $ run c s) s.
  #[global] Arguments bind {_ _} _ & _ : assert.

  #[global] Instance ap : Ap M := fun _ _ f c =>
    mk $ fun s => run f s $ run c s.
  #[global] Arguments ap {_ _} & _ _ : assert.

  #[global] Instance join : MJoin M := fun _ c =>
    mk $ fun s => run (run c s) s.
  #[global] Arguments join {_} & _ : assert.

  Definition ask : M S := mk id.

  Definition asks@{uA} {A : Type@{uA}} (f : S -> A) : M A := mk f.
  #[global] Arguments asks _ & _ : assert.	(* useful? *)

  Definition local@{uA} {A : Type@{uA}} (f : S -> S) (c : M A) : M A :=
    mk $ fun s => run c (f s).
  #[global] Arguments local _ _ & _ : assert.
End reader.
