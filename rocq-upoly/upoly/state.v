(*
 * Copyright (C) 2023-2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import skylabs.upoly.prelude.
Require Import skylabs.upoly.base.
Require Import skylabs.upoly.UTypes.
Require Import skylabs.upoly.prod.
Import UPoly.

(** * State monad *)
(**
This module is not meant to be <<Import>>ed.
*)

Record M@{*uS *uA | } {S : Type@{uS}} {A : Type@{uA}} := mk { runp : S -> S * A }.
Add Printing Constructor M.
#[global] Arguments M : clear implicits.
#[global] Arguments mk {_ _} _ : assert.
#[global] Arguments runp {_ _} & _ _ : assert.

Definition run {S A} (m : M S A) (s : S) : Datatypes.prod S A :=
  prod.run $ runp m s.
#[global] Arguments run {_ _} & _ _ : assert.

Section state.
  Universes uS.
  Context {S : Type@{uS}}.
  #[local] Notation M := (M S).

  #[global] Instance map : FMap M := fun _ _ f m =>
    mk $ fun s => second f $ runp m s.
  #[global] Arguments map {_ _} _ & _ : assert.

  #[global] Instance ret : MRet M := fun _ x =>
    mk $ fun s => (s, x).
  #[global] Arguments ret {_} & _ : assert.

  #[global] Instance bind : MBind M := fun _ _ f m =>
    mk $ fun s => let p := runp m s in runp (f p.2) p.1.
  #[global] Arguments bind {_ _} _ & _ : assert.

  Definition ap : Ap M := _.
  #[global] Arguments ap {_ _} & _ _ : assert.

  #[global] Instance join : MJoin M := fun _ m =>
    mk $ fun s => let p := runp m s in runp p.2 p.1.
  #[global] Arguments join {_} & _ : assert.

  Definition get : M S := mk $ fun s => (s, s).

  Definition gets@{uA} {A : Type@{uA}} (p : S -> A) : M A :=
    mk $ fun s => (s, p s).
  #[global] Arguments gets _ & _ : assert.	(* useful? *)

  Definition put (s : S) : M unit := mk $ fun s => (s, ()).

  Definition modify (f : S -> S) : M unit :=
    mk $ fun s => (f s, ()).

  Definition state@{uA | uS <= prod.u0, uA <= prod.u1}
      {A : Type@{uA}} (f : S -> Datatypes.prod S A) : M A :=
    mk $ fun s => prod.inj $ f s.
  #[global] Arguments state _ & _ : assert.	(* useful? *)
End state.
