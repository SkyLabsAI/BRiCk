(*
 * Copyright (C) 2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import skylabs.upoly.prelude.
Require Import skylabs.upoly.base.
Require Import skylabs.upoly.UTypes.
Require Import skylabs.upoly.monoid.
Import UPoly.

(** * Writer monad *)
(**
This module is not meant to be <<Import>>ed.
*)

Record M@{*uV uA | } {V : Type@{uV}} {A : Type@{uA}} : Type@{max(uV,uA)} := mk {
  value : V;
  result : A;
}.
Add Printing Constructor M.
#[global] Arguments M _ _ : clear implicits, assert.
#[global] Arguments mk {_ _} _ _ : assert.

Definition runp {V A} (m : M V A) : UTypes.prod V A := pair m.(value) m.(result).
#[global] Arguments runp _ _ & _ : assert.

Definition run {V A} (m : M V A) : Datatypes.prod V A := (m.(value), m.(result)).
#[global] Arguments run _ _ & _ : assert.

Section writer.
  Universes uV.
  Context {V : Type@{uV}}.
  Context `{!Monoid V}.
  #[local] Notation M := (M V).

  #[global] Instance map : FMap M := fun _ _ f a => mk a.(value) $ f a.(result).
  #[global] Arguments map {_ _} _ & _ : assert.

  #[global] Instance ret : MRet M := fun _ v => mk monoid_unit v.
  #[global] Arguments ret {_} & _ : assert.

  #[global] Instance bind : MBind M := fun _ _ f m =>
    match m with
    | mk v a =>
      match f a with
      | mk v' r => mk (monoid_op v v') r
      end
    end.
  #[global] Arguments bind {_ _} _ & _ : assert.

  #[global] Instance join : MJoin M := fun _ m =>
    match m with
    | mk v (mk v' r) => mk (monoid_op v v') r
    end.
  #[global] Arguments join {_} & _ : assert.

  #[global] Instance ap : Ap M := fun _ _ f x =>
    match f , x with
    | mk v f , mk v' a => mk (monoid_op v v') $ f a
    end.
  #[global] Arguments ap {_ _} & _ _ : assert.

  #[global] Instance traverse : Traverse M := fun _ _ _ _ _ _ f m =>
    match m with
    | mk v a => mk v <$> f a
    end.
  #[global] Arguments traverse {_ _ _ _ _ _} & _ _ : assert.

  Definition tell (v : V) : M unit := mk v tt.

  Definition writer (v : V) {A} (a : A) : M A := mk v a.
  #[global] Arguments writer _ _ & _ : assert.

  Definition listen {A} (m : M A) : M (A * V) :=
    mk m.(value) (m.(result), m.(value)).
  #[global] Arguments listen _ & _ : assert.

  Definition pass {A} (m : M (A * (V -> V))) : M A :=
    match m with
    | mk v (a, f) => mk (f v) a
    end.
  #[global] Arguments pass _ & _ : assert.
End writer.
