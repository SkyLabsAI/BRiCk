(*
 * Copyright (C) 2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import skylabs.upoly.prelude.
Require Import skylabs.upoly.base.
Require Import skylabs.upoly.UTypes.
Require Import skylabs.upoly.prod.
Require Import skylabs.upoly.monoid.
Import UPoly.

(** * Writer monad transformer *)
(**
This module is not meant to be <<Import>>ed.
*)

Record M@{*uV *u1 *u2 *uA | uV <= u1, uA <= u1}
    {V : Type@{uV}} {m : Type@{u1} -> Type@{u2}}
    {A : Type@{uA}} : Type@{u2} :=
  mk { runp : m (V * A)%type }.
Add Printing Constructor M.
#[global] Arguments M : clear implicits.
#[global] Arguments mk {_ _ _} _ : assert.
#[global] Arguments runp {_ _ _} & _ : assert.

Definition run {V m A} `{!FMap m} (c : M V m A) : m (Datatypes.prod V A) :=
  prod.run <$> runp c.
Arguments run {_ _ _ _} & _ : assert.

Section writer.
  Universes uV u1 u2.
  Constraint uV <= u1.
  Context {V : Type@{uV}} {m : Type@{u1} -> Type@{u2}}.
  Context `{!Monoid V, !FMap m, !MRet m}.
  #[local] Notation M := (M V m).

  #[global] Instance map : FMap M := fun _ _ f c =>
    mk $ second f <$> runp c.
  #[global] Arguments map {_ _} _ & _ : assert.

  #[global] Instance ret : MRet M := fun _ v =>
    mk $ mret (monoid_unit, v).
  #[global] Arguments ret {_} & _ : assert.

  #[global] Instance bind `{!MBind m} : MBind M := fun _ _ f a =>
    mk $ runp a >>= fun '(v, r) => first (monoid_op v) <$> runp (f r).
  #[global] Arguments bind {_ _ _} _ & _ : assert.

  #[global] Instance join `{!MBind m} : MJoin M := fun _ a =>
    mk $ runp a >>= fun '(v, r) => first (monoid_op v) <$> runp r.
  #[global] Arguments join {_ _} & _ : assert.

  #[global] Instance ap `{!Ap m} : Ap M := fun _ _ f a =>
     mk $ (fun '(v, f) '(v', r) => (monoid_op v v', f r)) <$> runp f <*> runp a.
  #[global] Arguments ap {_ _ _} & _ _ : assert.

  #[global] Instance lift : MLift m M := fun _ c =>
    mk $ pair monoid_unit <$> c.
  #[global] Arguments lift {_} & _ : assert.

  Definition tell (v : V) : M unit := mk $ mret (v, tt).

  Definition writer (v : V) {A} (c : m A) : M A :=
    mk $ pair v <$> c.
  #[global] Arguments writer _ _ & _ : assert.

  Definition listen {A} (c : M A) : M (A * V) :=
    mk $ (fun '(v, r) => (v, (r, v))) <$> runp c.
  #[global] Arguments listen _ & _ : assert.

  Definition pass {A} (m : M (A * (V -> V))) : M A :=
    mk $ (fun '(v, (a, f)) => (f v, a)) <$> runp m.
  #[global] Arguments pass _ & _ : assert.
End writer.
