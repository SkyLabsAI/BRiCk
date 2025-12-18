(*
 * Copyright (C) 2023-2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import skylabs.upoly.prelude.
Require Import skylabs.upoly.base.
Require Import skylabs.upoly.UTypes.
Import UPoly.

(** * Options *)
(**
This module is not meant to be <<Import>>ed.
*)

Definition run {A} (m : option A) : Datatypes.option A :=
  match m with
  | Some x => Datatypes.Some x
  | None => Datatypes.None
  end.
#[global] Arguments run _ & _ : assert.

Definition inj {A} (m : Datatypes.option A) : option A :=
  match m with
  | Datatypes.Some x => Some x
  | Datatypes.None => None
  end.
#[global] Arguments inj _ & _ : assert.

#[global] Instance map : FMap option := fun _ _ f m =>
  if m is Some a then Some (f a) else None.
#[global] Arguments map {_ _} _ & _ : assert.

#[global] Instance ret : MRet option := @Some.
#[global] Arguments ret {_} & _ : assert.

#[global] Instance bind : MBind option := fun _ _ f m =>
  if m is Some a then f a else None.
#[global] Arguments bind {_ _} _ & _ : assert.

#[global] Instance join : MJoin option := fun _ m =>
  if m is Some o then o else None.
#[global] Arguments join {_} & _ : assert.

Definition ap : Ap option := _.
#[global] Arguments ap {_ _} & _ _ : assert.

#[global] Instance traverse : Traverse option := fun _ _ _ _ _ _ f m =>
  if m is Some a then Some <$> f a else mret None.
#[global] Arguments traverse {_ _ _ _ _ _} & _ _ : assert.

#[global] Instance fail : MFail option := fun _ _ => None.
#[global] Arguments fail {_} _ : assert.

#[global] Instance catch : MCatch unit option := fun _ m h =>
  if m is Some _ then m else h ().
#[global] Arguments catch {_} & _ _ : assert.

Definition alternative : Alternative option := _.
#[global] Arguments alternative {_} & _ _ : assert.

#[global] Instance lift_option : MLift (eta Datatypes.option) option := fun _ c =>
  match c with
  | Datatypes.Some a => Some a
  | Datatypes.None => None
  end.

Definition from_option@{uA uB | }
    {A : Type@{uA}} {B : Type@{uB}} (f : A -> B) (d : B) (m : option A) : B :=
  match m with Some x => f x | None => d end.
#[global] Instance from_option_params : Params (@from_option) 3 := {}.
#[global] Arguments from_option _ _ _ & _ !_ : simpl nomatch, assert.
#[global] Hint Opaque from_option : typeclass_instances.

Definition default@{u | } {A : Type@{u}} (d : A) (m : option A) : A :=
  from_option id d m.
#[global] Instance default_params : Params (@default) 1 := {}.
#[global] Arguments default _ & _ !_ : simpl nomatch, assert.
#[global] Hint Opaque default : typeclass_instances.
