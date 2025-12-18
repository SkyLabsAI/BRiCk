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

(** * Sums *)
(**
This module is not meant to be <<Import>>ed.
*)

Module Export Notations.
  Infix "+" := sum : type_scope.
End Notations.

Definition run@{uA uB | uA <= sum.u0, uB <= sum.u1}
    {A : Type@{uA}} {B : Type@{uB}} (s : A + B) : Datatypes.sum A B :=
  match s with
  | inl a => Datatypes.inl a
  | inr b => Datatypes.inr b
  end.
#[global] Arguments run _ _ & _ : assert.

Definition inj@{uA uB | uA <= sum.u0, uB <= sum.u1}
    {A : Type@{uA}} {B : Type@{uB}} (s : Datatypes.sum A B) : A + B :=
  match s with
  | Datatypes.inl a => inl a
  | Datatypes.inr b => inr b
  end.
#[global] Arguments inj _ _ & _ : assert.

Section map.
  Universes uA uB uA' uB'.
  Context {A : Type@{uA}} {B : Type@{uB}} {A' : Type@{uA'}} {B' : Type@{uB'}}.

  Definition map (f : A -> A') (g : B -> B') (s : A + B) : A' + B' :=
    match s with
    | inl a => inl $ f a
    | inr b => inr $ g b
    end.
  #[global] Hint Opaque map : typeclass_instances.
  #[global] Arguments map _ _ & _ : assert.
End map.

Section traverse.
  Universes u1 u2 uS uA uB uA' uB'.
  Constraint uS <= u1.
  Constraint uA' <= uS.
  Constraint uB' <= uS.
  Context {F : Type@{u1} -> Type@{u2}} `{!FMap@{u1 u2 uS} F}.
  Context {A : Type@{uA}} {B : Type@{uB}} {A' : Type@{uA'}} {B' : Type@{uB'}}.

  Definition traverse (f : A -> F A') (g : B -> F B') (s : sum A B) : F (sum A' B') :=
    match s with
    | inl a => inl <$> f a
    | inr b => inr <$> g b
    end.
  #[global] Hint Opaque traverse : typeclass_instances.
  #[global] Arguments traverse _ _ & _ : assert.
End traverse.
