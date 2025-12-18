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

(** * Products *)
(**
This module is not meant to be <<Import>>ed.
*)

Module Export Notations.
  Infix "*" := prod : type_scope.
  Notation "( a , b , .. , c )" := (pair .. (pair a b) .. c) : core_scope.
  Notation "(., b )" := (fun a => (a, b)) : stdpp_scope.
  Notation "( a ,.)" := (fun b => (a, b)) : stdpp_scope.

  Notation "p .1" := (fst p).
  Notation "p .2" := (snd p).
  Notation "ps .*1" := (UPoly.fmap fst ps).
  Notation "ps .*2" := (UPoly.fmap snd ps).
End Notations.

Definition run@{uA uB | uA <= prod.u0, uB <= prod.u1}
    {A : Type@{uA}} {B : Type@{uB}} (p : A * B) : Datatypes.prod A B :=
  Datatypes.pair (fst p) (snd p).
#[global] Arguments run _ _ & _ : assert.

Definition inj@{uA uB | uA <= prod.u0, uB <= prod.u1}
    {A : Type@{uA}} {B : Type@{uB}} (p : Datatypes.prod A B) : A * B :=
  match p with
  | Datatypes.pair a b => (a, b)
  end.
#[global] Arguments inj _ _ & _ : assert.

Definition first {A A' B} (f : A -> A') (p : A * B) : A' * B := (f p.1, p.2).
Definition second {A B B'} (f : B -> B') (p : A * B) : A * B' := (p.1, f p.2).

Section map.
  Universes uA uB uA' uB'.
  Context {A : Type@{uA}} {B : Type@{uB}} {A' : Type@{uA'}} {B' : Type@{uB'}}.

  Definition map (f : A -> A') (g : B -> B') (p : A * B) : A' * B' :=
    (f p.1, g p.2).
  #[global] Hint Opaque map : typeclass_instances.
  #[global] Arguments map _ _ & _ : assert.
End map.

Section traverse.
  Universes u1 u2 uL uR.
  Constraint uL <= u1, uR <= u1.
  Context {F : Type@{u1} -> Type@{u2}} `{!FMap@{u1 u2 uR} F, !MRet F, AP : !Ap@{u1 u2 uL uR} F}.

  Universes uA uB uA' uB'.
  Constraint uA' <= uR.
  Constraint uB' <= uL, uB' <= uR.
  Context {A : Type@{uA}} {B : Type@{uB}} {A' : Type@{uA'}} {B' : Type@{uB'}}.
  Definition traverse (f : A -> F A') (g : B -> F B') (p : prod A B) : F (prod A' B') :=
    pair <$> f p.1 <*> g p.2.
  #[global] Hint Opaque traverse : typeclass_instances.
  #[global] Arguments traverse _ _ & _ : assert.
End traverse.
