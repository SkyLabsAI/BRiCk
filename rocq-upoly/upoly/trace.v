(*
 * Copyright (C) 2023-2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import skylabs.upoly.prelude.
Require Import skylabs.upoly.base.
Require Import skylabs.upoly.UTypes.
Require Import skylabs.upoly.list.
Import UPoly.

(** * Trace monad *)
(**
This module is not meant to be <<Import>>ed.

<<trace.M>> is a variation on <<result E A := Val (_ : A) | Err (_ :
E)>> with backtraces.

We tend to use a fixed, inhabited type <<E : Set>> and to lock errors
and backtrace entries. Example (using the Elpi locker): <<mlock
Definition My_error : E := inhabitant.>>
*)

Variant M@{*uE *uA | } {E : Type@{uE}} {A : Type@{uA}} : Type :=
| Success (_ : A)
| Backtrace (_ : list E).
#[global] Arguments M : clear implicits.

Definition run {E A} (m : M E A) : Datatypes.sum (Datatypes.list E) A :=
  match m with
  | Success a => Datatypes.inr a
  | Backtrace t => Datatypes.inl (list.run t)
  end.
#[global] Arguments run _ _ & _ : assert.

Definition runO {E A} (m : M E A) : Datatypes.option A :=
  match m with
  | Success a => Datatypes.Some a
  | Backtrace _ => Datatypes.None
  end.
#[global] Arguments runO _ _ & _ : assert.

Section trace.
  Universes uE.
  Context {E : Type@{uE}}.
  #[local] Notation M := (M E).

  #[global] Instance map : FMap M := fun _ _ f m =>
    match m with
    | Success a => Success $ f a
    | Backtrace t => Backtrace t
    end.
  #[global] Arguments map {_ _} _ & _ : assert.

  #[global] Instance ret : MRet M := fun _ => Success.
  #[global] Arguments ret {_} & _ : assert.

  #[global] Instance bind : MBind M := fun _ _ f m =>
    match m with
    | Success a => f a
    | Backtrace t => Backtrace t
    end.
  #[global] Arguments bind {_ _} _ & _ : assert.

  #[global] Instance join : MJoin M := fun _ m =>
    match m with
    | Success (Success _ as c) => c
    | Backtrace t | Success (Backtrace t) => Backtrace t
    end.
  #[global] Arguments join {_} & _ : assert.

  Definition ap : Ap M := _.
  #[global] Arguments ap {_ _} & _ _ : assert.

  #[global] Instance traverse : Traverse M := fun _ _ _ _ _ _ f s =>
    match s with
    | Success a => Success <$> f a
    | Backtrace t => mret $ Backtrace t
    end.
  #[global] Arguments traverse {_ _ _ _ _ _} & _ _ : assert.

  #[global] Instance fail : MFail M := fun _ _ => Backtrace [].
  #[global] Arguments fail {_} _ : assert.

  #[global] Instance trace : Trace E M := fun e _ m =>
    match m with
    | Success v => Success v
    | Backtrace t => Backtrace (e :: t)
    end.
  #[global] Arguments trace _ {_} & _ : assert.

  #[global] Instance throw : MThrow E M := fun _ e =>
    trace e mfail.
  #[global] Arguments throw {_} _ : assert.

  #[global] Instance catch : MCatch (list E) M := fun _ m h =>
    match m with
    | Success v => Success v
    | Backtrace t => h t
    end.
  #[global] Arguments catch {_} & _ _ : assert.

  Definition alternative : Alternative M := _.
  #[global] Arguments alternative {_} & _ _ : assert.

  #[global] Instance lift_optionp : MLift UTypes.option M := fun _ m =>
    if m is Some a then Success a else Backtrace [].
  #[global] Instance lift_option : MLift (eta Datatypes.option) M := fun _ m =>
    if m is Datatypes.Some a then Success a else Backtrace [].
End trace.
