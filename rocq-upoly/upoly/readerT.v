(*
 * Copyright (C) 2023-2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import skylabs.upoly.prelude.
Require Import skylabs.upoly.base.
Import UPoly.

(** * Reader monad transformer *)
(**
This module is not meant to be <<Import>>ed.
*)

Record M@{*uS *u1 *u2 *uA | uA <= u1} {S : Type@{uS}} {m : Type@{u1} -> Type@{u2}}
    {A : Type@{uA}} :=
  mk { run : S -> m A }.
Add Printing Constructor M.
#[global] Arguments M : clear implicits.
#[global] Arguments mk {_ _ _} _ : assert.
#[global] Arguments run _ _ _ & _ _ : assert.

Section readerT.
  Universes uS u1 u2 uM.
  Context {S : Type@{uS}} {m : Type@{u1} -> Type@{u2}}.
  Context `{!FMap m, !MRet m}.
  #[local] Notation M := (M S m).

  #[global] Instance map : FMap M := fun _ _ f x =>
    mk $ fun s => f <$> run x s.
  #[global] Arguments map {_ _} _ & _ : assert.

  #[global] Instance ret : MRet M := fun _ x =>
    mk $ fun _ => mret x.
  #[global] Arguments ret {_} & _ : assert.

  #[global] Instance bind `{MBind m} : MBind M := fun _ _ f c =>
    mk $ fun s => run c s >>= fun x => run (f x) s.
  #[global] Arguments bind {_ _ _} _ & _ : assert.

  #[global] Instance join `{!MBind m} : MJoin M := fun A c =>
    mk $ fun s => run c s >>= fun c => run c s.
  #[global] Arguments join {_ _} & _ : assert.

  #[global] Instance ap `{!Ap m} : Ap M := fun A B f c =>
    mk $ fun s => run f s <*> run c s.
  #[global] Arguments ap {_ _ _} & _ _ : assert.

  #[global] Instance alternative `{!Alternative m} : Alternative M := fun _ p q =>
    mk $ fun s => run p s <|> run (q ()) s.
  #[global] Arguments alternative {_ _} & _ _ : assert.

  (**
  TODO: Perhaps we could usefully lift <<Traverse>> from <<m>> to
  <<M>>
  *)

  #[global] Instance fail `{!MFail m} : MFail M := fun _ _ =>
    mk $ const mfail.
  #[global] Arguments fail {_ _} _ : assert.

  Section errors.
    Universes uE.
    Context {E : Type@{uE}}.

    #[global] Instance trace `{!Trace E m} : Trace E M := fun e _ c =>
      mk $ fun s => trace e $ run c s.
    #[global] Arguments trace {_} _ {_} & _ : assert.

    #[global] Instance throw `{!MThrow E m} : MThrow E M := fun _ e =>
      mk $ const (mthrow e).
    #[global] Arguments throw {_ _} _ : assert.

    #[global] Instance catch `{!MCatch E m} : MCatch E M := fun _ c h =>
      mk $ fun s => mcatch (run c s) $ fun e => run (h e) s.
    #[global] Arguments catch {_ _} & _ _ : assert.
  End errors.

  #[global] Instance lift : MLift m M := fun _ c =>
    mk $ const c.
  #[global] Arguments lift {_} & _ : assert.

  Section lift.
    Universes v1 v2.
    Context {m' : Type@{v1} -> Type@{v2}}.
    #[global] Instance lift_over `{!MLift m' m} : MLift m' M := fun _ c =>
      mk $ const (mlift c).
    #[global] Arguments lift_over {_ _} & _ : assert.
  End lift.

  Definition ask : M S := mk mret.
  Definition asksM@{uA} {A : Type@{uA}} (f : S -> m A) : M A := mk f.
  Definition asks@{uA} {A : Type@{uA}} (f : S -> A) : M A := mk $ fun s => mret (f s).
  #[global] Arguments asksM _ & _ : assert.	(* useful? *)
  #[global] Arguments asks _ & _ : assert.	(* useful? *)

  Definition localM@{uA} `{!MJoin m} {A : Type@{uA}} (f : S -> m S) (c : M A) : M A :=
    mk $ fun s => mjoin (run c <$> f s).
  Definition local@{uA} {A : Type@{uA}} (f : S -> S) (c : M A) : M A :=
    mk $ fun s => run c (f s).
  #[global] Arguments localM _ _ _ & _ : assert.
  #[global] Arguments local _ _ & _ : assert.
End readerT.
