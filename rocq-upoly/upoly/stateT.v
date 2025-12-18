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
Require skylabs.upoly.readerT.
Import UPoly.

(** * State monad transformer *)
(**
This module is not meant to be <<Import>>ed.
*)

Record M@{*uS *u1 *u2 *uA | uS <= u1, uA <= u1}
    {S : Type@{uS}} {m : Type@{u1} -> Type@{u2}} {A : Type@{uA}} :=
  mk { runp : S -> m (S * A)%type }.
Add Printing Constructor M.
#[global] Arguments M : clear implicits.
#[global] Arguments mk {_ _ _} _ : assert.
#[global] Arguments runp {_ _ _} & _ _ : assert.

Definition run {S A} {m : Type -> Type} `{!FMap m}
    (c : M S m A) (s : S) : m (Datatypes.prod S A) :=
  prod.run <$> runp c s.
#[global] Arguments run {_ _ _ _} & _ _ : assert.

Section stateT.
  Universes uS u1 u2.
  Constraint uS <= u1.
  Context {S : Type@{uS}} {m : Type@{u1} -> Type@{u2}}.
  Context `{!FMap m, !MRet m}.
  #[local] Notation M := (M S m).

  #[global] Instance map : FMap M := fun _ _ f c =>
    mk $ fun s => second f <$> runp c s.
  #[global] Arguments map {_ _} _ & _ : assert.

  #[global] Instance ret : MRet M := fun _ x =>
    mk $ fun s => mret (s, x).
  #[global] Arguments ret {_} & _ : assert.

  #[global] Instance join `{!MBind m} : MJoin M := fun A c =>
    mk $ fun s => runp c s >>= fun p => runp p.2 p.1.
  #[global] Arguments join {_ _} & _ : assert.

  #[global] Instance bind `{!MBind m} : MBind M := fun _ _ f c =>
    mk $ fun s => runp c s >>= fun p => runp (f p.2) p.1.
  #[global] Arguments bind {_ _ _} _ & _ : assert.

  Definition ap `{!MBind m} : Ap M := _.
  #[global] Arguments ap {_ _ _} & _ _ : assert.

  (**
  TODO: Perhaps we could usefully lift <<Traverse>> from <<m>> to
  <<M>>
  *)

  #[global] Instance alternative `{!Alternative m} : Alternative M := fun _ p q =>
    mk $ fun s => runp p s <|> runp (q ()) s.
  #[global] Arguments alternative {_ _} & _ _ : assert.

  #[global] Instance fail `{!MFail m} : MFail M := fun _ _ =>
    mk $ const mfail.
  #[global] Arguments fail {_ _} _ : assert.

  Section errors.
    Universes uE.
    Context {E : Type@{uE}}.

    #[global] Instance trace `{!Trace E m} : Trace E M := fun e _ c =>
      mk $ fun s => trace e (runp c s).
    #[global] Arguments trace {_} _ {_} & _ : assert.

    #[global] Instance throw `{!MThrow E m} : MThrow E M := fun _ e =>
      mk $ const (mthrow e).
    #[global] Arguments throw {_ _} _ : assert.

    #[global] Instance catch `{!MCatch E m} : MCatch E M := fun _ c h =>
      mk $ fun s => mcatch (runp c s) $ fun e => runp (h e) s.
    #[global] Arguments catch {_ _} & _ _ : assert.
  End errors.

  #[global] Instance lift : MLift m M := fun _ c =>
    mk $ fun s => pair s <$> c.
  #[global] Arguments lift {_} & _ : assert.

  Section lift.
    Universes v1 v2.
    Context {m' : Type@{v1} -> Type@{v2}}.
    #[global] Instance lift_over `{!MLift m' m} : MLift m' M := fun _ c =>
      mk $ fun s => pair s <$> mlift c.
    #[global] Arguments lift_over {_ _} & _ : assert.
  End lift.
  #[global] Instance lift_reader : MLift (readerT.M S m) M := fun _ c =>
    mk $ fun s => pair s <$> readerT.run c s.

  Definition get : M S := mk $ fun s => mret (s, s).

  Definition getsM@{uA} {A : Type@{uA}} (p : S -> m A) : M A :=
    mk $ fun s => pair s <$> p s.
  #[global] Arguments getsM _ & _ : assert.	(* useful? *)

  Definition gets@{uA} {A : Type@{uA}} (p : S -> A) : M A :=
    getsM (mret \o p).
  #[global] Arguments gets _ & _ : assert.	(* useful? *)

  Definition putM (s : m S) : M unit :=
    mk $ fun _ => (fun s => (s, ())) <$> s.
  Definition put (s : S) : M unit :=
    putM (mret s).

  Definition modifyM (f : S -> m S) : M unit :=
    mk $ fun s => (fun s => (s, ())) <$> f s.
  Definition modify (f : S -> S) : M unit :=
    modifyM (mret \o f).

  Definition stateM {A} (f : S -> m (Datatypes.prod S A)) : M A :=
    mk $ fun s => prod.inj <$> f s.
  #[global] Arguments stateM _ & _ : assert.	(* useful? *)

  Definition state {A} (f : S -> Datatypes.prod S A) : M A :=
    stateM (mret \o f).
  #[global] Arguments state _ & _ : assert.	(* useful? *)
End stateT.
