(*
 * Copyright (C) 2023-2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import skylabs.upoly.prelude.
Require Import skylabs.upoly.base.
Require Import skylabs.upoly.UTypes.
Require Import skylabs.upoly.option.
Import UPoly.

(** * Option monad transformer *)
(**
This module is not meant to be <<Import>>ed.
*)

Record M@{*u1 *u2 *uA | uA <= u1} {m : Type@{u1} -> Type@{u2}} {A : Type@{uA}} :=
  mk { runp : m (option A) }.
Add Printing Constructor M.
#[global] Arguments M : clear implicits.
#[global] Arguments mk {_ _} _ : assert.
#[global] Arguments runp _ _ & _ : assert.

Definition run {m : Type -> Type} `{!FMap m} {A} (c : M m A) : m (Datatypes.option A) :=
  option.run <$> runp c.
#[global] Arguments run _ _ _ & _ : assert.

Section optionT.
  Universes u1 u2.
  Context {m : Type@{u1} -> Type@{u2}}.
  #[local] Notation M := (M m).
  Context `{!FMap m, !MRet m}.

  #[global] Instance map : FMap M := fun _ _ f c =>
    mk $ fmap f <$> runp c.
  #[global] Arguments map {_ _} _ & _ : assert.

  #[global] Instance ret : MRet M := fun _ c =>
    mk $ mret $ Some c.
  #[global] Arguments ret {_} & _ : assert.

  #[global] Instance join `{!MBind m} : MJoin M := fun _ c =>
    mk $ runp c >>= fun o => if o is Some c then runp c else mret None.
  #[global] Arguments join {_ _} & _ : assert.

  #[global] Instance bind `{!MBind m} : MBind M := fun _ _ f c =>
    mjoin (f <$> c).
  #[global] Arguments bind {_ _ _} _ & _ : assert.

  #[global] Instance ap `{!Ap m} : Ap M := fun _ _ f c =>
    mk $ UPoly.ap (F:=option) <$> runp f <*> runp c.
  #[global] Arguments ap {_ _ _} & _ _ : assert.

  (**
  TODO: Perhaps we could usefully lift <<Traverse>> from <<m>> to
  <<M>>
  *)

  #[global] Instance fail : MFail M := fun _ _ => mk $ mret None.
  #[global] Arguments fail {_} _ : assert.

  #[global] Instance catch `{!MBind m} : MCatch unit M := fun _ c h =>
    mk $ runp c >>= fun c =>
    if c is Some _ then mret c else runp (h ()).
  #[global] Arguments catch {_ _} & _ _ : assert.

  (**
  NOTE: We would prefer to define <<Alternative>> without <<MBind>>
  (in case <<m>> is only applicative) but to do so, it seems we must
  eagerly force <<q>>, defeating laziness..
  *)
  Succeed Definition alternative_not_lazy `{!Ap m} : Alternative M := fun _ p q =>
    mk $ alternative <$> runp p <*> ((fun v _ => v) <$> runp (q ())).

  Definition alternative `{!MBind m} : Alternative M := _.
  #[global] Arguments alternative {_ _} & _ _ : assert.

  (**
  NOTE: The following instances can be useful in, e.g., parsers
  which might want to separate backtrackable errors from
  unrecoverable errors.
  *)
  #[global] Instance trace {E} `{!Trace E m} : Trace E M := fun e _ c =>
    mk $ trace e (runp c).
  #[global] Arguments trace {_ _} _ {_} & _ : assert.

  #[global] Instance throw {E} `{!MThrow E m} : MThrow E M := fun _ e =>
    mk $ mthrow e.
  #[global] Arguments throw {_ _ _} _ : assert.

  #[global] Instance catch' {E} `{!MCatch E m} : MCatch E M := fun _ c h =>
    mk $ mcatch (runp c) (fun e => runp (h e)).
  #[global] Arguments catch' {_ _ _} & _ _ : assert.

  #[global] Instance lift : MLift m M := fun _ c =>
    mk $ Some <$> c.
  #[global] Arguments lift {_} & _ : assert.

  Section lift.
    Universes v1 v2.
    Context {m' : Type@{v1} -> Type@{v2}}.
    #[global] Instance lift_over `{!MLift m' m} : MLift m' M := fun _ c =>
      mk $ Some <$> mlift c.
    #[global] Arguments lift_over {_ _} & _ : assert.
  End lift.
  #[global] Instance lift_optionp : MLift UTypes.option M := fun _ c =>
    mk $ mret c.
  #[global] Instance lift_option : MLift (eta Datatypes.option) M := fun _ c =>
    mk $ mret $ mlift c.
End optionT.
