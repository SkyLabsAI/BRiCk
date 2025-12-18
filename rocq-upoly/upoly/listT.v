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

#[local] Open Scope ulist_scope.

(** * List monad transformer *)
(**
This module is not meant to be <<Import>>ed.
*)

Record M@{*u1 *u2 *uA | uA <= u1} {m : Type@{u1} -> Type@{u2}} {A : Type@{uA}} :=
  mk { runp : m (list A) }.
Add Printing Constructor M.
#[global] Arguments M : clear implicits.
#[global] Arguments mk {_ _} _ : assert.
#[global] Arguments runp _ _ & _ : assert.

Definition run {m : Type -> Type} `{!FMap m} {A} (c : M m A) : m (Datatypes.list A) :=
  list.run <$> runp c.
#[global] Arguments run _ _ _ & _ : assert.

Section listT.
  Universes u1 u2.
  Context {m : Type@{u1} -> Type@{u2}}.
  Context `{!FMap m, !MRet m}.
  #[local] Notation M := (M m).

  #[global] Instance map : FMap M := fun _ _ f c =>
    mk $ fmap f <$> runp c.
  #[global] Arguments map {_ _} _ & _ : assert.

  #[global] Instance ret : MRet M := fun _ c =>
    mk $ mret [c].
  #[global] Arguments ret {_} & _ : assert.

  #[global] Instance join `{!MBind m} : MJoin M := fun A c =>
    mk $ runp c >>= fun cs =>
    foldr (fun l acc => runp l >>= fun k => foldr (fmap \o cons) acc k) (mret []) cs.
  #[global] Arguments join {_ _} & _ : assert.

  #[global] Instance bind `{!MBind m} : MBind M := fun _ _ f c =>
    mjoin (f <$> c).
  #[global] Arguments bind {_ _ _} _ & _ : assert.

  #[global] Instance ap `{!Ap m} : Ap M := fun _ _ f c =>
    mk $ UPoly.ap (F:=list) <$> runp f <*> runp c.
  #[global] Arguments ap {_ _ _} & _ _ : assert.

  (**
  TODO: Perhaps we could usefully lift <<Traverse>>, <<Trace E>>,
  <<MThrow E>>, <<MCatch E>> from <<m>> to <<M>>.
  *)

  #[global] Instance fail : MFail M := fun _ _ => mk $ mret [].
  #[global] Arguments fail {_} _ : assert.

  #[global] Instance catch `{!MBind m} : MCatch unit M := fun _ c h =>
    mk $ runp c >>= fun c =>
    if c isn't nil then mret c else runp (h ()).
  #[global] Arguments catch {_ _} & _ _ : assert.

  (**
  We would prefer to avoid <<MBind>>. See [optionT.alternative].
  *)
  Succeed Definition alternative_not_lazy `{!Ap m} : Alternative M := fun _ p q =>
    mk $ alternative <$> runp p <*> ((fun v _ => v) <$> runp (q ())).
  Definition alternative `{!MBind m} : Alternative M := _.
  #[global] Arguments alternative {_ _} & _ _ : assert.

  #[global] Instance lift : MLift m M := fun _ c =>
    mk $ mret <$> c.
  #[global] Arguments lift {_} & _ : assert.

  Section lift.
    Universes v1 v2.
    Context {m' : Type@{v1} -> Type@{v2}}.
    #[global] Instance lift_over `{!MLift m' m} : MLift m' M := fun _ c =>
      mk $ (fun x => [x]) <$> mlift c.
    #[global] Arguments lift_over {_ _} & _ : assert.
  End lift.
  #[global] Instance lift_listp : MLift UTypes.list M := fun _ c => mk $ mret c.
  #[global] Instance lift_list : MLift (eta Datatypes.list) M := fun _ c =>
    mk $ mret $ mlift c.
  #[global] Instance lift_optionp : MLift UTypes.option M := fun _ c =>
    mk $ mret $ mlift c.
  #[global] Instance lift_option : MLift (eta Datatypes.option) M := fun _ c =>
    mk $ mret $ mlift c.
End listT.
