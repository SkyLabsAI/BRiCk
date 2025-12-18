(*
 * Copyright (C) 2023-2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import skylabs.upoly.prelude.
Require Import skylabs.upoly.base.
Require Import skylabs.upoly.UTypes.
Require skylabs.upoly.trace.
Import UPoly.

(** * Trace monad transformer *)
(**
This module is not meant to be <<Import>>ed.
*)

Record M@{*uE *u1 *u2 *uA | uE <= u1, uA <= u1}
    {E : Type@{uE}} {m : Type@{u1} -> Type@{u2}} {A : Type@{uA}} :=
  mk { runp : m (trace.M E A) }.
Add Printing Constructor M.
#[global] Arguments M : clear implicits.
#[global] Arguments mk {_ _ _} _ : assert.
#[global] Arguments runp {_ _ _} & _ : assert.

Definition run {E m A} `{!FMap m} (c : M E m A)
    : m (Datatypes.sum (Datatypes.list E) A)%type :=
  trace.run <$> runp c.
#[global] Arguments run _ _ _ _ &_ : assert.

Definition runO {E m A} `{!FMap m} (c : M E m A) : m (Datatypes.option A)%type :=
  trace.runO <$> runp c.
#[global] Arguments runO _ _ _ _ &_ : assert.

Section traceT.
  Universes uE u1 u2.
  Constraint uE <= u1.
  Context {E : Type@{uE}} {m : Type@{u1} -> Type@{u2}}.
  Context `{!FMap m, !MRet m}.
  #[local] Notation U := (trace.M E).
  #[local] Notation M := (M E m).

  #[global] Instance map : FMap M := fun _ _ f x =>
    mk $ fmap f <$> runp x.
  #[global] Arguments map {_ _} _ & _ : assert.

  #[global] Instance ret : MRet M := fun _ x =>
    mk $ mret $ mret x.
  #[global] Arguments ret {_} & _ : assert.

  #[global] Instance join `{!MBind m} : MJoin M := fun _ c =>
    mk $
    letM* t := runp c in
    match t with
    | trace.Success c => runp c
    | trace.Backtrace t => mret $ trace.Backtrace t
    end.
  #[global] Arguments join {_ _} & _ : assert.

  #[global] Instance bind `{!MBind m} : MBind M := fun A B f c =>
    mjoin (f <$> c).
  #[global] Arguments bind {_ _ _} _ & _ : assert.

  #[global] Instance ap `{!Ap m} : Ap M | 1000 := fun _ _ f c =>
    mk $ ap (F:=U) <$> runp f <*> runp c.
  #[global] Arguments ap {_ _ _} & _ _ : assert.

  (**
  TODO: Perhaps we could usefully lift <<Traverse>> from <<m>> to
  <<M>>
  *)

  #[global] Instance fail : MFail M := fun _ _ =>
    mk $ mret $ mfail.
  #[global] Arguments fail {_} _ : assert.

  #[global] Instance trace : Trace E M := fun e _ c =>
    mk $ trace e <$> runp c.
  #[global] Arguments trace _ {_} & _ : assert.

  #[global] Instance throw : MThrow E M := fun _ e =>
    mk $ mret $ mthrow e.
  #[global] Arguments throw {_} _ : assert.

  #[global] Instance catch `{!MBind m} : MCatch (list E) M :=
    fun A (c : M A) (h : list E -> M A) =>
    mk $
    letM* c := runp c in
    match c with
    | trace.Success _ => mret c
    | trace.Backtrace t => runp $ h t
    end.
  #[global] Arguments catch {_ _} & _ _ : assert.

  (**
  We would prefer to avoid <<MBind>>. See [optionT.alternative].
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
  #[global] Instance throw' {E} `{!MThrow E m} : MThrow E M := fun _ e =>
    mk $ mthrow e.
  #[global] Arguments throw' {_ _ _} _ : assert.

  #[global] Instance catch' {E} `{!MCatch E m} : MCatch E M := fun _ c h =>
    mk $ mcatch (runp c) (fun e => runp (h e)).
  #[global] Arguments catch' {_ _ _} & _ _ : assert.

  #[global] Instance lift : MLift m M := fun A c =>
    mk $ trace.Success <$> c.
  #[global] Arguments lift {_} & _ : assert.

  Section lift.
    Universes v1 v2.
    Context {m' : Type@{v1} -> Type@{v2}}.
    #[global] Instance lift_over `{!MLift m' m} : MLift m' M := fun _ c =>
      mk $ trace.Success <$> mlift c.
    #[global] Arguments lift_over {_ _} & _ : assert.
  End lift.
  #[global] Instance lift_trace : MLift U M := fun A c =>
    mk $ mret $ c.
  #[global] Instance lift_optionp : MLift UTypes.option M := fun _ c =>
    mk $ mret $ mlift c.
  #[global] Instance lift_option : MLift (eta Datatypes.option) M := fun _ c =>
    mk $ mret $ mlift c.
End traceT.
