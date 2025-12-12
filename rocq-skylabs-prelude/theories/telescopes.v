(*
 * Copyright (c) 2020-2021 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Export stdpp.telescopes.
Require Export bluerock.prelude.base.

#[local] Set Universe Polymorphism.
#[local] Set Polymorphic Inductive Cumulativity.
#[local] Unset Universe Minimization ToSet.

Fixpoint tele_append (t : tele) {struct t}: (t -t> tele) -> tele :=
  match t as t return (t -t> tele) -> tele with
  | TeleO => fun x : tele => x
  | @TeleS T f => fun x => @TeleS T (fun t => tele_append (f t) (x t))
  end.

Definition tele_fun_pointwise@{X Z Y} {t : tele@{X}} {A : Type@{Z}}
    (R : A -> A -> Prop) (f g : tele_fun@{X Z Y} t A) : Prop :=
  forall x, R (tele_app f x) (tele_app g x).

Fixpoint tele_snoc (t : tele) (T : Type) : tele :=
  match t with
  | TeleO => TeleS (fun _ : T => TeleO)
  | @TeleS U f => TeleS (fun x : U => tele_snoc (f x) T)
  end.

Fixpoint tele_bind_snoc {U} {TT : tele} {T : Type}
  : (TT -> T -> U) -> tele_snoc TT T -t> U :=
  match TT as TT
        return (TT -> T -> U) -> tele_snoc TT T -t> U
  with
  | TeleO => fun F x => F tt x
  | @TeleS U f => fun F x => tele_bind_snoc (TT:=f x) (T:=T) (fun fx t => F (TeleArgCons x fx) t)
  end.

Fixpoint tele_arg_snoc {TT : tele} {T : Type}
  : TT -> T -> tele_snoc TT T :=
  match TT as TT
        return TT -> T -> tele_snoc TT T
  with
  | TeleO => fun _ t => TeleArgCons t ()
  | @TeleS U f => fun '(TeleArgCons x xs) t => TeleArgCons x (tele_arg_snoc xs t)
  end.

Fixpoint tele_bind_append {U} {TT1 : tele}
  : forall {TT2 : TT1 -t> tele},
    (forall args : TT1, tele_app TT2 args -> U) -> tele_append TT1 TT2 -t> U :=
  match TT1 as TT1
        return forall {TT2 : TT1 -t> tele},
      (forall args : TT1, tele_app TT2 args -> U) -> tele_append TT1 TT2 -t> U
  with
  | TeleO => fun _ f => tele_bind (f ()) (* fun F => tele_bind $ F () *)
  | @TeleS U F => fun _ f (x : U) =>
      tele_bind_append (TT1:=F x) (TT2:=_) (fun args => f (TeleArgCons x args))
  end.

Fixpoint tele_arg_append {TT1}
  : forall {TT2 : TT1 -t> tele}, forall args : tele_arg TT1, tele_arg (tele_app TT2 args) -> tele_append TT1 TT2 :=
  match TT1 as TT1
        return forall (TT2 : TT1 -t> tele) (args : tele_arg TT1),
      tele_arg (tele_app TT2 args) -> tele_append TT1 TT2

  with
  | TeleO => fun _ _ x => x
  | TeleS F => fun _ '(TeleArgCons x xs) args =>
                TeleArgCons x $ @tele_arg_append (F x) _ xs args
  end.
