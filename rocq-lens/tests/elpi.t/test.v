(*
 * Copyright (c) 2023 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)


Require Import elpi.elpi.
Require Import elpi.apps.derive.derive.
Require Import stdpp.numbers.
Require Import Lens.Elpi.Elpi.

(* #[verbose,only(lens)] derive Record State : Set := MkState
  { value : N
  }.
Print State._value. *)

Module no_prim_projs.
  #[projections(primitive=no)]
  Record State : Set := MkState
    { value : N
    }.

  #[verbose,only(lens)] derive State.
(* State__value *)
End no_prim_projs.

Print Module no_prim_projs.

Module polymorphic.
  Record Val {T : Type} : Type :=
    { value : T }.
  #[verbose,only(lens)] derive Val.

End polymorphic.

Print Module polymorphic.

Module prim_projs.
  #[projections(primitive=yes)]
  Record State : Set := MkState
    { value : N
    }.

  #[verbose,only(lens)] derive State.
(* State__value *)
End prim_projs.

Print Module prim_projs.

#[module] derive Inductive tickle A | := stop | more : A -> tickle -> tickle.
#[module] derive Record State : Set := MkState
  { value' : N
  }.
Module Import bar.
  #[verbose,module] derive Record State : Set := MkState
    { value : N
    }.
  Record State2 : Set := MkState2
    { value : N
    }.
End bar.

(* #[only(lens)] derive State. *)
Print Module bar.
Print Module bar.State.
Print bar.State.value.
Print Module State.
Import State(State).
Print Module State.
Print State.value.

(* lens.Lens
Print lens. *)
(* #[verbose,only(lens)] derive] State. *)
(* derive[lens] State. *)

