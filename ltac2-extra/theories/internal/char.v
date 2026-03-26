(*
 * Copyright (C) 2022-2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import skylabs.ltac2.extra.internal.init.
Require Import skylabs.ltac2.extra.internal.constr.

Require Import Stdlib.Strings.Ascii.

(** Minor extensions to [Ltac2.Char] *)
Module Char.
  Import Ltac2 Init.
  Export Ltac2.Char.

  (** [of_ascii_constr c] attempts to convert the Coq term [c], intended to be
      a full application of [Ascii] to concrete booleans, into a character. *)
  Ltac2 of_ascii_constr (c : constr) : char option :=
    let bool_to_int (t : constr) : int option :=
      lazy_match! t with
      | true  => Some 1
      | false => Some 0
      | _     => None
      end
    in
    let add xo yo :=
      Option.bind xo (fun x => Option.bind yo (fun y => Some (Int.add x y)))
    in
    let mul2 xo := Option.bind xo (fun x => Some (Int.mul 2 x)) in
    lazy_match! c with
    | Ascii ?b0 ?b1 ?b2 ?b3 ?b4 ?b5 ?b6 ?b7 =>
        let n :=              (bool_to_int b7) in
        let n := add (mul2 n) (bool_to_int b6) in
        let n := add (mul2 n) (bool_to_int b5) in
        let n := add (mul2 n) (bool_to_int b4) in
        let n := add (mul2 n) (bool_to_int b3) in
        let n := add (mul2 n) (bool_to_int b2) in
        let n := add (mul2 n) (bool_to_int b1) in
        let n := add (mul2 n) (bool_to_int b0) in
        Option.bind n (fun n => Some (of_int n))
    | _ => None
    end.

  (** [to_ascii_constr c] converts a character into a Rocq term, the full application of [Ascii] to
      concrete booleans. *)
  Ltac2 to_ascii_constr (c : char) : constr :=
    let lsb (n : int) : constr * int :=
      let b := Int.mod n 2 in
      let n := Int.div n 2 in
      let b := if Int.equal b 1 then '(true) else '(false) in
      (b, n) in
    let n := Char.to_int c in
    let (b0, n) := lsb n in
    let (b1, n) := lsb n in
    let (b2, n) := lsb n in
    let (b3, n) := lsb n in
    let (b4, n) := lsb n in
    let (b5, n) := lsb n in
    let (b6, n) := lsb n in
    let (b7, n) := lsb n in
    Control.assert_true (Int.equal n 0) ;
    Constr.Unsafe.make_app '(Ascii) [|b0;b1;b2;b3;b4;b5;b6;b7|].

End Char.
