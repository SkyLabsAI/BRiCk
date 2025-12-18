(*
 * Copyright (C) 2022-2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

Require Stdlib.Numbers.BinNums.
Require Stdlib.PArith.BinPos.
Require skylabs.ltac2.extra.internal.plugin.
Require Import skylabs.ltac2.extra.internal.init.
Require Import skylabs.ltac2.extra.internal.constr.
Require Import skylabs.ltac2.extra.internal.std.

(** Minor extensions to [Ltac2.Int] *)
Module Int.
  Import Ltac2 Init Constr.Unsafe.
  Export Ltac2.Int.

  (** [of_ascii_constr c] attempts to convert the Coq term [c], intended to be
      a full application of [Ascii] to concrete booleans, into a character. *)
  Ltac2 as_nat : int -> constr := fun n =>
    let s := constr:(S) in
    let z := constr:(O) in
    let rec go n acc :=
      if Int.le n 0 then acc else go (Int.sub n 1) (make_app1 s acc)
    in
    go n z.

  Ltac2 of_pos : constr -> int := fun p =>
    let rec go p :=
      lazy_match! Std.eval_whd_all p with
      | BinNums.xH => 1
      | BinNums.xO ?p =>
        let r := go p in
        Int.mul 2 r
      | BinNums.xI ?p =>
        let r := go p in
        (Int.add 1 (Int.mul 2 r))
      end
    in go p.

  Ltac2 of_nat' () : constr -> int :=
    let pon := '@BinPos.Pos.of_nat in
    fun n =>
    let n := Std.eval_whd_all n in
    lazy_match! n with
    | O => 0
    | _ => of_pos (make_app1 pon n)
  end.
  Ltac2 of_nat n : int := of_nat' () n.

  Ltac2 rec to_bits (acc : bool list) (i : int) : bool list :=
    if Int.le i 1 then
      acc
    else
      let b := Int.equal (Int.land i 1) 1 in
      let i := Int.lsr i 1 in
      to_bits (b::acc) i.

  Ltac2 as_pos' () : int -> constr :=
    let xH := constr:(BinNums.xH) in
    let xO := constr:(BinNums.xO) in
    let xI := constr:(BinNums.xI) in
    let rec go (acc : bool list) : constr :=
      match acc with
      | [] => xH
      | b :: acc => make_app1 (if b then xI else xO) (go acc)
      end
    in
    fun i => go (List.rev (to_bits [] i)).

  Ltac2 as_pos i := as_pos' () i.

  Module Map.
    Ltac2 Type 'a t.

    Ltac2 @ external empty : 'a t :=
      "br.IntMap" "empty".

    Ltac2 @ external is_empty : 'a t -> bool :=
      "br.IntMap" "is_empty".

    Ltac2 @ external mem : int -> 'a t -> bool :=
      "br.IntMap" "mem".

    Ltac2 @ external add : int -> 'a -> 'a t -> 'a t :=
      "br.IntMap" "add".

    Ltac2 @ external singleton : int -> 'a -> 'a t :=
      "br.IntMap" "singleton".

    Ltac2 @ external remove : int -> 'a t -> 'a t :=
      "br.IntMap" "remove".

    Ltac2 @ external cardinal : 'a t -> int :=
      "br.IntMap" "cardinal".

    Ltac2 @ external bindings : 'a t -> (int * 'a) list :=
      "br.IntMap" "bindings".

    Ltac2 @ external find_opt : int -> 'a t -> 'a option :=
      "br.IntMap" "find_opt".

    Ltac2 @ external min_binding_opt : 'a t -> (int * 'a) option :=
      "br.IntMap" "min_binding_opt".

    Ltac2 @ external max_binding_opt : 'a t -> (int * 'a) option :=
      "br.IntMap" "max_binding_opt".
  End Map.
End Int.
