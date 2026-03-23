(*
 * Copyright (C) 2026 Skylabs AI, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import skylabs.ltac2.extra.internal.init.

(** Functions to express comparisons in terms of a data type instead of integers. *)
Module Comparison.
  Import Ltac2.
  Import Init.

  Ltac2 Type 'a compare := 'a -> 'a -> comparison.

  Ltac2 of_int (i : int) : comparison :=
    if Int.lt i 0 then Lt
    else if Int.gt i 0 then Gt
    else Eq.

  Ltac2 to_int (c : comparison) :=
    match c with
    | Lt => -1
    | Eq => 0
    | Gt => 1
    end.

  Ltac2 lift (cmp : 'a -> 'a -> int) : 'a -> 'a -> comparison :=
    fun x y => of_int (cmp x y).

  Ltac2 lower (cmp : 'a compare) : 'a -> 'a -> int :=
    fun x y => to_int (cmp x y).

  Ltac2 compare_on (f : 'a -> 'b) (cmp : 'b compare) : 'a -> 'a -> comparison :=
    fun x y => cmp (f x) (f y).

  Ltac2 lt (cmp : 'a compare) (x : 'a) (y : 'a) : bool :=
    match cmp x y with
    | Lt => true
    | _ => false
    end.
  Ltac2 eq (cmp : 'a compare) (x : 'a) (y : 'a) : bool :=
    match cmp x y with
    | Eq => true
    | _ => false
    end.
  Ltac2 gt (cmp : 'a compare) (x : 'a) (y : 'a) : bool :=
    match cmp x y with
    | Gt => true
    | _ => false
    end.
  Ltac2 le (cmp : 'a compare) (x : 'a) (y : 'a) : bool :=
    Bool.neg (gt cmp x y).
  Ltac2 ge (cmp : 'a compare) (x : 'a) (y : 'a) : bool :=
    Bool.neg (lt cmp x y).

  Ltac2 rec lexicographical (cmp : (unit -> comparison) list) : comparison :=
    match cmp with
    | [] => Eq
    | c :: cmps =>
        let c := c () in
        match c with
        | Eq => lexicographical cmps
        | _ => c
        end
    end .

  Ltac2 lex2 (cmp_a : 'a compare) (cmp_b : 'b compare) : ('a * 'b) compare :=
    fun (x0,x1) (y0,y1) => lexicographical [(fun () => cmp_a x0 y0);(fun () => cmp_b x1 y1)].
  Ltac2 lex3 (cmp_a : 'a compare) (cmp_b : 'b compare) (cmp_c : 'c compare) : ('a * 'b * 'c) compare :=
    fun (x0,x1,x2) (y0,y1,y2) => lexicographical [(fun () => cmp_a x0 y0);(fun () => cmp_b x1 y1);(fun () => cmp_c x2 y2)].

End Comparison.

(** Utilities for comparison functions *)
Module Compare.
  Import Ltac2.

  Ltac2 compare_on (f : 'a -> 'b) (cmp : 'b -> 'b -> int) : 'a -> 'a -> int :=
    fun x y => cmp (f x) (f y).

End Compare.
