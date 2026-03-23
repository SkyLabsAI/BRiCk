(*
 * Copyright (C) 2022-2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

Require Ltac2.Ltac2.

(** Minor extensions to [Ltac2.List]. *)
Module List.
  Import Ltac2.
  Export Ltac2.List.

  Ltac2 iteri2 (f : int -> 'a -> 'b -> unit) (xs : 'a list) (ys : 'b list) :=
    let rec loop i xs ys :=
      match (xs, ys) with
      | ([]     , []     ) => ()
      | ([]     , _      ) => Control.throw (Invalid_argument None)
      | (_      , []     ) => Control.throw (Invalid_argument None)
      | (x :: xs, y :: ys) => f i x y; loop (Int.add i 1) xs ys
      end
    in
    loop 0 xs ys.

  (** These variants avoid silly edits when switching direction. *)

  Ltac2 foldl (f : 'a -> 'b -> 'b) (xs : 'a list) (acc : 'b) : 'b :=
    List.fold_left (fun acc x => f x acc) acc xs.
  Ltac2 foldr := List.fold_right.

  Ltac2 foldli (f : int -> 'a -> 'b -> 'b) (xs : 'a list) (acc : 'b) : 'b :=
    let rec go i acc xs :=
      match xs with
      | [] => acc
      | x :: xs => go (Int.add i 1) (f i x acc) xs
      end
    in go 0 acc xs.

  Ltac2 foldl2 (f : 'a -> 'b -> 'c -> 'c)
      (xs : 'a list) (ys : 'b list) (acc : 'c) : 'c :=
    List.fold_left2 (fun acc x y => f x y acc) xs ys acc.
  Ltac2 foldr2 (f : 'a -> 'b -> 'c -> 'c)
      (xs : 'a list) (ys : 'b list) (acc : 'c) : 'c :=
    List.fold_right2 f xs ys acc.

  Ltac2 rec find_map_opt (f : 'a -> 'b option) (xs : 'a list) : 'b option :=
    match xs with
    | [] => None
    | x :: xs => match f x with
                 | Some x => Some x
                 | None => find_map_opt f xs
                 end
    end.

  Ltac2 split_at (n : int) (xs : 'a list) : 'a list * 'a list :=
    let rec go n xs acc :=
      if Int.le n 0 then
        (List.rev acc, xs)
      else
        match xs with
        | [] => (List.rev acc, [])
        | x :: xs =>

            go (Int.sub n 1) xs (x :: acc)
        end in
    go n xs [].

  (* [bisect_partition ps xs]
     Assuming for some predicate [ps : 'a -> bool], [ps xs = List.for_all p xs], [bisect_partition] is
     characterized by [bisect_partition ps xs = List.partition p xs]. It offers better performances
     then [List.for_all] in terms of the number of calls to [ps].

     If every elements [x ∈ xs] satisfies [p x], [ps] is called only once.

     If only one elemeent [x ∈ xs] does *not* satisfy [p x], then
        i)  one of two halves of [xs], the one where [x] does *not* reside, can be partitioned using
            a single call to [ps]
        ii) the other half can again be split into two halves, one of which requires only a single
            call to [ps].
            ...
        log n) xs can be repeatedly split into two parts and [ps] will be called [log n] times,
               where [n = length xs].

     If two elements, [x, y ∈ xs] do *not* satisfy [p], [ps] will be called at most [2 * log n]
     times (if they are located in separate halves of [xs]) and at least [log n] times (if they are
     next to each other).

     The worse case performances obtain when no two consecutive elements of [xs] both satisfy [p]. [ps]
     will then be called [2 * n]. They can be improved by switching to linear search for small sizes of [n].

     Thus, the run goes from [O(log n)] to [O(n)] depending on the number and dispersion of elements of [xs]
     which do not satisfy [p]
   *)
  Ltac2 bisect_partition (ps : 'a list -> bool) (xs : 'a list) : 'a list * 'a list :=
    let min_len := 4 in
    let rec go len xs (acc0, acc1) :=
      if ps xs then
        (List.append xs acc0, acc1)
      else if Int.le len min_len then
        let (ys0, ys1)  :=
            List.partition
                     (fun l => ps [l])
                     xs in
        let acc0 := List.append ys0 acc0 in
        let acc1 := List.append ys1 acc1 in
        (acc0, acc1)
      else
        let len0 := Int.div len 2 in
        let len1 := Int.sub len len0 in
        let (xs0,  xs1)  := split_at len0 xs in
        let (acc0, acc1) := go len1 xs1 (acc0, acc1) in
        let (acc0, acc1) := go len0 xs0 (acc0, acc1) in
        (acc0, acc1) in
    let len := List.length xs in
    go len xs ([], []).

  (** Note: We have a "smart" list mapper in ML that works in the [Proofview]
      monad and uses Caml's [==] to promote sharing.

      We cannot lift it to an external Ltac2 function [List.Smart.map] of type
      [('a -> 'a) -> 'a list -> 'a list] due to the way that Ltac2's [repr]
      for list works. Under the hood, it is roughly [List.map]. Every time a
      list crosses the FFI boundary, we get a new list.

      We could perhaps write a [List.Smart.map] function in Ltac2 by adding an
      external primitive [==] (on ML type [valexpr]). *)
End List.
