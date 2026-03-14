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

  Ltac2 rec tails (xs : 'a list) : 'a list list :=
    match xs with
    | [] => []
    | _x :: xs =>
        xs :: tails xs
    end .

  Ltac2 inits (xs : 'a list) : 'a list list :=
    List.map List.rev (tails (List.rev xs)).

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

  Ltac2 rec first_some f xs :=
    match xs with
    | [] => None
    | x :: xs => match f x with
                 | Some x => Some x
                 | None => first_some f xs
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

  (** Note: We have a "smart" list mapper in ML that works in the [Proofview]
      monad and uses Caml's [==] to promote sharing.

      We cannot lift it to an external Ltac2 function [List.Smart.map] of type
      [('a -> 'a) -> 'a list -> 'a list] due to the way that Ltac2's [repr]
      for list works. Under the hood, it is roughly [List.map]. Every time a
      list crosses the FFI boundary, we get a new list.

      We could perhaps write a [List.Smart.map] function in Ltac2 by adding an
      external primitive [==] (on ML type [valexpr]). *)
End List.
