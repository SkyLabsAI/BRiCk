(*
 * Copyright (C) 2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import skylabs.ltac2.extra.internal.init.
Require Import skylabs.ltac2.extra.internal.list.

(** Minor extensions to [Ltac2.Array] *)
Module Array.
  Import Ltac2 Init.
  Export Ltac2.Array.

  Ltac2 make1 (elem : 'a) : 'a array :=
    let elems := Array.make 1 elem in
    elems.

  Ltac2 make2 (elem0 : 'a) (elem1 : 'a) : 'a array :=
    let elems := Array.make 2 elem0 in
    Array.set elems 1 elem1;
    elems.

  Ltac2 make3 (elem0 : 'a) (elem1 : 'a) (elem2 : 'a) : 'a array :=
    let elems := Array.make 3 elem0 in
    Array.set elems 1 elem1;
    Array.set elems 2 elem2;
    elems.

  Ltac2 make4 (elem0 : 'a) (elem1 : 'a) (elem2 : 'a)
      (elem3 : 'a) : 'a array :=
    let elems := Array.make 4 elem0 in
    Array.set elems 1 elem1;
    Array.set elems 2 elem2;
    Array.set elems 3 elem3;
    elems.

  Ltac2 make5 (elem0 : 'a) (elem1 : 'a) (elem2 : 'a)
      (elem3 : 'a) (elem4 : 'a) : 'a array :=
    let elems := Array.make 5 elem0 in
    Array.set elems 1 elem1;
    Array.set elems 2 elem2;
    Array.set elems 3 elem3;
    Array.set elems 4 elem4;
    elems.

  Ltac2 make6 (elem0 : 'a) (elem1 : 'a) (elem2 : 'a)
      (elem3 : 'a) (elem4 : 'a) (elem5 : 'a) : 'a array :=
    let elems := Array.make 6 elem0 in
    Array.set elems 1 elem1;
    Array.set elems 2 elem2;
    Array.set elems 3 elem3;
    Array.set elems 4 elem4;
    Array.set elems 5 elem5;
    elems.

  Ltac2 make7 (elem0 : 'a) (elem1 : 'a) (elem2 : 'a)
      (elem3 : 'a) (elem4 : 'a) (elem5 : 'a) (elem6 : 'a) : 'a array :=
    let elems := Array.make 7 elem0 in
    Array.set elems 1 elem1;
    Array.set elems 2 elem2;
    Array.set elems 3 elem3;
    Array.set elems 4 elem4;
    Array.set elems 5 elem5;
    Array.set elems 6 elem6;
    elems.

  Ltac2 make8 (elem0 : 'a) (elem1 : 'a) (elem2 : 'a)
      (elem3 : 'a) (elem4 : 'a) (elem5 : 'a) (elem6 : 'a)
      (elem7 : 'a) : 'a array :=
    let elems := Array.make 8 elem0 in
    Array.set elems 1 elem1;
    Array.set elems 2 elem2;
    Array.set elems 3 elem3;
    Array.set elems 4 elem4;
    Array.set elems 5 elem5;
    Array.set elems 6 elem6;
    Array.set elems 7 elem7;
    elems.

  Ltac2 make9 (elem0 : 'a) (elem1 : 'a) (elem2 : 'a)
      (elem3 : 'a) (elem4 : 'a) (elem5 : 'a) (elem6 : 'a)
      (elem7 : 'a) (elem8 : 'a) : 'a array :=
    let elems := Array.make 9 elem0 in
    Array.set elems 1 elem1;
    Array.set elems 2 elem2;
    Array.set elems 3 elem3;
    Array.set elems 4 elem4;
    Array.set elems 5 elem5;
    Array.set elems 6 elem6;
    Array.set elems 7 elem7;
    Array.set elems 8 elem8;
    elems.

  Ltac2 of_list_map (f : 'a -> 'b) (ls : 'a list) : 'b array :=
    let len := List.length ls in
    let (arr, ls_tail) :=
      match ls with
      | []      => (Array.empty, [])
      | h :: ls => (Array.make len (f h), ls)
      end
    in
    let add i v := Array.set arr (Int.add i 1) (f v) in
    List.iteri add ls_tail; arr.

  Ltac2 of_list_map2 (f : 'a -> 'b -> 'c) (ls1 : 'a list) (ls2 : 'b list) : 'c array :=
    let len := List.length ls1 in
    let (arr, ls1_tail, ls2_tail) :=
      match (ls1, ls2) with
      | ([]       , []       ) => (Array.empty, [], [])
      | (_        , []       ) => Control.throw (Invalid_argument None)
      | ([]       , _        ) => Control.throw (Invalid_argument None)
      | (h1 :: ls1, h2 :: ls2) => (Array.make len (f h1 h2), ls1, ls2)
      end
    in
    let add i v1 v2 := Array.set arr (Int.add i 1) (f v1 v2) in
    List.iteri2 add ls1_tail ls2_tail; arr.
End Array.
