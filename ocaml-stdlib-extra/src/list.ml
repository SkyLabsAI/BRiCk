(*
 * Copyright (C) 2021-2026 SkyLabs AI, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

open Prelude

include Stdlib.List

let rec choose : 'a list list -> 'a list list = fun bs ->
  match bs with
  | []      -> [[]]
  | b :: bs ->
  let extend r = map (fun i -> i :: r) b in
  concat (map extend (choose bs))

let has_dups : type a. a cmp -> a list -> bool = fun cmp xs ->
  let module S = Set.Make(struct type t = a let compare = cmp end) in
  let rec has_dups seen xs =
    match xs with
    | []      -> false
    | x :: xs -> S.mem x seen || has_dups (S.add x seen) xs
  in
  has_dups S.empty xs

let exists_or_empty : ('a -> bool) -> 'a list -> bool = fun p l ->
  l = [] || exists p l
