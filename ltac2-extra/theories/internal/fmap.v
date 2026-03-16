(*
 * Copyright (C) 2022-2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import skylabs.ltac2.extra.internal.init.
Require Import skylabs.ltac2.extra.internal.printf.
Require Import skylabs.ltac2.extra.internal.list.

(** Minor extensions to [Ltac2.FMap] *)
Module FMap.
  Import Ltac2 Init Printf.
  Export Ltac2.FMap .

  Ltac2 alter (v0 : 'v) (k : 'k) (f : 'v -> 'v) (m : ('k,'v) FMap.t) : ('k,'v) FMap.t :=
    match FMap.find_opt k m with
    | Some v => FMap.add k (f v) m
    | None => FMap.add k (f v0) m
    end.

  Ltac2 of_list (tag : 'k FSet.Tags.tag) (xs : ('k * 'a) list) : ('k, 'a) FMap.t :=
    List.foldl (fun (k, v) => FMap.add k v) xs (FMap.empty tag).

  Ltac2 filter_mapi (f : 'k -> 'a -> 'b option) (map : ('k, 'a) FMap.t) : ('k, 'b) FMap.t :=
    let map := mapi f map in
    let map := FMap.fold
      (fun k v acc =>
         if Option.is_none v then FMap.remove k acc
      else acc ) map map in
    FMap.mapi (fun _ v => Option.get v) map.

  Ltac2 filteri (f : 'k -> 'a -> bool) : ('k, 'a) FMap.t -> ('k, 'a) FMap.t :=
    filter_mapi
      (fun k v => if f k v then Some v else None).

  Ltac2 pp (pp_k : 'k pp) (pp_a : 'a pp) : ('k, 'a) FMap.t pp :=
    fun () map =>
    if FMap.is_empty map then
      fprintf "{}"
    else
      let pp_pair () (k, a) := fprintf "(%a,%a)" pp_k k pp_a a in
      fprintf "{%a}" (pp_list_sep ", " pp_pair) (FMap.bindings map).

End FMap.
