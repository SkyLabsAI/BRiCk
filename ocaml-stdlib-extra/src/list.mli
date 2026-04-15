(*
 * Copyright (C) 2021-2026 SkyLabs AI, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

(** Extension of [Stdlib.List]. *)

open Prelude

include module type of Stdlib.List

(** [choose bs] takes as input a list of buckets [bs], and it generates a list
    of all the possible ways to pick one element from each bucket. *)
val choose : 'a list list -> 'a list list

(** [has_dups cmp l] indicates whether the list [l] has duplicates  (according
    to the comparison function [cmp]). *)
val has_dups : 'a cmp -> 'a list -> bool

(** [exists_or_empty p l] is similar to [exists p l], but it returns [true] if
    the list [l] is empty. *)
val exists_or_empty : ('a -> bool) -> 'a list -> bool
