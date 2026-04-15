(*
 * Copyright (C) 2021-2026 SkyLabs AI, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

(** Type of a standard equality function. *)
type 'a eq = 'a -> 'a -> bool

(** Type of a standard comparison function. *)
type 'a cmp = 'a -> 'a -> int

(** [failwith ~fail fmt] is equivalent to calling [fail msg] (or, if [fail] is
    not given, [Stdlib.failwith msg]), where [msg] is an error message that is
    built from the format [fmt] and the extra arguments it specifies. Warning:
    the function must be fully applied for the exception to trigger. *)
val failwith : ?fail:(string -> 'e) -> ('a, 'e) Format.koutfmt -> 'a
