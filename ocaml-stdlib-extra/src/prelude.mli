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

(** [wrn fmt] outputs the warning message specified by [fmt] (and the attached
    arguments) to [stderr]. A newline is automatically added at the end of the
    message, and [stderr] is also flushed. *)
val wrn : 'a Format.outfmt -> 'a

(** [err fmt] is the same as [wrn fmt], but outputs an error message. *)
val err : 'a Format.outfmt -> 'a

(** [panic ?code fmt] prints the error message specified by [fmt] to [stderr],
    and interrupts the program with [exit code] (with [code] defaulting to 1).
    A newline is automatically inserted, and [stderr] is flushed. Warning: you
    must fully apply the function for the error to trigger. *)
val panic : ?code:int -> ('a, 'b) Format.koutfmt -> 'a
