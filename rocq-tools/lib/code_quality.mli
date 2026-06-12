(*
 * Copyright (C) 2023-2025 BlueRock Security, Inc.
 *
 * This library is free software; you can redistribute it and/or modify it
 * under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation; version 2.1.
 *
 * This library is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General Public License
 * for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this library; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA
 *)

type pos = {
  line : int; (* Line number.  *)
  c0   : int; (* Start column. *)
  c1   : int; (* End column.   *)
}

module Warning : sig
  type t = {
    file : string;     (* File where the warning originated.     *)
    pos  : pos option; (* Optional warning position in the file. *)
    name : string;     (* Name for the warning.                  *)
    text : string;     (* Text from the warning.                 *)
    full : string;     (* Original content including headers     *)
  }

  (* Flaky warning are warnings whose text might change spuriously. Two flaky
     warnings will be considered identical if they are equal up to their
     text. *)
  val is_flaky : t -> bool

  (* [compare] compares warnings modulo flaky texts *)
  val compare : t -> t -> int
end

module Error : sig
  type t = {
    file : string;
    pos  : pos option;
    text : string;
    full : string;
  }

  val compare : t -> t -> int
end

type line =
  | Header of { file : string; pos: pos option; full: string (* full line *) }
  | Data of string * bool (* Is this the last warning line? *)

val parse_line : string -> line
val parse_lines : ?assume_errors:bool -> line list -> (int * string) list * Warning.t list * Error.t list
