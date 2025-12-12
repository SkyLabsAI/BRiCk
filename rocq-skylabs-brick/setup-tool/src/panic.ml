(*
 * SPDX-License-Identifier: BSD-3-Clause
 * Copyright: RefinedC developers and contributors 2020-2023
 * Copyright: 2024 BlueRock Security, Inc.
 *)

(** Output and debugging utilities. *)

(** Short name for a standard formatter. *)
type 'a outfmt = ('a, Format.formatter, unit) format

(** Short name for a standard formatter with continuation. *)
type ('a, 'b) koutfmt = ('a, Format.formatter, unit, unit, unit, 'b) format6

(** Format transformers (colors). *)
let with_color k fmt = "\027[" ^^ k ^^ "m" ^^ fmt ^^ "\027[0m%!"

let red fmt = with_color "31" fmt
let gre fmt = with_color "32" fmt
let yel fmt = with_color "33" fmt
let blu fmt = with_color "34" fmt
let mag fmt = with_color "35" fmt
let cya fmt = with_color "36" fmt

let info : 'a outfmt -> 'a = Format.printf

(** [wrn fmt] outputs the warning message specified by [fmt] (and the attached
    arguments) to [stderr]. A newline is automatically added at the end of the
    message, and [stderr] is also flushed. *)
let wrn : 'a outfmt -> 'a = fun fmt ->
  Format.eprintf (yel (fmt ^^ "\n%!"))

(** [err] is the same as [wrn], but outputs an error message. *)
let err : 'a outfmt -> 'a = fun fmt ->
  Format.eprintf (red (fmt ^^ "\n%!"))

(** [panic fmt] outputs the error message specified by [fmt] (and the attached
    arguments) to [stderr], and interupts the program with [exit 1]. A newline
    is automatically inserted, and [stderr] is also flushed. *)
let panic : ('a,'b) koutfmt -> 'a = fun fmt ->
  Format.kfprintf (fun _ -> exit 1) Format.err_formatter (red (fmt ^^ "\n%!"))
