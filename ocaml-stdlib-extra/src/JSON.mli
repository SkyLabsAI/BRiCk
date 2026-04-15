(*
 * Copyright (C) 2021-2026 SkyLabs AI, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

(** High-level JSON interface. *)

(** Type of JSON data, same as [Yojson.Basic]. *)
type t = [
  | `Null
  | `Bool of bool
  | `Int of int
  | `Float of float
  | `String of string
  | `Assoc of (string * t) list
  | `List of t list
]

(** Exception raised by [from_channel] and [from_file]. *)
exception Error of string

(** [from_channel ic] reads a JSON value from the input channel [ic]. When the
    function fails to parse such a value, the [Error] exception is raised. The
    [Sys_error] exception is raised on file system errors. *)
val from_channel : In_channel.t -> t

(** [from_file file] reads the given [file] into a JSON value. If the contents
    if the file cannot be parsed, the [Error] exception is raised. If there is
    a an error with the file system, [Sys_error] is raised. *)
val from_file : string -> t

(** [write oc json] write the given [json] to the output channel [oc]. In case
    of file system error, the [Sys_error] exception is raised. *)
val write : Stdlib.out_channel -> t -> unit
