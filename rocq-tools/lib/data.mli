(*
 * Copyright (C) 2023-2024 BlueRock Security, Inc.
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

(** Type of profiling data attached to a single Rocq command. *)
type cmd = private {
  cmd_line  : int;
  (** Line where the command starts in the source file. *)
  cmd_sbyte : int;
  (** Index of the first byte of the command in the file. *)
  cmd_ebyte : int;
  (** Index of the last byte of the command in the file. *)
  cmd_text  : string;
  (** Text of the command (full text only when short, ellipsis otherwise). *)
  cmd_ic    : int;
  (** Instruction count for the command. *)
}

(** [make_cmd ~line ~sbyte ~ebyte ~text ~ic] constructs a [cmd] record. *)
val make_cmd :
  line:int -> sbyte:int -> ebyte:int -> text:string -> ic:int -> unit -> cmd

(** Type of profiling data for a Rocq file. *)
type t = {
  ic : int;
  (** Instruction count for processing the whole file. *)
  tm : int;
  (** Time for processing the whole file (in micro-seconds). *)
  mj : int;
  (** Number of words allocated on the major heap for processing the file. *)
  mn : int;
  (** Number of words allocated on the minor heap for processing the file. *)
  cs : cmd array
  (** Data for all the commands in the file (in order). *)
}

(** [make ~ic cmds] constructs a data record. *)
val make : ic:int -> tm:int -> mj:int -> mn:int -> cmd array -> t

(** [to_json data] converts the given [data] into JSON. The produced object is
    formed of two fields:
    - ["i"] - an integer giving the CPU instruction count for the full "rocq"
      process (except the OCaml runtime initialization / finalization),
    - ["a"] - an array of objects giving data about each individual, toplevel  
      Rocq command that was processed.
    The objects stored in the latter field contain the following fields:
    - ["l"] (integer) - the number of the line on which the command starts,
    - ["s"] (integer) - the index of the first command's byte in the file,
    - ["e"] (integer) - the index of the last command's byte in the file,
    - ["p"] (string) - the first few characters of the command (at least),
    - ["i"] (integer) - CPU instruction counts for the command. *)
val to_json : t -> JSON.t

(** [of_json o] tries to convert the JSON object [o] into profiling data. This
    only succeeds with [Some(_)] if [o] is well-formed, and [None] is returned
    otherwise. Objects [o] returned by [as_json] are guaranteed to be be well-
    formed. *)
val of_json : JSON.t -> t option

(** Exception raised by [read]. *)
exception Read_error of string

(** [read_json path] opens the (JSON) file indentified by [path], and attempts
    to interpret it as profiing data. In case of error with file manipulation,
    the [Sys_error] exception is raised. If the contents of the file is not of
    the expected shape, then the [Read_error] exception is raised. *)
val read_json : string -> t

(** [write_json path data] converts the given [data] to JSON, and writes it to
    the file identified by [path]. The [Sys_error] exception is raised in case
    of a file manipulation error. *)
val write_json : string -> t -> unit

(** [add_noise p data] returns a copy of [data] with noise added to the fields
    containing instruction counts, timings or memory usage data. The parameter
    [p] indicates that values are changed by a factor of [p] at most. Example:
    if [p] is [0.1], then the added noise is at most 10% of the initial value,
    in absolute terms. *)
val add_noise : Float.t -> t -> t
