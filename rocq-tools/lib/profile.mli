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

(** Extracting per-command profiling data from Rocq output. *)

(** Exception raised by [extract] in case of error. *)
exception Error of string

(** Exception raised by [extract] if instruction counts are not included. *)
exception NoInstr

(** [extract o] extracts per-command profiling data from the given JSON object
    [o], assumed to have been produced by running "rocq" with "-profile". Note
    that the exception [Error(_)] is raised if the object is not recognised as
    a well-formed Rocq profiling data output. Exception [NoInstr] is raised if
    the profiling data does not contain instruction counts. This may happen if
    Rocq was not compiled with instruction count support, or if the data fails
    to be read for some reason (e.g., lack of privileges). *)
val extract : JSON.t -> Data.t
