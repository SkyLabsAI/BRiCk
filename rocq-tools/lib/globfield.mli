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

(** Encoding of custom fields into Rocq "glob" files. *)

(** Mode for encoded fields. *)
type mode = Binary | Text

(** Representation of the contents of a Rocq "glob" file. *)
type glob_file

(** [fold_fields f glob acc] folds [f] over the custom fields of [glob], using
    [acc] as initial accumulator. Note that fields are visited in the order of
    their integer keys. *)
val fold_fields : (key:int -> mode:mode -> value:Base64.t -> 'a -> 'a) ->
  glob_file -> 'a -> 'a

(** [iter_fields f glob] iterates [f] over the custom fields of [glob], in the
    order of their integer keys. *)
val iter_fields : (key:int -> mode:mode -> value:Base64.t -> unit) ->
  glob_file -> unit

(** [find_field ~key glob] finds the mode and value mapped to the given [key].
    If there is no mapping for [key], [Not_found] is raised. If [key < 0], the
    [Invalid_argument] exception is raised. *)
val find_field : key:int -> glob_file -> mode * Base64.t

(** [add_field ~key ~mode ~value glob] extends [glob] with a new field mapping
    [key] to the given [value] with the given [mode]. When [key] is already in
    [glob], then the old binding is removed. Note that if [key < 0], exception
    [Invalid_argument] is raised. *)
val add_field : key:int -> mode:mode -> value:string -> glob_file -> glob_file

(** [remove_field ~key glob] removes the binding for [key] from [glob]. If key
    [key] was not mapped in [glob], then [glob] is returned unchanged. As with
    [add_field], [Invalid_argument] is raised if [key < 0]. *)
val remove_field : key:int -> glob_file -> glob_file

(** Exception raised by the functions that interpret glob files. *)
exception Bad_glob_file

(** [read_glob_file ~allow_fields file] opens and parses the given [file] as a
    Rocq "glob" file. If [file] is ill-formed, [Bad_glob_file] is raised. This
    can happen if [allow_fields] is [false] and [file] has ustom field. In the
    case of a file system error, exception [Sys_error] is raised. *)
val read_glob_file : allow_fields:bool -> string -> glob_file

(** [write_glob_file path glob] writes [glob] to the file identified by [path]
    (if a file already exists, it is truncated to 0). Exception [Sys_error] is
    raised in case of file manipulation error. *)
val write_glob_file : string -> glob_file -> unit

(** [write_field ~assume_new path ~key ~mode ~value] adds a new mapping of the
    [key] to [mode] and [value] to the "glob" file identified by [path]. If it
    is not initially well-formed, exception [Bad_glob_file] may be raised. The
    [Sys_error] exception is raised upon file manipulation errors. If the flag
    [assume_new] is [true], then the file is not read at all, and a mapping is
    simply inserted at the end of the file. This is *always* safe, since later
    mappings override previous ones, but this can lead to larger files. If the
    [key] is negative, [Invalid_argument] is raised. *)
val write_field : assume_new:bool -> string -> key:int -> mode:mode ->
  value:string -> unit

(** [write_fields ~assume_new path mappints] is similar to [write_fields], but
    allows for writting several fields at once. *)
val write_fields : assume_new:bool -> string -> (int * mode * string) list ->
  unit

(** [read_field path ~key] returns the mode and value pair mapped to the given
    [key] in the Rocq "glob" file identified by [path]. If no binding is found
    the [Not_found] exception is raised.  The [Bad_glob_file] exception may be
    raised if the file is ill-formed. The [Sys_error] exception is raised upon
    file manipulation errors.  The [Invalid_argument] exception is raised when
    [key < 0]. *)
val read_field : string -> key:int -> mode * Base64.t

(** [read_fields path ~keys] is similar to [read_field], but allows reading an
    arbitrary number of fields at once. The [Not_found] exception is triggered
    if any of the keys is missing. *)
val read_fields : string -> keys:int list -> (int * mode * Base64.t) list

(** [read_all_fields path] returns the field mapping from the Rocq "glob" file
    identified by [path]. The [Bad_glob_file] exception may be raised when the
    file is ill-formed. Exception [Sys_error] is raised upon file manipulation
    errors. *)
val read_all_fields : string -> (int * mode * Base64.t) list
