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

(** Minimal "file system" embedded into Rocq "glob" files. *)

(** Path to a regular file. All functions in this module except values of type
    [file_path] to represent valid paths to existing regular files. If that is
    not they case, such function will raise [Invalid_arguments]. Moreover, the
    path to "glob" files, always passed as labelled argument [glob], must have
    extension [".glob"], otherwise [Invalid_argument] is also raised. If there
    is a file manipulations in any function, [Sys_error] is raised. *)
type file_path = string

(** Files that are embedded into a Rocq glob file, say ["dir/file.glob"], have
    an associated [key], which encodes an extension of their file paths. These
    keys can be thought of as a "file paths", where ['.'] is used as directory
    separator instead of ['/']. With the above "glob" file, a key that encodes
    ["path1.path2"] is mapped to ["dir/file.glob.path1.path2"]. Note that Keys
    may not be uniquely mapped in a "glob" files, since file can only be added
    and not removed. Functions of this module only deal with this last mapping
    unless otherwise specified. *)
module Key : sig
  (** Type of a key. *)
  type t

  (** [of_string s] parses the string [s] as a key. The string [s] is expected
      to consist in a dot-separated sequence of identifiers, each matching the
      regexp ["[a-zA-Z][a-zA-Z0-9_]*"]. If that is not the case, the exception
      [Invalid_argument] is raised. *)
  val of_string : string -> t

  (** [to_string ~key] gives the string representation of [key]. *)
  val to_string : key:t -> string

  (** [of_file ~glob ~path] computes the appropriate key for file [path] to be
      embedded into [glob]. If that is not possible then [Invalid_argument] is
      raised. *)
  val of_file : glob:file_path -> file:file_path -> t

  (** [to_file ~glob ~key] gives the canonical path associated to [key] in the
      given Rocq "glob" file [glob]. *)
  val to_file : glob:file_path -> key:t -> file_path
end

(** [append ~glob ~file] is the same as [append_gen ~glob ~key ~file], but the
    [key] is computed using [Key.of_file] (whose exceptions are not caught. *)
val append : glob:file_path -> file:file_path -> unit

(** [append_gen ~glob ~key ~file] adds a mapping from [key] to the contents of
    the [file] at the end of [glob]. If a previous mapping of [key] appears in
    [glob], then it is not removed. The [key] is expected to be non-empty, and
    to only contain strings matching ["[a-zA-Z][a-zA-Z0-9_]*"] as a regexp. An
    [Invalid_argument] exception is raised if [key] is ill-formed. If there is
    an error during compression, [Zip.Error] can be raised. *)
val append_gen : glob:file_path -> key:Key.t -> file:file_path -> unit

(** [append_data ~glob ~key ~data] is similar to [append_gen ~glob ~key _] but
    takes the data directly form [data] instead of from a file. *)
val append_data : glob:file_path -> key:Key.t -> data:string -> unit

(** [clear ~glob] removes all embedded files from [glob]. *)
val clear : glob:file_path -> unit

(** Exception raised by the following functions when ill-formed file embedding
    data is encountered (e.g., when a "glob" file has been messed with). *)
exception Ill_formed

(** [glob_data ~glob] gives the contents of the Rocq "glob" file [glob], as if
    it did not have any embedded file. *)
val glob_data : glob:file_path -> string

(** [list_keys ~glob] lists all mapping keys from [glob] in order. It may have
    duplicates in cases where a key is mapped several times. *)
val list_keys : glob:file_path -> Key.t list

(** [find ~glob ~key] extracts the contents of the file associated to the last
    mapping of [key] in [glob]. The [Not_found] exception is raised if no such
    mapping exists. *)
val find : glob:file_path -> key:Key.t -> string

(** [extract_key ~glob ~key] extracts the file associated to (the last mapping
    of) [key] in [glob] to the appropriate file (determined by [Key.to_file]).
    The [Not_found] exception is raised when no such mapping exists. *)
val extract_key : glob:file_path -> key:Key.t -> unit

(** [extract ~glob ~file] is similar to [extract_key ~glob ~key], but it calls
    [Keys.of_file] (whose exceptions are not caught) to compute the [key]. *)
val extract : glob:file_path -> file:file_path -> unit

(** [extract_all ~glob] extracts all files embedded into [glob] to appropriate
    files (as dictated by [Keys.to_file]). *)
val extract_all : glob:file_path -> unit
