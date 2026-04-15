(*
 * Copyright (C) 2025-2026 SkyLabs AI, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

(** [mkdir ?mode dir] creates directory [dir], as well as any required parent.
    The given [mode] ([0o755] by default) is used for created directories, and
    the mode of existing directories is not modified. If [dir] already exists,
    but is not a directory, then [Sys_error] is raised. *)
val mkdir : ?mode:int -> Filepath.t -> unit

(** [remove_file file] removes the given [file] if it exists. Note that [file]
    is expected to be a regular file, and the function raises [Sys_error] when
    that is not the case. *)
val remove_file : Filepath.t -> unit

(** [rmdir_if_empty ?recursive dir] removes directory [dir] if it is empty. If
    [recursive] is [true], then the process continues with parent directories.
    Note that [dir] is expected to be a directory, and the function will raise
    [Sys_error] if that is not the case. *)
val rmdir_if_empty : ?recursive:bool -> Filepath.t -> unit

(** [write_file file f] writes to the given [file] using function [f]. In case
    of file system error, the [Sys_error] exception is raised. *)
val write_file : Filepath.t -> (Format.formatter -> unit) -> unit

(** [read_lines file] reads all the lines from the given [file].  In case of a
    file system error, the [Sys_error] exception is raised. *)
val read_lines : Filepath.t -> string list

(** [outut_lines oc ls] prints the lines [ls] to the output channel [oc]. Note
    that a newline character is added at the end of each line. *)
val output_lines : out_channel -> string list -> unit

(** [write_lines file ls] writes the lines of [ls] to file [file], terminating
    each line with a newline character. *)
val write_lines : string -> string list -> unit

(** [append_lines file ls] writes the lines [ls] at the end of file [fname]. A
    newline terminates each inserted lines. The file must exist. *)
val append_file : string -> string list -> unit

(** [iter_files_with_state ?skip_dir ?skip_file ?chdir state file fn] iterates
    over files, while maintaining state dependent on the directory where files
    are contained. The optional [skip_dir] and [skip_file] predicates are used
    to respectively stop the iteration at a specific directory (including each
    of its sub-directories) or file. The [chdir] function is used to alter the
    state when moving under a directory. Iteration starts on the given [file],
    with the given initial [state]. Function [fn] is called on every file that
    is not ignored via the predicates. Exception [Failure] is raised if [file]
    does not exist, or if a file somehow disapears during iteration. *)
val iter_files_with_state :
  ?skip_dir:(path:string -> 'state -> bool) ->
  ?skip_file:(path:string -> 'state -> bool) ->
  ?chdir:(dir:string -> base:string -> 'state -> 'state) ->
  'state -> string -> (path:string -> 'state -> unit) -> unit
