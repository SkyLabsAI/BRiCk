(*
 * SPDX-License-Identifier: BSD-3-Clause
 * Copyright: RefinedC developers and contributors 2020-2023
 * Copyright: 2024 BlueRock Security, Inc.
 *)

(** Standard library extension (mostly). *)

(** Short name for the type of a pretty-printing function. *)
type 'a pp = Format.formatter -> 'a -> unit

(** Short name for the type of an equality function. *)
type 'a eq = 'a -> 'a -> bool

(** Short name for the type of a comparison function. *)
type 'a cmp = 'a -> 'a -> int

module Char = struct
  include Char

  let printable_ascii : char -> bool = fun c ->
    ' ' <= c && c <= '~'
end

module Filepath = struct
  type t = string

  let normalize : string -> string = fun file ->
    let (dir, file) =
      if Sys.is_directory file then (file, None) else
      (Filename.dirname file, Some(Filename.basename file))
    in
    let dir =
      try
        let cwd = Sys.getcwd () in
        Sys.chdir dir;
        let dir = Sys.getcwd () in
        Sys.chdir cwd; dir
      with Sys_error(_) -> dir
    in
    match file with
    | None       -> dir
    | Some(file) -> Filename.concat dir file

  let equal : t -> t -> bool = fun f1 f2 -> f1 = f2 ||
    match (Sys.is_directory f1, Sys.is_directory f2) with
    | exception Sys_error(_) -> false
    | (false, true ) -> false
    | (true , false) -> false
    | (_    , _    ) -> normalize f1 = normalize f2
end

module Filename = struct
  include Filename

  let concat : string -> string -> string = fun f1 f2 ->
    if f1 = current_dir_name then f2 else
    if f2 = current_dir_name then f1 else
    concat f1 f2

  (** [iter_files_with_state ?skip_dir ?skip_file ?chdir state file fn] can be
      used to iterate over files, which maintaining state that is dependent on
      the directory where the files are contained. The optional [skip_dir] and
      [skip_file] predicates can be used to respectively stop the iteration at
      a specific directory (including its contents) or file. Using the [chdir]
      function, one can control the evolution of the state when moving under a
      directory. The iteration is performed starting on the given [file], with
      the given initial [state]. Function [fn] is called on every file that is
      not ignored via the predicates. Exception [Failure] can be raised if the
      given [file] does not exist, or if a file somehow disapears while in the
      middle of running the function. *)
  let iter_files_with_state : ?skip_dir:(path:string -> 'state -> bool) ->
      ?skip_file:(path:string -> 'state -> bool) ->
      ?chdir:(dir:string -> base:string -> 'state -> 'state) ->
      'state -> string -> (path:string -> 'state -> unit) -> unit =
      fun ?(skip_dir=fun ~path:_ _ -> false)
          ?(skip_file=fun ~path:_ _ -> false)
          ?(chdir=fun ~dir:_ ~base:_ s -> s) state file f ->
    let rec iter files =
      match files with
      | []                          -> ()
      | (state, dir, base) :: files ->
      let path = concat dir base in
      if not (Sys.file_exists path) then
        failwith ("no such file or directory [" ^ path ^ "]");
      match Sys.is_directory path with
      | false when skip_file ~path state -> iter files
      | false                            -> f ~path state; iter files
      | true  when skip_dir ~path state  -> iter files
      | true                             ->
      let state =
        match base = Filename.current_dir_name with
        | true  -> state
        | false -> chdir ~dir ~base state
      in
      let new_files = Sys.readdir path in
      Array.sort String.compare new_files;
      let fn name files = (state, path, name) :: files in
      iter (Array.fold_right fn new_files files)
    in
    iter [(state, dirname file, basename file)]

  let decompose : string -> string * string * string = fun file ->
    let ext = extension file in
    let ext_len = String.length ext in
    let ext = if ext_len = 0 then ext else String.sub ext 1 (ext_len - 1) in
    (dirname file, remove_extension (basename file), ext)
end

module Buffer = struct
  include Buffer

  let add_full_channel : t -> in_channel -> unit = fun buf ic ->
    try
      while true do
        add_char buf (input_char ic)
      done
    with End_of_file -> ()

  let add_file : t -> string -> unit = fun buf fname ->
    let ic = open_in fname in
    add_full_channel buf ic;
    close_in ic

  let from_file : string -> t = fun fname ->
    let buf = create 4096 in
    add_file buf fname; buf

  let to_file : string -> t -> unit = fun fname buf ->
    let oc = open_out fname in
    output_buffer oc buf;
    close_out oc
end

module String = struct
  include String

  let for_all : (char -> bool) -> string -> bool = fun p s ->
    try iter (fun c -> if not (p c) then raise Exit) s; true
    with Exit -> false

  let sub_from : string -> int -> string = fun s i ->
    sub s i (length s - i)

  let trim_leading : char -> string -> string = fun c s ->
    let len = length s in
    let index = ref 0 in
    while !index < len && s.[!index] = c do incr index done;
    sub_from s !index
end

(** [outut_lines oc ls] prints the lines [ls] to the output channel [oc]. Note
    that a newline character is added at the end of each line. *)
let output_lines : out_channel -> string list -> unit = fun oc ls ->
  List.iter (Printf.fprintf oc "%s\n") ls

(** [write_file fname ls] writes the lines [ls] to file [fname]. All lines are
    terminated with a newline character. *)
let write_file : string -> string list -> unit = fun fname ls ->
  let oc = open_out fname in
  output_lines oc ls; close_out oc

(** [append_file fname ls] writes the lines [ls] at the end of file [fname]. A
    newline terminates each inserted lines. The file must exist. *)
let append_file : string -> string list -> unit = fun fname ls ->
  let oc = open_out_gen [Open_append] 0 fname in
  output_lines oc ls; close_out oc

(** [read_file fname] returns the list of the lines of file [fname]. Note that
    the trailing newlines are removed. *)
let read_file : string -> string list = fun fname ->
  let ic = open_in fname in
  let lines = ref [] in
  try
    while true do lines := input_line ic :: !lines done;
    assert false (* Unreachable. *)
  with End_of_file -> close_in ic; List.rev !lines

(** Short name for a standard formatter with continuation. *)
type ('a,'b) koutfmt = ('a, Format.formatter, unit, unit, unit, 'b) format6

(** [invalid_arg fmt ...] raises [Invalid_argument] with the given message. It
    can be formed using the standard formatter syntax. *)
let invalid_arg : ('a, 'b) koutfmt -> 'a = fun fmt ->
  let cont _ = invalid_arg (Format.flush_str_formatter ()) in
  Format.kfprintf cont Format.str_formatter fmt
