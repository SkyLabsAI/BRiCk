(*
 * Copyright (C) 2025-2026 SkyLabs AI, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

open Prelude

let sys_error fmt =
  Prelude.failwith ~fail:(fun s -> raise (Sys_error(s))) fmt

let rec mkdir ?(mode=0o755) path =
  let dir = Filename.dirname path in
  if not (Sys.file_exists dir) then mkdir dir;
  match Sys.file_exists path with
  | false -> Sys.mkdir path mode
  | true  ->
  match Sys.is_directory path with
  | true  -> ()
  | false ->
  sys_error "cannot create directory %S (a file exists with that name)" path

let remove_file : Filepath.t -> unit = fun file ->
  let try_remove file = try Sys.remove file with Sys_error(_) -> () in
  match Sys.is_directory file with
  | true                   -> sys_error "file %S is not a directory" file
  | false                  -> try_remove file
  | exception Sys_error(_) -> ()

let rmdir_if_empty : Filepath.t -> unit = fun dir ->
  let try_remove dir = try Sys.rmdir dir with Sys_error(_) -> () in
  match Sys.is_directory dir with
  | true                   -> try_remove dir
  | false                  -> sys_error "file %S is not a directory" dir
  | exception Sys_error(_) -> ()

let rec recursively_rmdir_if_empty : Filepath.t -> unit = fun dir ->
  rmdir_if_empty dir;
  let dir = Filename.dirname dir in
  if dir <> Filename.current_dir_name then recursively_rmdir_if_empty dir

let rmdir_if_empty : ?recursive:bool -> Filepath.t -> unit =
    fun ?(recursive=false) dir ->
  (if recursive then recursively_rmdir_if_empty else rmdir_if_empty) dir

let write_file : Filepath.t -> (Format.formatter -> unit) -> unit =
    fun file f ->
  try
    Out_channel.with_open_text file @@ fun oc ->
    let ff = Format.formatter_of_out_channel oc in
    f ff; Format.fprintf ff "%!"; Printf.fprintf oc "%!"
  with Sys_error(s) -> sys_error "unable to write file %S (%s)" file s

let read_lines : Filepath.t -> string list = fun file ->
  try
    In_channel.with_open_text file @@ fun ic ->
    let rec loop lines =
      match In_channel.input_line ic with
      | None       -> List.rev lines
      | Some(line) -> loop (line :: lines)
    in
    loop []
  with Sys_error(s) -> sys_error "unable to read file %S (%s)" file s

let output_lines : out_channel -> string list -> unit = fun oc ls ->
  List.iter (Printf.fprintf oc "%s\n") ls

let write_lines : string -> string list -> unit = fun fname ls ->
  let oc = open_out fname in
  output_lines oc ls; close_out oc

let append_file : string -> string list -> unit = fun fname ls ->
  let oc = open_out_gen [Open_append] 0 fname in
  output_lines oc ls; close_out oc

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
    let path = Filename.concat dir base in
    if not (Sys.file_exists path) then
      failwith "no such file or directory %S" path;
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
  iter [(state, Filename.dirname file, Filename.basename file)]
