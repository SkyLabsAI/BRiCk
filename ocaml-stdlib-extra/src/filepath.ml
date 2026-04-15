type t = string

module Filename = Stdlib.Filename
module String = Stdlib.String

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

(** Decomposed relative path to a file or directory. *)
type decomposed_rel_path = {
  path : string list;
  (** Directories on the path to the file. *)
  name : string;
  (** Base name of the file (without extension). *)
  ext  : string option;
  (** File extension if any. *)
}

let decompose : t -> decomposed_rel_path = fun path ->
  if not (Filename.is_relative path) then
    failwith "Filepath.decompose: not relative.";
  let special s = Filename.(s = current_dir_name || s = parent_dir_name) in
  let base = Filename.basename path in
  if special base then
    failwith "Filepath.decompose: contains special directories.";
  let name = Filename.remove_extension base in
  let ext =
    match Filename.extension base with ""  -> None | ext ->
    Some(String.sub ext 1 (String.length ext - 1))
  in
  let rec collect_dirs path dir =
    if dir = Filename.current_dir_name then path else
    collect_dirs (Filename.basename dir :: path) (Filename.dirname dir)
  in
  let path = collect_dirs [] (Filename.dirname path) in
  {path; name; ext}
