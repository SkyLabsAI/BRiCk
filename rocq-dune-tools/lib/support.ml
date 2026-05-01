module OS = Bos.OS
module Sexp = Sexplib.Sexp

exception Error of string

module StringMap = Map.Make (String)
module StringSet = Set.Make (String)

let prune_dirs = StringSet.of_list [".git"; "_build"; "_opam"]

let transitive_marker = "; transitive dependencies"

let exit_success = 0

let exit_error = 2

let failf fmt = Printf.ksprintf (fun message -> raise (Error message)) fmt

let result_or_fail ~context = function
  | Ok value ->
      value
  | Error (`Msg message) ->
      failf "%s: %s" context message

let fpath_or_fail ~context path = result_or_fail ~context (Fpath.of_string path)

let read_text_file path =
  result_or_fail
    ~context:(Printf.sprintf "failed to read %s" (Fpath.to_string path))
    (OS.File.read path)

let write_text_file path text =
  result_or_fail
    ~context:(Printf.sprintf "failed to write %s" (Fpath.to_string path))
    (OS.File.write path text)

let current_env () =
  result_or_fail ~context:"failed to read the process environment"
    (OS.Env.current ())

let env_var name =
  let env = current_env () in
  match Astring.String.Map.find name env with
  | Some value ->
      Some value
  | None ->
      None

let parse_sexp ~context text =
  try Sexp.of_string text
  with exn -> failf "%s: %s" context (Printexc.to_string exn)

let display_path ~cwd path =
  match Fpath.relativize ~root:cwd path with
  | Some relative ->
      Fpath.to_string relative
  | None ->
      Fpath.to_string path

let is_within ~root path = Option.is_some (Fpath.relativize ~root path)

let dedupe_preserving_order values =
  let rec loop seen acc = function
    | [] ->
        List.rev acc
    | value :: rest when StringSet.mem value seen ->
        loop seen acc rest
    | value :: rest ->
        loop (StringSet.add value seen) (value :: acc) rest
  in
  loop StringSet.empty [] values

let dedupe_sorted values = List.sort_uniq String.compare values
