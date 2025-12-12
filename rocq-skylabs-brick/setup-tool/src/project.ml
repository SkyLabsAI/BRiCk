open Extra
open Panic

type br_project = {
  brp_coq_dirpath    : Coq_path.t;
  brp_coq_package    : string;
  brp_coq_theories   : string list;
  brp_clang_includes : Filepath.t list;
  brp_clang_flags    : string list;
  brp_proj_ignored   : Filepath.t list;
}

type config_mode =
  | Extend
  | Override

type br_config = {
  brc_coq_dirpath    : Coq_path.t option;
  brc_coq_package    : string option;
  brc_coq_theories   : (config_mode * string list);
  brc_clang_includes : (config_mode * Filepath.t list);
  brc_clang_flags    : (config_mode * string list);
  brc_proj_ignored   : Filepath.t list;
}

let write_file : Filepath.t -> (Format.formatter -> unit) -> unit =
    fun file f ->
  try
    Out_channel.with_open_text file @@ fun oc ->
    f (Format.formatter_of_out_channel oc)
  with Sys_error(msg) ->
    panic "System error while writing to file %s. Error: %s." file msg

let write_br_project : Filepath.t -> br_project -> unit = fun file config ->
  let pp = Toml.Printer.value in
  let pp_string ff s = pp ff (Toml.Types.TString(s)) in
  let pp_string_array ff l = pp ff Toml.Types.(TArray(NodeString(l))) in
  let {brp_coq_dirpath; brp_coq_package; brp_coq_theories; _} = config in
  let {brp_clang_includes; brp_clang_flags; _} = config in
  let {brp_proj_ignored; _} = config in
  write_file file @@ fun ff ->
  let line fmt = Format.fprintf ff (fmt ^^ "\n") in
  line "# Project configuration file (at the root of the workspace).";
  line "";
  line "[coq]";
  line "dirpath = %a" pp_string (Coq_path.to_string brp_coq_dirpath);
  line "package = %a" pp_string brp_coq_package;
  line "theories = %a" pp_string_array brp_coq_theories;
  line "";
  line "[clang]";
  line "includes = %a" pp_string_array brp_clang_includes;
  line "flags = %a" pp_string_array brp_clang_flags;
  line "";
  line "[project]";
  line "ignored = %a" pp_string_array brp_proj_ignored

let write_br_config : Filepath.t -> br_config -> unit = fun file config ->
  let pp = Toml.Printer.value in
  let pp_string ff s = pp ff (Toml.Types.TString(s)) in
  let pp_string_array ff l = pp ff Toml.Types.(TArray(NodeString(l))) in
  let {brc_coq_dirpath; brc_coq_package; brc_coq_theories; _} = config in
  let {brc_clang_includes; brc_clang_flags; _} = config in
  let {brc_proj_ignored; _} = config in
  write_file file @@ fun ff ->
  let line fmt = Format.fprintf ff (fmt ^^ "\n") in
  line "# Local configuration file.";
  line "";
  line "[coq]";
  Option.iter (fun s ->
    line "dirpath = %a" pp_string (Coq_path.to_string s)
  ) brc_coq_dirpath;
  Option.iter (line "package = %a" pp_string) brc_coq_package;
  let (mode, brc_coq_theories) = brc_coq_theories in
  let extra = match mode with Extend -> "extra_" | Override -> "" in
  line "%stheories = %a" extra pp_string_array brc_coq_theories;
  line "";
  line "[clang]";
  let (mode, brc_clang_includes) = brc_clang_includes in
  let extra = match mode with Extend -> "extra_" | Override -> "" in
  line "%sincludes = %a" extra pp_string_array brc_clang_includes;
  let (mode, brc_clang_flags) = brc_clang_flags in
  let extra = match mode with Extend -> "extra_" | Override -> "" in
  line "%sflags = %a" extra pp_string_array brc_clang_flags;
  line "";
  line "[project]";
  line "ignored = %a" pp_string_array brc_proj_ignored

type item =
  | Coq_dirpath of Coq_path.t
  | Coq_package of string
  | Coq_theories of string list
  | Coq_extra_theories of string list
  | Clang_includes of Filepath.t list
  | Clang_extra_includes of Filepath.t list
  | Clang_flags of string list
  | Clang_extra_flags of string list
  | Project_ignored of Filepath.t list
  | Bad_entry of string

let iter_toml_table_items : Toml.Types.table ->
    (string -> Toml.Types.value -> unit) -> unit = fun table f ->
  let rec iter rev_path table =
    let handle_entry key value =
      let key = Toml.Types.Table.Key.to_string key in
      match value with
      | Toml.Types.TTable(table) -> iter (key :: rev_path) table
      | _                        ->
          let path = String.concat "." (List.rev (key :: rev_path)) in
          f path value
    in
    Toml.Types.Table.iter handle_entry table
  in
  iter [] table

exception Ill_typed of string
exception Ill_formed of string

let as_string : Toml.Types.value -> string = fun value ->
  match value with
  | Toml.Types.TString(s) -> s
  | _                     -> raise (Ill_typed("string"))

let as_coqpath : Toml.Types.value -> Coq_path.t = fun value ->
  try Coq_path.path_of_string (as_string value) with
  | Invalid_argument(_) -> raise (Ill_formed("invalid Coq directory path"))

let as_string_list : Toml.Types.value -> string list = fun value ->
  match value with
  | TArray(NodeString(l)) -> l
  | TArray(NodeEmpty    ) -> []
  | _                     -> raise (Ill_typed("string list"))

let items_of_toml : Toml.Types.table -> (string * item) list = fun table ->
  let build_item path value =
    match path with
    | "coq.dirpath"          -> Coq_dirpath(as_coqpath value)
    | "coq.package"          -> Coq_package(as_string value)
    | "coq.theories"         -> Coq_theories(as_string_list value)
    | "coq.extra_theories"   -> Coq_extra_theories(as_string_list value)
    | "clang.includes"       -> Clang_includes(as_string_list value)
    | "clang.extra_includes" -> Clang_extra_includes(as_string_list value)
    | "clang.flags"          -> Clang_flags(as_string_list value)
    | "clang.extra_flags"    -> Clang_extra_flags(as_string_list value)
    | "project.ignored"      -> Project_ignored(as_string_list value)
    | _                      -> Bad_entry("unknown key")
  in
  let items = ref [] in
  let add_item path value =
    let item =
      try build_item path value with
      | Ill_typed(desc) -> Bad_entry("ill-typed, expected " ^ desc)
      | Ill_formed(msg) -> Bad_entry(msg)
    in
    items := (path, item) :: !items
  in
  iter_toml_table_items table add_item;
  List.rev !items

type error = string * string

let report_error : error -> unit = fun (path, msg) ->
  err "Error on field [%s]: %s." path msg

let read_br_project : Filepath.t -> br_project = fun file ->
  let panic fmt =
   panic ("Failure while reading configuration file [%s].\n" ^^ fmt) file
  in
  let items =
    match Toml.Parser.from_filename file with
    | `Ok(table)               -> items_of_toml table
    | `Error(msg, _)           -> panic "%s." msg
    | exception Sys_error(msg) -> panic "System error (%s)." msg
  in
  let errors = ref [] in
  let coq_dirpath = ref None in
  let coq_package = ref None in
  let coq_theories = ref None in
  let clang_includes = ref None in
  let clang_flags = ref None in
  let project_ignored = ref None in
  let handle_item (path, item) =
    let error msg = errors := (path, msg) :: !errors in
    match item with
    | Coq_dirpath(dirpath)    -> coq_dirpath := Some(dirpath)
    | Coq_package(package)    -> coq_package := Some(package)
    | Coq_theories(theories)  -> coq_theories := Some(theories)
    | Coq_extra_theories(_)   -> error "unsupported in this file"
    | Clang_includes(dirs)    -> clang_includes := Some(dirs)
    | Clang_extra_includes(_) -> error "unsupported in this file"
    | Clang_flags(flags)      -> clang_flags := Some(flags)
    | Clang_extra_flags(_)    -> error "unsupported in this file"
    | Project_ignored(files)  -> project_ignored := Some(files)
    | Bad_entry(msg)          -> error msg
  in
  List.iter handle_item items;
  let errors = List.rev !errors in
  List.iter report_error errors;
  if errors <> [] then panic "There were %i errors." (List.length errors);
  let (brp_coq_dirpath, brp_coq_package) =
    match (!coq_dirpath, !coq_package) with
    | (None         , None         ) ->
        panic "Error: [coq.dirpath] and [coq.package] entries are mandatory."
    | (None         , _            ) ->
        panic "Error: [coq.dirpath] entry is mandatory."
    | (_            , None         ) ->
        panic "Error: [coq.package] entry is mandatory."
    | (Some(dirpath), Some(package)) -> (dirpath, package)
  in
  let brp_coq_theories = Option.value !coq_theories ~default:[] in
  let brp_clang_includes = Option.value !clang_includes ~default:[] in
  let brp_clang_flags = Option.value !clang_flags ~default:[] in
  let brp_proj_ignored = Option.value !project_ignored ~default:[] in
  {brp_coq_dirpath; brp_coq_package; brp_coq_theories;
   brp_clang_includes; brp_clang_flags; brp_proj_ignored}

let read_br_config : Filepath.t -> br_config = fun file ->
  let panic fmt =
   panic ("Failure while reading project file [%s].\n" ^^ fmt) file
  in
  let items =
    match Toml.Parser.from_filename file with
    | `Ok(table)               -> items_of_toml table
    | `Error(msg, _)           -> panic "%s." msg
    | exception Sys_error(msg) -> panic "System error (%s)." msg
  in
  let errors = ref [] in
  let coq_dirpath = ref None in
  let coq_package = ref None in
  let coq_theories = ref None in
  let clang_includes = ref None in
  let clang_flags = ref None in
  let project_ignored = ref None in
  let handle_item (path, item) =
    let error msg = errors := (path, msg) :: !errors in
    let check_extra r name =
      match !r with None -> () | Some(_) -> error @@
      Printf.sprintf
        "only one of [clang.%s] and [clang.extra_%s] can be set"
        name name
    in
    match item with
    | Coq_dirpath(dirpath)       ->
        coq_dirpath := Some(dirpath)
    | Coq_package(package)       ->
        coq_package := Some(package)
    | Coq_theories(ths)          ->
        check_extra coq_theories "theories";
        coq_theories := Some(Override, ths)
    | Coq_extra_theories(ths)    ->
        check_extra coq_theories "theories";
        coq_theories := Some(Extend, ths)
    | Clang_includes(dirs)       ->
        check_extra clang_includes "includes";
        clang_includes := Some(Override, dirs)
    | Clang_extra_includes(dirs) ->
        check_extra clang_includes "includes";
        clang_includes := Some(Extend, dirs)
    | Clang_flags(flags)         ->
        check_extra clang_flags "flags";
        clang_flags := Some(Override, flags)
    | Clang_extra_flags(flags)   ->
        check_extra clang_flags "flags";
        clang_flags := Some(Extend, flags)
    | Project_ignored(files)     ->
        project_ignored := Some(files)
    | Bad_entry(msg)             ->
        error msg
  in
  List.iter handle_item items;
  let errors = List.rev !errors in
  List.iter report_error errors;
  if errors <> [] then panic "There were %i errors." (List.length errors);
  let brc_coq_dirpath = !coq_dirpath in
  let brc_coq_package = !coq_package in
  let brc_coq_theories =
    Option.value !coq_theories ~default:(Extend, [])
  in
  let brc_clang_includes =
    Option.value !clang_includes ~default:(Extend, [])
  in
  let brc_clang_flags = Option.value !clang_flags ~default:(Extend, []) in
  let brc_proj_ignored = Option.value !project_ignored ~default:[] in
  {brc_coq_dirpath; brc_coq_package; brc_coq_theories;
   brc_clang_includes; brc_clang_flags; brc_proj_ignored}

let project_file_name : string = "br-project.toml"

let config_file_name : string = "br-config.toml"

let locate_root : unit -> (Filepath.t * Filepath.t) option = fun _ ->
  let rec locate_root cur_candidate path_to_cwd =
    let candidate = Filename.concat cur_candidate project_file_name in
    match Sys.file_exists candidate with
    | true  -> Some(cur_candidate, path_to_cwd)
    | false ->
    let new_candidate = Filename.dirname cur_candidate in
    if new_candidate = cur_candidate then None else
    let dir = Filename.basename cur_candidate in
    let path_to_cwd = Filename.concat dir path_to_cwd in
    locate_root new_candidate path_to_cwd
  in
  locate_root (Sys.getcwd ()) Filename.current_dir_name

let move_to_root : unit -> Filepath.t = fun _ ->
  let rec locate_root cur_candidate path_to_cwd =
    let candidate = Filename.concat cur_candidate project_file_name in
    match Sys.file_exists candidate with
    | true  -> Sys.chdir cur_candidate; path_to_cwd
    | false ->
    let new_candidate = Filename.dirname cur_candidate in
    if new_candidate = cur_candidate then
      panic "Error: no project file [%s] could be located.\nYou must run the \
        command from within a project." project_file_name;
    let dir = Filename.basename cur_candidate in
    let path_to_cwd = Filename.concat dir path_to_cwd in
    locate_root new_candidate path_to_cwd
  in
  locate_root (Sys.getcwd ()) Filename.current_dir_name

type config = {
  coq_dirpath    : Coq_path.t;
  coq_package    : string;
  coq_theories   : string list;
  clang_includes : Filepath.t list;
  clang_flags    : string list;
  proj_ignored   : Filepath.t list; (* Relative to project root. *)
}

let make_config : br_project -> config = fun br_project ->
  let coq_dirpath = br_project.brp_coq_dirpath in
  let coq_package = br_project.brp_coq_package in
  let coq_theories = br_project.brp_coq_theories in
  let clang_includes = br_project.brp_clang_includes in
  let clang_flags = br_project.brp_clang_flags in
  let proj_ignored = br_project.brp_proj_ignored in
  {coq_dirpath; coq_package; coq_theories;
   clang_includes; clang_flags; proj_ignored}

let merge_br_config : dir:string -> config -> br_config -> config =
    fun ~dir config br_config ->
  let coq_dirpath =
    match br_config.brc_coq_dirpath with
    | None          -> config.coq_dirpath
    | Some(dirpath) -> dirpath
  in
  let coq_package =
    match br_config.brc_coq_package with
    | None          -> config.coq_package
    | Some(package) -> package
  in
  let coq_theories =
    let (mode, ths) = br_config.brc_coq_theories in
    match mode with
    | Extend   -> config.coq_theories @ ths
    | Override -> ths
  in
  let clang_includes =
    let (mode, includes) = br_config.brc_clang_includes in
    match mode with
    | Extend   -> config.clang_includes @ includes
    | Override -> includes
  in
  let clang_flags =
    let (mode, flags) = br_config.brc_clang_flags in
    match mode with
    | Extend   -> config.clang_flags @ flags
    | Override -> flags
  in
  let proj_ignored =
    let extra_ignored =
      List.map (Filename.concat dir) br_config.brc_proj_ignored
    in
    config.proj_ignored @ extra_ignored
  in
  {coq_dirpath; coq_package; coq_theories;
   clang_includes; clang_flags; proj_ignored}

let chdir_config : name:string -> config -> config = fun ~name config ->
  let coq_dirpath =
    let name =
       match Coq_path.fixup_string_member name with
       | Some(name) -> name
       | None       ->
       panic "Error: Directory name [%s] is not a valid Coq path member." name
    in
    let member = Coq_path.member_of_string name in
    Coq_path.append config.coq_dirpath [member]
  in
  let coq_package = config.coq_package in
  let coq_theories = config.coq_theories in
  let clang_includes =
    let parent file =
      match Filename.is_relative file with false -> file | _ ->
      Filename.concat Filename.parent_dir_name file
    in
    List.map parent config.clang_includes
  in
  let clang_flags = config.clang_flags in
  let proj_ignored = config.proj_ignored in
  {coq_dirpath; coq_package; coq_theories;
   clang_includes; clang_flags; proj_ignored}

let discover : unit -> (Filepath.t * config) list = fun _ ->
  let config = make_config (read_br_project project_file_name) in
  let skip_dir ~path config =
    List.exists (Filepath.equal path) config.proj_ignored
  in
  let skip_file ~path config =
    not (List.mem (Filename.extension path) [".hpp"; ".cpp"; ".h"; ".c"]) ||
    List.exists (Filepath.equal path) config.proj_ignored
  in
  let chdir ~dir ~base config =
    let config = chdir_config ~name:base config in
    let full_dir = Filename.concat dir base in
    let config_file = Filename.concat full_dir config_file_name in
    if not (Sys.file_exists config_file) then config else
    let br_config = read_br_config config_file in
    merge_br_config ~dir:full_dir config br_config
  in
  let found = ref [] in
  let add ~path config = found := (path, config) :: !found in
  Filename.iter_files_with_state ~skip_dir ~skip_file ~chdir config "." add;
  List.rev !found
