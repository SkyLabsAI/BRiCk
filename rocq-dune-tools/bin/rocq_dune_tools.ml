open Cmdliner
module OS = Bos.OS
module Sexp = Sexplib.Sexp

exception Error of string

type generate_options = {
  root : Fpath.t;
  prefix : Fpath.t option;
  coq_flags : Fpath.t;
}

type workspace_layout = {
  cwd : Fpath.t;
  build_dir : Fpath.t;
  cwd_within_workspace : Fpath.t;
}

let extra_mappings =
  [ (Fpath.v "fmdeps/cpp2v-core/rocq-skylabs-brick/tests/", "bedrocktest") ]

let current_dir = Fpath.v "./"
let failf fmt = Printf.ksprintf (fun message -> raise (Error message)) fmt

let result_or_fail ~context = function
  | Ok value -> value
  | Error (`Msg message) -> failf "%s: %s" context message

let fpath_or_fail ~context path = result_or_fail ~context (Fpath.of_string path)

let file_exists path =
  result_or_fail
    ~context:(Printf.sprintf "failed to stat %s" (Fpath.to_string path))
    (OS.Path.exists path)

let dir_exists path =
  result_or_fail
    ~context:(Printf.sprintf "failed to stat %s" (Fpath.to_string path))
    (OS.Dir.exists path)

let read_text_file path =
  result_or_fail
    ~context:(Printf.sprintf "failed to read %s" (Fpath.to_string path))
    (OS.File.read path)

let load_sexps path =
  try Sexp.load_sexps (Fpath.to_string path)
  with exn -> failf "%s: %s" (Fpath.to_string path) (Printexc.to_string exn)

let strip_current_dir_prefix path =
  if Fpath.equal path current_dir then current_dir
  else
    match Fpath.rem_prefix current_dir path with
    | Some path -> path
    | None -> path

let prefix_path ~prefix path =
  match prefix with
  | None -> path
  | Some prefix ->
      let prefix = Fpath.to_dir_path prefix in
      if Fpath.equal path current_dir then prefix else Fpath.append prefix path

let resolve_path ~root path =
  if Fpath.is_rel path then Fpath.append root path else path

let relativize_or_keep ~root path =
  match Fpath.relativize ~root path with
  | Some relative -> relative
  | None -> path

let dune_describe_env () =
  let env =
    result_or_fail ~context:"failed to read the process environment"
      (OS.Env.current ())
  in
  List.fold_left
    (fun env var -> Astring.String.Map.remove var env)
    env
    [ "DUNE_ROOT"; "DUNE_SOURCEROOT"; "INSIDE_DUNE" ]

let current_workspace_layout probe_path =
  let cwd =
    result_or_fail ~context:"failed to determine the current directory"
      (OS.Dir.current ())
    |> Fpath.to_dir_path |> Fpath.normalize
  in
  let cmd =
    Bos.Cmd.(
      v "dune" % "describe" % "workspace" % "--format=sexp" % "--lang=0.1"
      % "--no-print-directory" % "--ignore-lock-dir" % p probe_path)
  in
  let output =
    result_or_fail ~context:"failed to run dune describe workspace"
      (OS.Cmd.run_out ~env:(dune_describe_env ()) cmd |> OS.Cmd.to_string)
  in
  let fields =
    match Sexp.of_string output with
    | Sexp.List fields -> fields
    | _ -> failf "unexpected dune describe workspace output"
  in
  let get_field name =
    let rec loop = function
      | Sexp.List (Sexp.Atom head :: Sexp.Atom value :: _) :: _ when head = name
        ->
          Some value
      | _ :: rest -> loop rest
      | [] -> None
    in
    loop fields
  in
  let workspace_root =
    match get_field "root" with
    | Some root ->
        fpath_or_fail ~context:"invalid dune workspace root" root
        |> Fpath.to_dir_path |> Fpath.normalize
    | None -> failf "dune describe workspace output did not include a root"
  in
  let build_context =
    match get_field "build_context" with
    | Some build_context ->
        fpath_or_fail ~context:"invalid dune build context" build_context
        |> Fpath.to_dir_path
    | None ->
        failf "dune describe workspace output did not include a build_context"
  in
  let build_dir =
    (if Fpath.is_rel build_context then
       Fpath.append workspace_root build_context
     else build_context)
    |> Fpath.to_dir_path |> Fpath.normalize
  in
  let cwd_within_workspace =
    match Fpath.relativize ~root:workspace_root cwd with
    | Some path -> Fpath.to_dir_path path
    | None ->
        failf "current directory %s is not inside dune workspace root %s"
          (Fpath.to_string cwd)
          (Fpath.to_string workspace_root)
  in
  { cwd; build_dir; cwd_within_workspace }

let path_within_workspace layout path =
  let path = Fpath.to_dir_path path in
  if Fpath.equal layout.cwd_within_workspace current_dir then path
  else if Fpath.equal path current_dir then layout.cwd_within_workspace
  else Fpath.append layout.cwd_within_workspace path |> Fpath.to_dir_path

let build_tree_path layout path =
  let absolute_build_path =
    let build_relative_path = path_within_workspace layout path in
    if Fpath.equal build_relative_path current_dir then layout.build_dir
    else Fpath.append layout.build_dir build_relative_path
  in
  relativize_or_keep ~root:layout.cwd absolute_build_path |> Fpath.to_dir_path

let path_has_component component path =
  List.exists (String.equal component) (Fpath.segs path)

let find_named_list name items =
  let rec loop = function
    | Sexp.List (Sexp.Atom head :: tail) :: _ when head = name -> Some tail
    | _ :: rest -> loop rest
    | [] -> None
  in
  loop items

let first_atom = function Sexp.Atom atom :: _ -> Some atom | _ -> None

let gather_mappings_for_dune_file ~layout ~prefix dune_file =
  if path_has_component ".git" dune_file then []
  else
    let forms = load_sexps dune_file in
    match find_named_list "rocq.theory" forms with
    | None -> []
    | Some theory_fields -> (
        let logical_path =
          match find_named_list "name" theory_fields with
          | Some atoms -> first_atom atoms
          | None -> None
        in
        match logical_path with
        | None -> []
        | Some logical_path ->
            let source_path =
              dune_file |> Fpath.parent |> strip_current_dir_prefix
              |> prefix_path ~prefix |> Fpath.to_dir_path
            in
            let build_line =
              "-Q "
              ^ Fpath.to_string (build_tree_path layout source_path)
              ^ " " ^ logical_path
            in
            if Fpath.basename source_path = "elpi" then [ build_line ]
            else
              [
                build_line;
                "-Q " ^ Fpath.to_string source_path ^ " " ^ logical_path;
              ])

let find_dune_files root =
  let stop_on_error _path = function
    | Ok _ -> Ok ()
    | Error _ as error -> error
  in
  let traverse path =
    Ok (match Fpath.basename path with "_build" | ".git" -> false | _ -> true)
  in
  let collect path acc =
    if Fpath.basename path = "dune" then path :: acc else acc
  in
  result_or_fail
    ~context:(Printf.sprintf "failed to scan %s" (Fpath.to_string root))
    (OS.Path.fold ~err:stop_on_error ~dotfiles:true ~elements:`Files
       ~traverse:(`Sat traverse) collect []
       [ Fpath.to_dir_path root ])
  |> List.sort Fpath.compare

let emit_line line =
  output_string stdout line;
  output_char stdout '\n'

let emit_header () =
  emit_line "# AUTO-GENERATED CONTENT, EDIT `dune-rocqproject` INSTEAD";
  emit_line "";
  emit_line "# Avoid warnings about entries in this _CoqProject";
  emit_line "-arg -w -arg -cannot-open-path"

let emit_optional_flags_file ~root ~coq_flags =
  let path = resolve_path ~root coq_flags in
  if file_exists path then output_string stdout (read_text_file path)

let emit_plugin_section () =
  emit_line "";
  emit_line "# Plugin directory.";
  emit_line "-I _build/install/default/lib"

let emit_paths_section_intro () =
  emit_line "";
  emit_line "# Specified logical paths for directories (for .v and .vo files)."

let emit_mappings lines = List.iter emit_line lines

let extra_mapping_lines ~layout ~root ~prefix =
  let mapping_lines (directory, logical_path) =
    let absolute_directory = resolve_path ~root directory in
    if not (dir_exists absolute_directory) then []
    else
      let emitted_directory =
        prefix_path ~prefix directory |> Fpath.to_dir_path
      in
      let build_line =
        "-Q "
        ^ Fpath.to_string (build_tree_path layout emitted_directory)
        ^ " " ^ logical_path
      in
      if Fpath.basename directory = "elpi" then [ build_line ]
      else
        [
          "-Q " ^ Fpath.to_string emitted_directory ^ " " ^ logical_path;
          build_line;
        ]
  in
  List.concat_map mapping_lines extra_mappings

let run_generate options =
  let root = Fpath.to_dir_path options.root in
  if not (dir_exists root) then
    failf "%s is not a directory" (Fpath.to_string root);
  let layout = current_workspace_layout root in
  emit_header ();
  emit_optional_flags_file ~root ~coq_flags:options.coq_flags;
  emit_plugin_section ();
  emit_paths_section_intro ();
  let emitted =
    find_dune_files root
    |> List.concat_map
         (gather_mappings_for_dune_file ~layout ~prefix:options.prefix)
  in
  emit_mappings emitted;
  emit_mappings (extra_mapping_lines ~layout ~root ~prefix:options.prefix)

let report_error_and_exit = function
  | Error message ->
      prerr_endline ("error: " ^ message);
      exit 1
  | Sys_error message ->
      prerr_endline ("error: " ^ message);
      exit 1
  | Unix.Unix_error (error, function_name, argument) ->
      let suffix = if argument = "" then "" else " (" ^ argument ^ ")" in
      prerr_endline
        ("error: " ^ function_name ^ suffix ^ ": " ^ Unix.error_message error);
      exit 1
  | exn -> raise exn

let with_error_handling f = try f () with exn -> report_error_and_exit exn

let fpath_conv =
  let parse path = Fpath.of_string path in
  Arg.conv (parse, Fpath.pp)

let root_arg =
  let doc =
    "Scan $(docv) recursively for dune files. Subdirectories named $(b,.git) \
     and $(b,_build) are skipped. The default is the current directory."
  in
  Arg.(value & opt fpath_conv Fpath.(v ".") & info [ "root" ] ~docv:"DIR" ~doc)

let prefix_arg =
  let doc =
    "Prepend $(docv) to emitted physical paths. This is useful when a dune \
     workspace is vendored under another repository and the generated mappings \
     must stay rooted at the outer workspace."
  in
  Arg.(
    value & opt (some fpath_conv) None & info [ "prefix" ] ~docv:"PREFIX" ~doc)

let coq_flags_arg =
  let doc =
    "If this file exists, splice its contents into the generated _CoqProject \
     output after the built-in warning settings. Missing files are ignored."
  in
  Arg.(
    value
    & opt fpath_conv Fpath.(v "coq.flags")
    & info [ "coq-flags" ] ~docv:"FILE" ~doc)

let generate_term =
  let run root prefix coq_flags =
    with_error_handling (fun () -> run_generate { root; prefix; coq_flags })
  in
  Term.(const run $ root_arg $ prefix_arg $ coq_flags_arg)

let generate_doc = "generate _CoqProject content from $(b,rocq.theory) stanzas"

let top_man : Manpage.block list =
  [
    `S Manpage.s_description;
    `P
      "Generate _CoqProject content for Rocq projects that are organized in a \
       dune workspaces.";
    `P
      "$(b,dune-rocqproject) scans the selected workspace root, discovers \
       $(b,rocq.theory) stanzas, and prints the corresponding _CoqProject \
       contents.";
    `Pre
      {|The contents of the _CoqProject file are constructed by using:
1/ built-in warning settings;
2/ optional contents from $(b,--coq-flags);
3/ -Q paths for the project and each of its dependencies to the workspace
   build directory; and
4/ -Q paths for each project and its dependencies to the source directory.
   Build-directory paths come from $(b,dune describe workspace).|};
    `P
      "Directories whose physical path ends in $(b,/elpi) emit only the \
       build-tree mapping.";
    `S Manpage.s_examples;
    `P "$(b,dune-rocqproject) > _CoqProject";
    `P
      "$(b,dune-rocqproject --root fmdeps/auto --prefix fmdeps/auto) > \
       _CoqProject.auto";
  ]

let default_info = Cmd.info "dune-rocqproject" ~doc:generate_doc ~man:top_man
let command = Cmd.v default_info generate_term
let () = exit (Cmd.eval command)
