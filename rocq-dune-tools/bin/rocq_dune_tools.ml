open Cmdliner

type sexp = Atom of string | List of sexp list

exception Error of string

type generate_options = { root : string; prefix : string; coq_flags : string }
type gather_options = { prefix : string; paths : string list }

let extra_mappings =
  [ ("fmdeps/cpp2v-core/rocq-skylabs-brick/tests/", "bedrocktest") ]

let failf fmt = Printf.ksprintf (fun message -> raise (Error message)) fmt

let read_file path =
  let ic = open_in_bin path in
  Fun.protect
    ~finally:(fun () -> close_in_noerr ic)
    (fun () ->
      let length = in_channel_length ic in
      really_input_string ic length)

let is_whitespace = function ' ' | '\t' | '\r' | '\n' -> true | _ -> false

let contains_substring string substring =
  let string_length = String.length string in
  let substring_length = String.length substring in
  let rec loop index =
    index + substring_length <= string_length
    && (String.sub string index substring_length = substring || loop (index + 1))
  in
  substring_length = 0 || loop 0

let normalize_relative_path path =
  if String.starts_with ~prefix:"./" path then
    String.sub path 2 (String.length path - 2)
  else path

let prefix_path ~prefix path = if prefix = "" then path else prefix ^ "/" ^ path

let ensure_trailing_slash path =
  if String.ends_with ~suffix:"/" path then path else path ^ "/"

let resolve_path ~root path =
  if Filename.is_relative path then Filename.concat root path else path

let rec skip_comment text index =
  if index >= String.length text then index
  else if text.[index] = '\n' then index + 1
  else skip_comment text (index + 1)

let rec skip_layout text index =
  if index >= String.length text then index
  else
    match text.[index] with
    | ';' -> skip_layout text (skip_comment text (index + 1))
    | character when is_whitespace character -> skip_layout text (index + 1)
    | _ -> index

let parse_string text index =
  let buffer = Buffer.create 32 in
  let rec loop current =
    if current >= String.length text then failf "unterminated string literal"
    else
      match text.[current] with
      | '"' -> (Buffer.contents buffer, current + 1)
      | '\\' ->
          if current + 1 >= String.length text then
            failf "unterminated string escape"
          else (
            Buffer.add_char buffer text.[current + 1];
            loop (current + 2))
      | character ->
          Buffer.add_char buffer character;
          loop (current + 1)
  in
  loop (index + 1)

let parse_atom text index =
  let rec loop current =
    if current >= String.length text then current
    else
      match text.[current] with
      | '(' | ')' | ';' -> current
      | character when is_whitespace character -> current
      | _ -> loop (current + 1)
  in
  let stop = loop index in
  if stop = index then failf "expected atom at byte %d" index;
  (String.sub text index (stop - index), stop)

let rec parse_one text index =
  let current = skip_layout text index in
  if current >= String.length text then None
  else
    match text.[current] with
    | '(' ->
        let items, next = parse_list text (current + 1) in
        Some (List items, next)
    | ')' -> failf "unexpected closing parenthesis at byte %d" current
    | '"' ->
        let value, next = parse_string text current in
        Some (Atom value, next)
    | _ ->
        let atom, next = parse_atom text current in
        Some (Atom atom, next)

and parse_list text index =
  let rec loop acc current =
    let current = skip_layout text current in
    if current >= String.length text then failf "unterminated list expression"
    else
      match text.[current] with
      | ')' -> (List.rev acc, current + 1)
      | _ -> (
          match parse_one text current with
          | None -> failwith "unreachable"
          | Some (item, next) -> loop (item :: acc) next)
  in
  loop [] index

let parse_all text =
  let rec loop acc index =
    let index = skip_layout text index in
    if index >= String.length text then List.rev acc
    else
      match parse_one text index with
      | None -> List.rev acc
      | Some (item, next) -> loop (item :: acc) next
  in
  loop [] 0

let find_named_list name items =
  let rec loop = function
    | List (Atom head :: tail) :: _ when head = name -> Some tail
    | _ :: rest -> loop rest
    | [] -> None
  in
  loop items

let first_atom = function Atom atom :: _ -> Some atom | _ -> None

let gather_mappings_for_dune_file ~prefix ~display_path ~input_path =
  if contains_substring display_path ".git" then []
  else
    let text = read_file input_path in
    let forms =
      try parse_all text
      with Error message -> failf "%s: %s" input_path message
    in
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
            let physical_path =
              display_path |> Filename.dirname |> normalize_relative_path
              |> prefix_path ~prefix
            in
            let add_sources =
              not (String.ends_with ~suffix:"/elpi" physical_path)
            in
            let source_path = ensure_trailing_slash physical_path in
            let build_path = "_build/default/" ^ source_path in
            let mappings = [ "-Q " ^ build_path ^ " " ^ logical_path ] in
            if add_sources then
              mappings @ [ "-Q " ^ source_path ^ " " ^ logical_path ]
            else mappings)

let directory_entries path =
  Array.to_list (Sys.readdir path) |> List.sort String.compare

let is_directory_no_follow path =
  try (Unix.lstat path).Unix.st_kind = Unix.S_DIR
  with Unix.Unix_error _ -> false

let is_directory path =
  try (Unix.stat path).Unix.st_kind = Unix.S_DIR
  with Unix.Unix_error _ -> false

let find_dune_files root =
  let rec scan relative_directory absolute_directory acc =
    let entries = directory_entries absolute_directory in
    List.fold_left
      (fun acc entry ->
        let absolute_entry = Filename.concat absolute_directory entry in
        if is_directory_no_follow absolute_entry then
          if entry = "_build" || entry = ".git" then acc
          else
            let relative_entry =
              if relative_directory = "" then entry
              else Filename.concat relative_directory entry
            in
            scan relative_entry absolute_entry acc
        else if entry = "dune" then
          let relative_file =
            if relative_directory = "" then "dune"
            else Filename.concat relative_directory "dune"
          in
          relative_file :: acc
        else acc)
      acc entries
  in
  List.rev (scan "" root []) |> List.sort String.compare

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
  if Sys.file_exists path then output_string stdout (read_file path)

let emit_plugin_section () =
  emit_line "";
  emit_line "# Plugin directory.";
  emit_line "-I _build/install/default/lib"

let emit_paths_section_intro () =
  emit_line "";
  emit_line "# Specified logical paths for directories (for .v and .vo files)."

let emit_mappings lines = List.iter emit_line lines

let extra_mapping_lines ~root ~prefix =
  let mapping_lines (directory, logical_path) =
    if not (is_directory (resolve_path ~root directory)) then []
    else
      let emitted_directory = prefix_path ~prefix directory in
      let build_line =
        "-Q _build/default/" ^ emitted_directory ^ " " ^ logical_path
      in
      if String.ends_with ~suffix:"/elpi/" directory then [ build_line ]
      else [ "-Q " ^ emitted_directory ^ " " ^ logical_path; build_line ]
  in
  List.concat_map mapping_lines extra_mappings

let run_generate options =
  if not (is_directory options.root) then
    failf "%s is not a directory" options.root;
  emit_header ();
  emit_optional_flags_file ~root:options.root ~coq_flags:options.coq_flags;
  emit_plugin_section ();
  emit_paths_section_intro ();
  let dune_files = find_dune_files options.root in
  let emitted =
    List.concat_map
      (fun dune_file ->
        let input_path = Filename.concat options.root dune_file in
        gather_mappings_for_dune_file ~prefix:options.prefix
          ~display_path:dune_file ~input_path)
      dune_files
  in
  emit_mappings emitted;
  emit_mappings (extra_mapping_lines ~root:options.root ~prefix:options.prefix)

let run_gather options =
  options.paths
  |> List.concat_map (fun dune_file ->
      gather_mappings_for_dune_file ~prefix:options.prefix
        ~display_path:dune_file ~input_path:dune_file)
  |> emit_mappings

let root_arg =
  let doc =
    "Scan $(docv) recursively for dune files. Subdirectories named $(b,.git) \
     and $(b,_build) are skipped. The default is the current directory."
  in
  Arg.(value & opt string "." & info [ "root" ] ~docv:"DIR" ~doc)

let prefix_arg =
  let doc =
    "Prepend $(docv) to emitted physical paths. This is useful when a dune \
     workspace is vendored under another repository and the generated mappings \
     must stay rooted at the outer workspace."
  in
  Arg.(value & opt string "" & info [ "prefix" ] ~docv:"PREFIX" ~doc)

let coq_flags_arg =
  let doc =
    "If this file exists, splice its contents into the generated _CoqProject \
     output after the built-in warning settings. Missing files are ignored."
  in
  Arg.(value & opt string "coq.flags" & info [ "coq-flags" ] ~docv:"FILE" ~doc)

let dune_files_arg =
  let doc =
    "Dune files to inspect. Each file is parsed for a $(b,rocq.theory) stanza, \
     and the corresponding $(b,-Q) mapping lines are printed."
  in
  Arg.(non_empty & pos_all file [] & info [] ~docv:"DUNE_FILE" ~doc)

let generate_term =
  let run root prefix coq_flags = run_generate { root; prefix; coq_flags } in
  Term.(const run $ root_arg $ prefix_arg $ coq_flags_arg)

let gather_term =
  let run prefix paths = run_gather { prefix; paths } in
  Term.(const run $ prefix_arg $ dune_files_arg)

let generate_doc = "generate _CoqProject content from $(b,rocq.theory) stanzas"
let gather_doc = "print only the $(b,-Q) mappings for selected dune files"

let top_man : Manpage.block list =
  [
    `S Manpage.s_description;
    `P
      "Generate _CoqProject content for Rocq projects that are organized in a \
       dune workspaces.";
    `P
      "When invoked without a subcommand, $(b,dune-rocqproject) generates a \
       _CoqProject file for the rocq.theories in the dune workspace.";
    `Pre
      {|The contents of the _CoqProject file are constructed by using:
1/ built-in warning settings;
2/ optional contents from $(b,--coq-flags);
3/ -Q paths for the project and each of its dependencies to the workspace
   build directory; and
4/ -Q paths for each project and its dependencies to the source directory.
   Paths to the _build directory will target _default.|};
    `P
      "Directories whose physical path ends in $(b,/elpi) emit only the \
       build-tree mapping. This preserves the behavior of the legacy helper \
       scripts and avoids duplicate mappings for Elpi sources.";
    `P
      "Use the $(b,gather-coq-paths) subcommand when only the mapping lines \
       are needed.";
    `S Manpage.s_examples;
    `P "$(b,dune-rocqproject) > _CoqProject";
    `P
      "$(b,dune-rocqproject --root fmdeps/auto --prefix fmdeps/auto) > \
       _CoqProject.auto";
    `P
      "$(b,dune-rocqproject gather-coq-paths path/to/theories/dune \
       path/to/tests/dune)";
  ]

let generate_man =
  [
    `S Manpage.s_description;
    `P
      "Scan the workspace rooted at $(b,--root) and print the full _CoqProject \
       content. This includes a short prelude, optional contents from \
       $(b,--coq-flags), the plugin search path, discovered $(b,-Q) mappings \
       from dune files, and a small set of hard-coded compatibility mappings \
       carried over from the legacy shell script.";
  ]

let gather_man =
  [
    `S Manpage.s_description;
    `P
      "Parse the given dune files and print only the corresponding $(b,-Q) \
       mapping lines. This is the OCaml replacement for the old \
       $(b,gather-coq-paths.py) helper.";
    `P
      "If a dune file has no $(b,rocq.theory) stanza or no theory name, it \
       contributes no output.";
  ]

let default_info = Cmd.info "dune-rocqproject" ~doc:generate_doc ~man:top_man

let generate_info =
  Cmd.info "generate-coq-project" ~doc:generate_doc ~man:generate_man

let gather_info = Cmd.info "gather-coq-paths" ~doc:gather_doc ~man:gather_man

let command =
  Cmd.group ~default:generate_term default_info
    [ Cmd.v generate_info generate_term; Cmd.v gather_info gather_term ]

let () =
  let exit_code =
    try Cmd.eval command with
    | Error message ->
        prerr_endline ("error: " ^ message);
        1
    | Sys_error message ->
        prerr_endline ("error: " ^ message);
        1
    | Unix.Unix_error (error, function_name, argument) ->
        let suffix = if argument = "" then "" else " (" ^ argument ^ ")" in
        prerr_endline
          ("error: " ^ function_name ^ suffix ^ ": " ^ Unix.error_message error);
        1
  in
  exit exit_code
