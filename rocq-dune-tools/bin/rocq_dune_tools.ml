type sexp = Atom of string | List of sexp list

exception Error of string
exception Usage of string

type generate_options = { root : string; prefix : string; coq_flags : string }
type gather_options = { prefix : string; paths : string list }
type command = Generate of generate_options | Gather of gather_options

let extra_mappings =
  [ ("fmdeps/cpp2v-core/rocq-skylabs-brick/tests/", "bedrocktest") ]

let default_generate_options =
  { root = "."; prefix = ""; coq_flags = "coq.flags" }

let default_gather_options = { prefix = ""; paths = [] }
let failf fmt = Printf.ksprintf (fun message -> raise (Error message)) fmt

let read_file path =
  let ic = open_in_bin path in
  Fun.protect
    ~finally:(fun () -> close_in_noerr ic)
    (fun () ->
      let length = in_channel_length ic in
      really_input_string ic length)

let is_whitespace = function ' ' | '\t' | '\r' | '\n' -> true | _ -> false

let has_prefix string prefix =
  let string_length = String.length string in
  let prefix_length = String.length prefix in
  string_length >= prefix_length && String.sub string 0 prefix_length = prefix

let has_suffix string suffix =
  let string_length = String.length string in
  let suffix_length = String.length suffix in
  string_length >= suffix_length
  &&
  let start = string_length - suffix_length in
  String.sub string start suffix_length = suffix

let contains_substring string substring =
  let string_length = String.length string in
  let substring_length = String.length substring in
  let rec loop index =
    index + substring_length <= string_length
    && (String.sub string index substring_length = substring || loop (index + 1))
  in
  substring_length = 0 || loop 0

let normalize_relative_path path =
  if has_prefix path "./" then String.sub path 2 (String.length path - 2)
  else path

let prefix_path ~prefix path = if prefix = "" then path else prefix ^ "/" ^ path

let ensure_trailing_slash path =
  if has_suffix path "/" then path else path ^ "/"

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
            let add_sources = not (has_suffix physical_path "/elpi") in
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
      if has_suffix directory "/elpi/" then [ build_line ]
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

let usage_message =
  String.concat "\n"
    [
      "Usage:";
      "  dune-rocqproject [generate-coq-project] [--root DIR] [--prefix \
       PREFIX] [--coq-flags FILE]";
      "  dune-rocqproject gather-coq-paths [--prefix PREFIX] DUNE_FILE...";
      "";
      "Default command:";
      "  generate-coq-project";
    ]

let rec parse_generate_args options = function
  | [] -> options
  | "--root" :: value :: rest ->
      parse_generate_args { options with root = value } rest
  | "--prefix" :: value :: rest ->
      parse_generate_args { options with prefix = value } rest
  | "--coq-flags" :: value :: rest ->
      parse_generate_args { options with coq_flags = value } rest
  | "--help" :: _ | "-h" :: _ -> raise (Usage usage_message)
  | "--" :: [] -> options
  | "--" :: _ ->
      failf "generate-coq-project does not accept positional arguments"
  | option :: _ when has_prefix option "-" ->
      failf "unknown option for generate-coq-project: %s" option
  | argument :: _ ->
      failf "generate-coq-project does not accept positional argument %S"
        argument

let rec parse_gather_args options = function
  | [] -> options
  | "--prefix" :: value :: rest ->
      parse_gather_args { options with prefix = value } rest
  | "--help" :: _ | "-h" :: _ -> raise (Usage usage_message)
  | "--" :: rest -> { options with paths = options.paths @ rest }
  | option :: _ when has_prefix option "-" ->
      failf "unknown option for gather-coq-paths: %s" option
  | path :: rest ->
      parse_gather_args { options with paths = options.paths @ [ path ] } rest

let parse_command argv =
  match Array.to_list argv with
  | _program_name :: "gather-coq-paths" :: rest ->
      Gather (parse_gather_args default_gather_options rest)
  | _program_name :: "generate-coq-project" :: rest ->
      Generate (parse_generate_args default_generate_options rest)
  | _program_name :: "--help" :: _ -> raise (Usage usage_message)
  | _program_name :: "-h" :: _ -> raise (Usage usage_message)
  | _program_name :: arguments ->
      Generate (parse_generate_args default_generate_options arguments)
  | [] -> Generate default_generate_options

let main () =
  match parse_command Sys.argv with
  | Generate options ->
      run_generate options;
      0
  | Gather options ->
      if options.paths = [] then
        failf "gather-coq-paths expects at least one dune file path";
      run_gather options;
      0

let () =
  let exit_code =
    try main () with
    | Usage message ->
        print_endline message;
        0
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
