open Support

type options = {no_normalize: bool}

type parsed_file =
  { path: Fpath.t
  ; file: Dune_file.t
  ; theories: Dune_file.theory list }

type file_change =
  { path: Fpath.t
  ; updated_text: string }

let current_cwd () =
  result_or_fail ~context:"failed to determine the current directory"
    (OS.Dir.current ())
  |> Fpath.to_dir_path |> Fpath.normalize

let read_dune_files dune_files =
  let rec loop parsed_files errors = function
    | [] ->
        (List.rev parsed_files, List.rev errors)
    | path :: rest -> (
      try
        let file, theories = Dune_file.read path in
        loop ({path; file; theories} :: parsed_files) errors rest
      with Error message -> loop parsed_files (message :: errors) rest )
  in
  loop [] [] dune_files

let display_file_error ~cwd path message =
  Printf.sprintf "%s %s" (display_path ~cwd path) message

let analyze_targets ~cwd parsed_files ~no_normalize =
  let transitive_dep_graph =
    Rewrite.build_transitive_dep_graph
      (List.map
         (fun (parsed_file : parsed_file) ->
           (parsed_file.path, parsed_file.theories) )
         parsed_files )
  in
  let errors = ref [] in
  let changes =
    List.filter_map
      (fun (parsed_file : parsed_file) ->
        if
          parsed_file.theories = []
          || not (is_within ~root:cwd parsed_file.path)
        then None
        else
          try
            let updated_theories =
              Rewrite.update_theories transitive_dep_graph ~no_normalize
                parsed_file.theories
            in
            let updated_text = Dune_file.write parsed_file.file updated_theories in
            Some {path= parsed_file.path; updated_text}
          with
          | Error message ->
              errors :=
                display_file_error ~cwd parsed_file.path message :: !errors ;
              None
          | Dune_file.Theory_mismatch theory_names ->
              let theory_names =
                if theory_names = [] then "<none>"
                else String.concat ", " theory_names
              in
              errors :=
                display_file_error ~cwd parsed_file.path
                  (Printf.sprintf
                     "internal theory mismatch while rewriting [%s]"
                     theory_names )
                :: !errors ;
              None )
      parsed_files
  in
  (changes, List.rev !errors)

let run options =
  let cwd = current_cwd () in
  let workspace = Workspace.current () in
  let dune_files = Workspace.dune_files workspace in
  let parsed_files, workspace_errors = read_dune_files dune_files in
  let changes, analysis_errors =
    analyze_targets ~cwd parsed_files ~no_normalize:options.no_normalize
  in
  let errors = workspace_errors @ analysis_errors in
  if errors <> [] then (
    List.iter (fun error -> prerr_endline ("error: " ^ error)) errors ;
    exit exit_error ) ;
  List.iter
    (fun (change : file_change) ->
      let current_text = read_text_file change.path in
      if not (String.equal current_text change.updated_text) then
        write_text_file change.path change.updated_text )
    changes
