open Support

type options =
  { no_normalize: bool
  ; check: bool
  ; ascii: bool }

type parsed_file =
  { path: Fpath.t
  ; file: Dune_file.t
  ; theories: Dune_file.theory list }

type file_change =
  { path: Fpath.t
  ; updated_text: string }

type pending_change =
  { change_path: Fpath.t
  ; original_text: string
  ; replacement_text: string }

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

let pending_changes changes =
  List.filter_map
    (fun (change : file_change) ->
      let original_text = read_text_file change.path in
      if String.equal original_text change.updated_text then None
      else
        Some
          { change_path= change.path
          ; original_text
          ; replacement_text= change.updated_text } )
    changes

let with_temp_file prefix suffix f =
  let path = Filename.temp_file prefix suffix in
  Fun.protect
    ~finally:(fun () -> try Sys.remove path with Sys_error _ -> ())
    (fun () -> f path)

let write_temp_text path text =
  let channel = open_out_bin path in
  Fun.protect
    ~finally:(fun () -> close_out channel)
    (fun () -> output_string channel text)

let rec read_all_lines channel buffer =
  match input_line channel with
  | line ->
      Buffer.add_string buffer line ;
      Buffer.add_char buffer '\n' ;
      read_all_lines channel buffer
  | exception End_of_file ->
      Buffer.contents buffer

let emit_diff ~ascii ~display original_text replacement_text =
  with_temp_file "dune-rocqdeps-original" ".tmp" (fun original_path ->
      with_temp_file "dune-rocqdeps-replacement" ".tmp"
        (fun replacement_path ->
          write_temp_text original_path original_text ;
          write_temp_text replacement_path replacement_text ;
          let argv =
            [| "patdiff"
             ; "-default"
             ; (if ascii then "-ascii" else "-ansi")
             ; "-location-style"
             ; "diff"
             ; "-alt-old"
             ; Filename.concat "old" display
             ; "-alt-new"
             ; Filename.concat "new" display
             ; original_path
             ; replacement_path |]
          in
          let channel = Unix.open_process_args_in "patdiff" argv in
          let output = read_all_lines channel (Buffer.create 256) in
          match Unix.close_process_in channel with
          | Unix.WEXITED 0 ->
              ()
          | Unix.WEXITED 1 ->
              output_string stdout output
          | Unix.WEXITED code ->
              failf "patdiff failed for %s with exit code %d" display code
          | Unix.WSIGNALED signal | Unix.WSTOPPED signal ->
              failf "patdiff failed for %s with signal %d" display signal ) )

let emit_diffs ~cwd ~ascii changes =
  List.iter
    (fun change ->
      emit_diff
        ~ascii
        ~display:(display_path ~cwd change.change_path)
        change.original_text change.replacement_text )
    changes

let analyze_targets ~cwd parsed_files ~no_normalize =
  let transitive_dep_graph =
    Rewrite.build_transitive_dep_graph
      (List.map
         (fun (parsed_file : parsed_file) ->
           (parsed_file.path, parsed_file.theories) )
         parsed_files )
  in
  let changes, errors =
    List.fold_left
      (fun (changes, errors) (parsed_file : parsed_file) ->
        if
          parsed_file.theories = []
          || not (is_within ~root:cwd parsed_file.path)
        then (changes, errors)
        else
          try
            let updated_theories =
              Rewrite.update_theories transitive_dep_graph ~no_normalize
                parsed_file.theories
            in
            let updated_text =
              Dune_file.write parsed_file.file updated_theories
            in
            ({path= parsed_file.path; updated_text} :: changes, errors)
          with
          | Error message ->
              ( changes
              , display_file_error ~cwd parsed_file.path message :: errors )
          | Dune_file.Theory_mismatch theory_names ->
              let theory_names =
                if theory_names = [] then "<none>"
                else String.concat ", " theory_names
              in
              ( changes
              , display_file_error ~cwd parsed_file.path
                  (Printf.sprintf
                     "internal theory mismatch while rewriting [%s]"
                     theory_names )
                :: errors ) )
      ([], []) parsed_files
  in
  (List.rev changes, List.rev errors)

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
  let pending_changes = pending_changes changes in
  if options.check && pending_changes <> [] then (
    emit_diffs ~cwd ~ascii:options.ascii pending_changes ;
    exit exit_check_failed ) ;
  List.iter
    (fun change ->
      write_text_file change.change_path change.replacement_text )
    pending_changes
