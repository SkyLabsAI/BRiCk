let basename path = Fpath.basename (Fpath.v path)

let is_rocq_file file = Fpath.has_ext ".v" (Fpath.v file)

let parse_line_directive s =
  Scanf.sscanf_opt (String.trim s) "#line %d %S %!" (fun line file ->
      (line, file))

let line_directive ~file line = Printf.sprintf "#line %d %S" line (basename file)

let unwrap = function Ok value -> value | Error (`Msg message) -> failwith message

let read_lines file =
  Bos.OS.File.read_lines (Fpath.v file) |> unwrap |> Array.of_list

let output_lines oc lines =
  Array.iter
    (fun line ->
      output_string oc line;
      output_char oc '\n')
    lines

let target_permissions file =
  Bos.OS.Path.stat (Fpath.v file)
  |> Result.map (fun stat -> stat.Unix.st_perm)
  |> Result.to_option

let write_lines_atomic file lines =
  let file = Fpath.v file in
  let write oc lines =
    output_lines oc lines;
    Ok ()
  in
  Bos.OS.File.with_oc ?mode:(target_permissions (Fpath.to_string file)) file
    write lines
  |> Result.join
  |> unwrap

let rewrite_lines ~file lines =
  let marker = "Elpi Accumulate lp:{{" in
  let marker_re = Str.regexp_string marker in
  let rewritten = ref [] in
  let output_line = ref 0 in
  let emit line =
    incr output_line;
    rewritten := line :: !rewritten
  in
  let rec copy_blank_lines idx =
    if idx < Array.length lines && String.trim lines.(idx) = "" then (
      emit lines.(idx);
      copy_blank_lines (idx + 1))
    else idx
  in
  let rec loop idx =
    if idx >= Array.length lines then ()
    else
      let line = lines.(idx) in
      match Str.search_forward marker_re line 0 with
      | exception Not_found ->
          emit line;
          loop (idx + 1)
      | marker_idx ->
          let after_open_start = marker_idx + String.length marker in
          let before_payload = String.sub line 0 after_open_start in
          let after_open =
            String.sub line after_open_start
              (String.length line - after_open_start)
          in
          let payload = String.trim after_open in
          if payload <> "" then (
            let directive = line_directive ~file (!output_line + 2) in
            emit (before_payload ^ directive);
            if parse_line_directive payload = None then emit after_open;
            loop (idx + 1))
          else (
            emit line;
            let next_idx = copy_blank_lines (idx + 1) in
            if next_idx >= Array.length lines then loop next_idx
            else
              let directive = line_directive ~file (!output_line + 2) in
              if parse_line_directive lines.(next_idx) = None then (
                emit directive;
                loop next_idx)
              else (
                emit directive;
                loop (next_idx + 1)))
  in
  loop 0;
  Array.of_list (List.rev !rewritten)

let rewrite_file file = rewrite_lines ~file (read_lines file)

let run in_place files =
  let files = List.filter is_rocq_file files in
  match (in_place, files) with
  | false, [ file ] ->
      output_lines stdout (rewrite_file file);
      0
  | false, [] -> 0
  | false, _ ->
      Printf.eprintf "rocq-elpi-lint: without -i, pass exactly one file\n";
      2
  | true, files ->
      List.iter
        (fun file ->
          let rewritten = rewrite_file file in
          write_lines_atomic file rewritten)
        files;
      0

let in_place =
  let doc = "Rewrite files in place." in
  Cmdliner.Arg.(value & flag & info [ "i"; "in-place" ] ~doc)

let files =
  let doc = "Rocq source files to lint." in
  Cmdliner.Arg.(
    non_empty & pos_all file [] & info [] ~doc ~docv:"FILE.v")

let cmd =
  let doc = "fix #line directives in Rocq-Elpi accumulate blocks" in
  let info = Cmdliner.Cmd.info "rocq-elpi-lint" ~doc in
  Cmdliner.Cmd.v info Cmdliner.Term.(const run $ in_place $ files)

let () = exit (Cmdliner.Cmd.eval' cmd)
