open Extra
open Panic

let command : bool -> unit = fun debug ->
  let path_to_initial_cwd = Project.move_to_root () in
  if debug then begin
    Printf.eprintf "Changed directory to [%s].\n%!" (Sys.getcwd ());
    Printf.eprintf "Initial directory was [%s].\n%!" path_to_initial_cwd
  end;
  let files = Project.discover () in
  let describe file config =
    Printf.eprintf "File [%s]:\n" file;
    let dirpath = Coq_path.to_string config.Project.coq_dirpath in
    Printf.eprintf " - coq_dirpath: %s\n" dirpath;
    let includes = String.concat ", " config.Project.clang_includes in
    if includes <> "" then Printf.eprintf " - clang_includes: %s\n" includes;
    let flags = String.concat " " config.Project.clang_flags in
    if flags <> "" then Printf.eprintf " - clang_flags: %s\n" flags
  in
  let rec mkdir path =
    let dir = Filename.dirname path in
    if not (Sys.file_exists dir) then mkdir dir;
    match Sys.file_exists path with
    | false -> Sys.mkdir path 0o755
    | true  ->
    if not (Sys.is_directory path) then
      panic "Error: cannot create directory [%s].\nA file already exists \
        with that name." path
  in
  let handle_file (file, config) =
    if debug then describe file config;
    let Project.{coq_dirpath; coq_package; coq_theories; _} = config in
    let Project.{clang_includes; clang_flags; _} = config in
    let (dir, base, ext) = Filename.decompose file in
    let mod_name = Printf.sprintf "%s_%s" base ext in
    let proof_dir = Filename.concat dir "proof" in
    let gen_dir = Filename.concat proof_dir mod_name in
    if debug then Printf.eprintf "Creating directory [%s].\n%!" gen_dir;
    mkdir gen_dir;
    let dune_file = Filename.concat gen_dir "dune" in
    let default_theories =
      [ "Stdlib"; "stdpp"; "iris"; "elpi"; "elpi_elpi"; "Lens"; "Ltac2";
        "bluerock.upoly"; "bluerock.prelude"; "bluerock.lang" ]
    in
    let theories = default_theories @ coq_theories in
    Out_channel.with_open_text dune_file @@ fun oc ->
    let out fmt = Printf.fprintf oc fmt in
    out "(include_subdirs qualified)\n";
    out "(coq.theory\n";
    out " (name %s.%s)\n" (Coq_path.to_string coq_dirpath) mod_name;
    out " (package %s)\n" coq_package;
    (* temporarily disable verbose incompatible prefix warnings *)
    out " (flags (:standard -w -notation-incompatible-prefix))\n";
    out " (theories";
    List.iter (out "\n  %s") theories;
    out "))\n";
    out "(rule\n";
    out " (targets code.v names.v)\n";
    out " (deps\n";
    out "  (:input ../../%s.%s)" base ext;
    let dep_include dir =
      if Filename.is_relative dir then
        out "\n  (glob_files_rec ../../%s/*.hpp)" dir
    in
    List.iter dep_include clang_includes;
    out ")\n";
    out " (action\n";
    out "  (run cpp2v -v %%{input} -o code.v -names names.v --";
    let out_include dir =
      if Filename.is_relative dir then
        out "\n   -I../../%s" dir
      else
        out "\n   -I%s" dir
    in
    List.iter out_include clang_includes;
    if clang_flags <> [] then out "\n   %s" (String.concat " " clang_flags);
    out ")))\n"
  in
  List.iter handle_file files
