open Cmdliner
open Extra
open Panic

let version = "dev"

let coq_dirpath =
  let doc =
    "Defines $(docv) as the base Coq directory path under which generated \
     Coq theories will be placed. The argument is expected to be a valid Coq \
     module path, that is, a dot-separated list of valid module identifiers. \
     In the case where no directory path is given, then the program defaults \
     to \"br.project.DIRNAME\", where DIRNAME is the current directory name. \
     If DIRNAME is not a valid identifier, then the command fails."
  in
  let i = Arg.(info ["coq-dirpath"] ~docv:"DIRPATH" ~doc) in
  Arg.(value & opt (some string) None & i)

let coq_package =
  let doc =
    "Defines $(docv) as the name of the opam package to which generated Coq \
     theories will be attached. If this option is not given, then a package \
     named DIRNAME is created, where DIRNAME is the current directory name. \
     If DIRNAME is not a suitable package name, then the command fails."
  in
  let i = Arg.(info ["coq-package"] ~docv:"PACKAGE" ~doc) in
  Arg.(value & opt (some string) None & i)

let clang_includes =
  let doc =
    "Adds $(docv) to the list of directories to be search for \".hpp\" files \
     when processing a C++ source file."
  in
  let i = Arg.(info ["I"] ~docv:"DIR" ~doc) in
  Arg.(value & opt_all dir [] & i)

let clang_flags =
  let doc =
    "Adds $(docv) to the Clang flags used when processing a C++ source file."
  in
  Arg.(value & opt_all (list string) [] & (info ["flags"] ~docv:"FLAGS" ~doc))

let init_config =
  let build coq_dirpath coq_package clang_includes clang_flags =
    let dirname =
      Lazy.from_fun @@ fun () ->
      let dirname = Filename.basename (Sys.getcwd ()) in
      match Coq_path.fixup_string_member dirname with
      | Some(_) -> dirname
      | None    ->
      panic "Error: cannot derive a valid package name / Coq path member\n\
        from the directory name [%s]." dirname
    in
    let brp_coq_dirpath =
      match coq_dirpath with
      | None          ->
          let dirpath =
            match Coq_path.fixup_string_member (Lazy.force dirname) with
            | Some(member) -> "br.project." ^ member
            | None         -> assert false (* Impossible. *)
          in
          Coq_path.path_of_string dirpath
      | Some(dirpath) ->
          try Coq_path.path_of_string dirpath with Invalid_argument(msg) ->
          panic "Error: the given DIRPATH \"%s\" is invalid.\n%s" dirpath msg
    in
    let brp_coq_package =
      match coq_package with Some(package) -> package | None ->
      Lazy.force dirname
    in
    let brp_coq_theories = [] in
    let brp_clang_includes = clang_includes in
    let brp_clang_flags = List.concat clang_flags in
    let brp_proj_ignored = [] in
    Project.{brp_coq_dirpath; brp_coq_package; brp_coq_theories;
     brp_clang_includes; brp_clang_flags; brp_proj_ignored}
  in
  Term.(const build $ coq_dirpath $ coq_package $
    clang_includes $ clang_flags)

let init_cmd =
  let doc = "Initialize a default br-project.toml file." in
  Cmd.(v (info "init" ~version ~doc) Term.(const Init.command $ init_config))

let debug =
  let doc = "Enable debug printing." in
  Arg.(value & flag & info ["debug"] ~doc)

let gen_cmd =
  let doc = "Generate Coq code from C++ source files." in
  Cmd.(v (info "gen" ~version ~doc) Term.(const Gen.command $ debug))

let _ =
  let cmds = [init_cmd; gen_cmd] in
  let default = Term.(ret (const (`Help(`Pager, None)))) in
  let default_info =
    let doc = "BlueRock C++ program verification setup tool." in
    Cmd.info "br" ~version ~doc
  in
  exit (Cmd.eval (Cmd.group default_info ~default cmds))
