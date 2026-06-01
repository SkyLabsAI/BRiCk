open Cmdliner
module Dune_file = Rocq_dune_tools_lib.Dune_file
module Support = Rocq_dune_tools_lib.Support
module Tool = Rocq_dune_tools_lib.Tool

let report_error_and_exit = function
  | Dune_file.Theory_mismatch theory_names ->
      let theory_names =
        if theory_names = [] then "<none>" else String.concat ", " theory_names
      in
      prerr_endline
        ( "error: internal theory mismatch while rewriting [" ^ theory_names
        ^ "]" ) ;
      exit Support.exit_error
  | Support.Error message ->
      prerr_endline ("error: " ^ message) ;
      exit Support.exit_error
  | Sys_error message ->
      prerr_endline ("error: " ^ message) ;
      exit Support.exit_error
  | Unix.Unix_error (error, function_name, argument) ->
      let suffix = if argument = "" then "" else " (" ^ argument ^ ")" in
      prerr_endline
        ("error: " ^ function_name ^ suffix ^ ": " ^ Unix.error_message error) ;
      exit Support.exit_error
  | exn ->
      raise exn

let with_error_handling f = try f () with exn -> report_error_and_exit exn

let run options = with_error_handling (fun () -> Tool.run options)

let no_normalize_arg =
  let doc =
    "Only append newly discovered dependencies. Existing dependency order is \
     preserved, and files are unchanged when no new dependencies are needed."
  in
  Arg.(value & flag & info ["no-normalize"] ~doc)

let check_arg =
  let doc =
    "Do not edit dune files. Exit successfully only if the selected \
     rocq.theory stanzas would be left unchanged because they already contain \
     the needed dependency closure."
  in
  Arg.(value & flag & info ["check"] ~doc)

let term =
  let run no_normalize check = run Tool.{no_normalize; check} in
  Term.(const run $ no_normalize_arg $ check_arg)

let doc = "synchronize recursive rocq dependency stanzas in dune files"

let man =
  [ `S Manpage.s_description
  ; `P
      "$(b,dune-rocqdeps) scans the current dune workspace, rewrites \
       $(b,rocq.theory) $(b,(theories ...)) fields in the current directory \
       subtree, and expands them with recursive transitive dependencies."
  ; `P
      "Rewritten stanzas list direct dependencies first and then a $(b,; \
       transitive dependencies) section. Once a file uses that style, only the \
       pre-marker entries are treated as direct roots when the closure is \
       recomputed."
  ; `S Manpage.s_examples
  ; `P "$(b,dune-rocqdeps)"
  ; `P "$(b,dune-rocqdeps --no-normalize)"
  ; `P "$(b,dune-rocqdeps --check)" ]

let info = Cmd.info "dune-rocqdeps" ~doc ~man

let command = Cmd.v info term

let () = exit (Cmd.eval command)
