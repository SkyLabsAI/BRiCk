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
    "Do not edit dune files. Print a patdiff against the canonical rewrite \
     that $(b,dune-rocqdeps) would produce. The printed diff is not \
     necessarily a minimal patch required to make the check pass: it may \
     include normalization-only changes such as ordering, grouping, comments, \
     or line layout. The exit status is based on whether the selected \
     $(b,rocq.theory) dependency closures are stale under $(b,dune-rocqdeps)' \
     dependency comparison, not on whether file text exactly matches the \
     printed rewrite."
  in
  Arg.(value & flag & info ["check"] ~doc)

let ascii_arg =
  let doc =
    "When used with $(b,--check), print diff output without ANSI escape codes."
  in
  Arg.(value & flag & info ["ascii"] ~doc)

let term =
  let run no_normalize check ascii = run Tool.{no_normalize; check; ascii} in
  Term.(const run $ no_normalize_arg $ check_arg $ ascii_arg)

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
  ; `P
      "The canonical rewrite may differ textually from other accepted layouts. \
       When using $(b,--check), treat the printed diff as the canonical output \
       rather than as a minimal required patch, and trust the exit status."
  ; `S Manpage.s_examples
  ; `P "$(b,dune-rocqdeps)"
  ; `P "$(b,dune-rocqdeps --no-normalize)"
  ; `P "$(b,dune-rocqdeps --check)" ]

let info = Cmd.info "dune-rocqdeps" ~doc ~man

let command = Cmd.v info term

let () = exit (Cmd.eval command)
