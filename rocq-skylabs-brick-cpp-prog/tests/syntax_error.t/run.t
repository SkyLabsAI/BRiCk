  $ cd "$DUNE_SOURCEROOT/fmdeps/BRiCk/rocq-skylabs-brick-cpp-prog/tests"
  $ cp syntax_error.t/test.v /tmp/cpp_prog_no_defns.v
  $ rm -f /tmp/cpp_prog_no_defns.glob /tmp/cpp_prog_no_defns.vo /tmp/cpp_prog_no_defns.vos /tmp/cpp_prog_no_defns.vok /tmp/.cpp_prog_no_defns.aux
  $ rocq c $(awk '{ if ($1 == "-arg") { sub(/^-arg /, ""); print } else print }' _RocqProject) /tmp/cpp_prog_no_defns.v
  File "/tmp/cpp_prog_no_defns.v", line 5, characters 2-7:
  Error: Syntax error: [cpp_flags] expected after [ident] (in [command]).
  
  [1]
  $ rm -f /tmp/cpp_prog_no_defns.glob /tmp/cpp_prog_no_defns.vo /tmp/cpp_prog_no_defns.vos /tmp/cpp_prog_no_defns.vok /tmp/.cpp_prog_no_defns.aux /tmp/cpp_prog_no_defns.v
