  $ . ../setup-project.sh
  $ . ../setup-cpp2v.sh

The final-core tree, not Clang's AST, determines paths. This fixture covers a
flattened multi-declaration list, absent if options, a path-stable point-empty
synthesized else branch, an erased parenthesis wrapper, and ordered call
arguments.

  $ check_cpp2v_locations fixture.cpp
  cpp2v -v -check-types -o fixture_17_cpp.v --locations fixture_17_cpp_locations.v fixture.cpp -- -std=c++17 2>&1 | sed 's/^ *[0-9]* | //'
  rocq c -w -notation-overridden -w -notation-incompatible-prefix fixture_17_cpp.v
  rocq c -w -notation-overridden -w -notation-incompatible-prefix fixture_17_cpp_locations.v
  $ rocq c $ROCQC_ARGS check.v
