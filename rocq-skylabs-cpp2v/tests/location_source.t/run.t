  $ . ../setup-project.sh
  $ . ../setup-cpp2v.sh
  $ CRAM_CXXFLAGS="-I. -isystem system"

The default companion uses physical main-file membership. It omits header-only
roots (even when a header's `#line` names the main file), keeps main-file
presumed coordinates, and strips header spelling plus complete macro stacks
from main-file macro expansions.

  $ check_cpp2v_locations fixture.cpp
  cpp2v -v -check-types -o fixture_17_cpp.v --locations fixture_17_cpp_locations.v fixture.cpp -- -std=c++17 -I. -isystem system 2>&1 | sed 's/^ *[0-9]* | //'
  rocq c -w -notation-overridden -w -notation-incompatible-prefix fixture_17_cpp.v
  rocq c -w -notation-overridden -w -notation-incompatible-prefix fixture_17_cpp_locations.v
  $ rocq c $ROCQC_ARGS check.v

The explicit opt-out retains the complete legacy all-file data: nested macro
frames, spelling and expansion ranges, first-seen files, include ancestry, and
user/system classification.

  $ cpp2v -o all_files_ast.v --locations all_files_locations.v --locations-all-files fixture.cpp -- -std=c++17 -I. -isystem system
  $ rocq c $ROCQC_ARGS all_files_ast.v
  $ rocq c $ROCQC_ARGS all_files_locations.v
  $ rocq c $ROCQC_ARGS check_all_files.v
