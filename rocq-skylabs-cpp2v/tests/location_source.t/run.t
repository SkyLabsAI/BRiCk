  $ . ../setup-project.sh
  $ . ../setup-cpp2v.sh
  $ CRAM_CXXFLAGS="-I. -isystem system"

The production companion retains nested macro frames, spelling and expansion
ranges, physical and presumed coordinates, first-seen files, include ancestry,
and user/system classification.

  $ check_cpp2v_locations fixture.cpp
  cpp2v -v -check-types -o fixture_17_cpp.v --locations fixture_17_cpp_locations.v fixture.cpp -- -std=c++17 -I. -isystem system 2>&1 | sed 's/^ *[0-9]* | //'
  rocq c -w -notation-overridden -w -notation-incompatible-prefix fixture_17_cpp.v
  rocq c -w -notation-overridden -w -notation-incompatible-prefix fixture_17_cpp_locations.v
  $ rocq c $ROCQC_ARGS check.v
