  $ . ../setup-project.sh
  $ . ../setup-cpp2v.sh

Ordinary and template symbol/type roots remain disjoint. The selected roots also
retain self-typedef/compatible-definition behavior, implicit and transformed
origins, synthesized anchors, template parameter/default/value order, and
separate specialization points of instantiation.

  $ check_cpp2v_locations fixture.cpp
  cpp2v -v -check-types -o fixture_17_cpp.v --locations fixture_17_cpp_locations.v fixture.cpp -- -std=c++17 2>&1 | sed 's/^ *[0-9]* | //'
  rocq c -w -notation-overridden -w -notation-incompatible-prefix fixture_17_cpp.v
  rocq c -w -notation-overridden -w -notation-incompatible-prefix fixture_17_cpp_locations.v
  $ rocq c $ROCQC_ARGS check.v
