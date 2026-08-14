  $ . ../setup-project.sh
  $ . ../setup-cpp2v.sh

Unsupported semantic values keep main-file diagnostic origins. Point-empty
children remain distinguishable as successful empty lookups, while a wholly
point-empty compiler-provided root is omitted by the default scope.

  $ check_cpp2v_locations fixture.cpp
  cpp2v -v -check-types -o fixture_17_cpp.v --locations fixture_17_cpp_locations.v fixture.cpp -- -std=c++17 2>&1 | sed 's/^ *[0-9]* | //'
  rocq c -w -notation-overridden -w -notation-incompatible-prefix fixture_17_cpp.v
  rocq c -w -notation-overridden -w -notation-incompatible-prefix fixture_17_cpp_locations.v
  $ grep -q 'Tunsupported "Builtin long double"' fixture_17_cpp.v
  $ grep -q 'Eunsupported "unsupported floating-point semantics' fixture_17_cpp.v
  $ rocq c $ROCQC_ARGS check.v

A conservatively sized generated multi-root translation unit is a non-golden
scaling smoke. Both complete outputs compile, and a deep lookup in the final
root reduces. Larger real workspace TUs are covered by the composed validation
gate. No timing threshold weakens the semantic assertion.

  $ { echo 'int seed = 0;'; i=0; while test "$i" -lt 16; do echo "int large_$i(int value) { return value + $i; }"; i=$((i + 1)); done; } > large.cpp
  $ test "$(wc -l < large.cpp)" -eq 17
  $ check_cpp2v_locations large.cpp
  cpp2v -v -check-types -o large_17_cpp.v --locations large_17_cpp_locations.v large.cpp -- -std=c++17 2>&1 | sed 's/^ *[0-9]* | //'
  rocq c -w -notation-overridden -w -notation-incompatible-prefix large_17_cpp.v
  rocq c -w -notation-overridden -w -notation-incompatible-prefix large_17_cpp_locations.v
  $ test -s large_17_cpp_locations.v
  $ rocq c $ROCQC_ARGS large_check.v
