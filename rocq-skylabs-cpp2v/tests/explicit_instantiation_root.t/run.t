Explicit template instantiations are translation-unit roots even when their
directives are written in an included header.

  $ cpp2v_command --no-elaborate --check-types -o test_cpp.v test.cpp -- -std=c++20
  $ for name in ExplicitClass explicit_function explicit_variable declared_function MemberOwner member_function member_variable root; do grep -q "\"$name\"" test_cpp.v || echo "missing $name"; done
  $ grep -q '"UnusedRecord"' test_cpp.v
  [1]
  $ rocq c -w -notation-overridden -w -notation-incompatible-prefix test_cpp.v
