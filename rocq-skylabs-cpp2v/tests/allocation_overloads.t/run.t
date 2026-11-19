Keep the replaceable unsized and sized global deallocation functions when
Clang selects one overload for a delete expression.

  $ cpp2v_command --no-elaborate --check-types -o test_cpp.v test.cpp -- -std=c++20
  $ grep -Eq '\(OODelete false\) \(t[0-9]+ :: nil\)' test_cpp.v
  $ grep -Eq '\(OODelete false\) \(t[0-9]+ :: Tulong :: nil\)' test_cpp.v
  $ rocq c -w -notation-overridden -w -notation-incompatible-prefix test_cpp.v
