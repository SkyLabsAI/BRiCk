Resolved concept values survive parsing, both in ordinary expressions and
instantiated constexpr branches.
  $ cpp2v -v -check-types -o test_cpp.v test.cpp -- -std=c++20
  $ rocq c $CHECK_CPP2V_ROCQC_ARGS -Q . test test_cpp.v
  $ rocq c $CHECK_CPP2V_ROCQC_ARGS -Q . test test.v

Printing uninstantiated templates must not ask Clang for their truth values.
  $ cpp2v -v -check-types -o instances.v --templates templates.v test.cpp -- -std=c++20
  $ grep -q 'potentially dependent concept specialization' templates.v
  $ rocq c $CHECK_CPP2V_ROCQC_ARGS -Q . test instances.v
  $ rocq c $CHECK_CPP2V_ROCQC_ARGS -Q . test templates.v
