Clang 22 can report a variable template specialization as its own
instantiation pattern. Reachability analysis must terminate on that cycle.

  $ cpp2v_command --no-elaborate --check-types -o test_cpp.v test.cpp -- -std=c++20
  $ rocq c -w -notation-overridden -w -notation-incompatible-prefix test_cpp.v
