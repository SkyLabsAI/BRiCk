  $ setup_project

cpp2v emits the std::align_val_t declaration required by Clang's implicit
aligned allocation functions.

  $ cpp2v --module=test_cpp.v test.cpp -- -target x86_64-linux-gnu -std=c++17 -nostdinc
  $ dune build check.vo
