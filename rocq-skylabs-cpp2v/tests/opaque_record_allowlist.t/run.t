  $ setup_project

Translate a trivial_abi class with a bit-field and the opaque-record controls.
  $ cpp2v -o test_cpp.v test.cpp -- -std=c++17 --target=x86_64-linux-gnu

Check the declaration kinds and reasons in the generated translation unit.
  $ dune build
