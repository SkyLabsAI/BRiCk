Distinct unnamed types whose invented names would coincide get distinct names.

  $ cpp2v -v -check-types -o test_cpp.v test.cpp -- -std=c++20 2>&1 | sed 's/^ *[0-9]* | //'
  $ rocq c -w -notation-overridden -w -notation-incompatible-prefix test_cpp.v
  $ rocq c -w -notation-overridden -w -notation-incompatible-prefix test.v
