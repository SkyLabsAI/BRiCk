  $ cpp2v -v -check-types -o test_combined.v test.cpp --loc-info=none -- -std=c++17 2>&1 | sed 's/^ *[0-9]* | //'
  $ rocq c -w -notation-overridden -w -notation-incompatible-prefix test_combined.v
  $ rocq c -w -notation-overridden -w -notation-incompatible-prefix test.v
