  $ . ../setup-cpp2v.sh
  $ cpp2v -v -check-types --module-with-templates test_combined.v test.cpp -- -std=c++17 2>&1 | sed 's/^ *[0-9]* | //'
  $ rocq c -w -notation-overridden -w -notation-incompatible-prefix test_combined.v
  $ rocq c -w -notation-overridden -w -notation-incompatible-prefix test.v
