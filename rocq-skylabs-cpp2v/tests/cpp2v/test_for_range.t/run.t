  $ . ../../setup-cpp2v.sh
  $ check_cpp2v test.cpp
  cpp2v -v -check-types -o test_17_cpp.v test.cpp -- -std=c++17 2>&1 | sed 's/^ *[0-9]* | //'
  $TESTCASE_ROOT/test.cpp:46:10: warning: range-based for loop initialization statements are a C++20 extension
      for (const auto z = r; auto i : z) {
           ^~~~~~~~~~~~~~~~~
  1 warning generated.
  rocq c -w -notation-overridden -w -notation-incompatible-prefix test_17_cpp.v
