  $ . ../../../setup-cpp2v.sh
  $ check_cpp2v test.cpp
  cpp2v -v -check-types -names test_17_cpp_names.v -o test_17_cpp.v test.cpp -- -std=c++17 2>&1 | sed 's/^ *[0-9]* | //'
  $TESTCASE_ROOT/test.cpp:9:9: error: initializing multiple members of union
      int y {1};
          ^
  $TESTCASE_ROOT/test.cpp:8:9: note: previous initialization is here
      int x {3};
          ^
  1 error generated.
  Error while processing $TESTCASE_ROOT/test.cpp.
  coqc -w -notation-overridden -w -notation-incompatible-prefix test_17_cpp_names.v
  Error: Can't find file ./test_17_cpp_names.v
  coqc -w -notation-overridden -w -notation-incompatible-prefix test_17_cpp.v
  Error: Can't find file ./test_17_cpp.v
  [1]
