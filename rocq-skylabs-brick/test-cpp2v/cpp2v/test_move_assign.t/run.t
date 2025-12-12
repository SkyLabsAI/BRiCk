  $ . ../../setup-cpp2v.sh
  $ check_cpp2v test.cpp
  cpp2v -v -check-types -names test_17_cpp_names.v -o test_17_cpp.v test.cpp -- -std=c++17 2>&1 | sed 's/^ *[0-9]* | //'
  coqc -w -notation-overridden -w -notation-incompatible-prefix test_17_cpp_names.v
  coqc -w -notation-overridden -w -notation-incompatible-prefix test_17_cpp.v
