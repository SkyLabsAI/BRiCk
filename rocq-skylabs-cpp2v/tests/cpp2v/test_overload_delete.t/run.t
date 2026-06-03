  $ . ../../setup-cpp2v.sh
  $ check_cpp2v_versions test.cpp 20
  cpp2v -v -check-types -o test_20_cpp.v test.cpp -- -std=c++20 2>&1 | sed 's/^ *[0-9]* | //'
  rocq c -w -notation-overridden -w -notation-incompatible-prefix test_20_cpp.v
