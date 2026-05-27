  $ . ../../setup-cpp2v.sh
  $ check_cpp2v_templates test.cpp
  cpp2v -v -check-types -o test_17_cpp.v --templates test_17_cpp_templates.v test.cpp -- -std=c++17 2>&1 | sed 's/^ *[0-9]* | //'
  coqc -w -notation-overridden -w -notation-incompatible-prefix test_17_cpp_templates.v
  coqc -w -notation-overridden -w -notation-incompatible-prefix test_17_cpp.v
  $ coqc -w -notation-overridden test.v
