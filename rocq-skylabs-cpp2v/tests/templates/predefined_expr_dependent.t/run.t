  $ . ../../setup-cpp2v.sh
  $ check_cpp2v_templates_versions test.cpp 23
  cpp2v -v -check-types -o test_23_cpp.v --templates test_23_cpp_templates.v test.cpp -- -std=c++23 2>&1 | sed 's/^ *[0-9]* | //'
  coqc -w -notation-overridden -w -notation-incompatible-prefix test_23_cpp_templates.v
  coqc -w -notation-overridden -w -notation-incompatible-prefix test_23_cpp.v
  $ coqc -w -notation-overridden test.v
