  $ . ../../setup-cpp2v.sh
  $ check_cpp2v_templates test.cpp
  cpp2v -v -check-types -o test_17_cpp.v --templates test_17_cpp_templates.v test.cpp -- -std=c++17 2>&1 | sed 's/^ *[0-9]* | //'
  rocq c -w -notation-overridden -w -notation-incompatible-prefix test_17_cpp_templates.v
  rocq c -w -notation-overridden -w -notation-incompatible-prefix test_17_cpp.v
  $ grep -Eq 'E(sizeof_pack None|unresolved_sizeof_pack) "T"' test_17_cpp_templates.v
  $ grep -Eq 'E(sizeof_pack None|unresolved_sizeof_pack) "args"' test_17_cpp_templates.v
  $ if grep -q 'Esizeof_pack' test_17_cpp.v; then grep -q '(Some 3%N) "T"' test_17_cpp.v && grep -q '(Some 3%N) "args"' test_17_cpp.v; else test "$(grep -o 'Eint 3 (Tnum int_rank.Ilong Unsigned)' test_17_cpp.v | wc -l)" -eq 2; fi
