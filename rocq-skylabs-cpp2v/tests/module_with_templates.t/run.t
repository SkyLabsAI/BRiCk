  $ . ../setup-cpp2v.sh
  $ cpp2v -v -check-types -o test_combined.v test.cpp -- -std=c++17 2>&1 | sed 's/^ *[0-9]* | //'
  $ rocq c -w -notation-overridden -w -notation-incompatible-prefix test_combined.v
  $ grep -q '^Section static\.$' test_combined.v
  $ grep -q '^Section meta\.$' test_combined.v
  $ grep -q '^Definition source := Eval vm_compute in skylabs.lang.cpp.mparser.tu.with_templates static__source meta__templates\.$' test_combined.v
  $ grep -q 'cpp.prog static__source' test_combined.v
  $ grep -q 'Dtemplated_function' test_combined.v
