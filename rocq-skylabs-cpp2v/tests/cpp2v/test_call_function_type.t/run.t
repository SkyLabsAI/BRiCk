  $ . ../../setup-cpp2v.sh
  $ check_cpp2v test.cpp
  cpp2v -v -check-types -o test_17_cpp.v test.cpp -- -std=c++17 2>&1 | sed 's/^ *[0-9]* | //'
  rocq c -w -notation-overridden -w -notation-incompatible-prefix test_17_cpp.v

Substituted top-level qualifiers are stripped from function parameter types,
while the template argument itself remains qualified.

  $ grep -Fq '"templated" ((Tnum int_rank.Iint Signed) :: nil)' test_17_cpp.v
  $ if grep -Fq '"templated" ((Tqualified QC ' test_17_cpp.v; then false; fi
