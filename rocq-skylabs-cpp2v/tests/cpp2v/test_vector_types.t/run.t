  $ check_cpp2v test.cpp
  cpp2v -v -check-types -o test_17_cpp.v test.cpp -- -std=c++17 2>&1 | sed 's/^ *[0-9]* | //'
  rocq c -w -notation-overridden -w -notation-incompatible-prefix test_17_cpp.v
  $ grep -E 'Dtypedef.*"v(4di|16qi)' test_17_cpp.v
      (Dtypedef (Nglobal (Nid "v4di")) (Tvector Tlonglong 4 32))
      (Dtypedef (Nglobal (Nid "v4di_u")) (Tvector Tlonglong 4 1))
      (Dtypedef (Nglobal (Nid "v16qi_u")) (Tvector Tchar 16 1))
