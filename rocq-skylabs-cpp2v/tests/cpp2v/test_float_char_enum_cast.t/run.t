  $ . ../../setup-cpp2v.sh
  $ check_cpp2v_versions test.cpp 23
  cpp2v -v -check-types -names test_23_cpp_names.v -o test_23_cpp.v test.cpp -- -std=c++23 2>&1 | sed 's/^ *[0-9]* | //'
  coqc -w -notation-overridden -w -notation-incompatible-prefix test_23_cpp_names.v
  coqc -w -notation-overridden -w -notation-incompatible-prefix test_23_cpp.v
  $ grep -o 'Ecast (Cint2float Tfloat)' test_23_cpp.v | head -1
  Ecast (Cint2float Tfloat)
  $ grep -o 'Ecast (Cint2float Tdouble)' test_23_cpp.v
  Ecast (Cint2float Tdouble)
  $ grep -o 'Ecast (Cfloat2int Tchar)' test_23_cpp.v
  Ecast (Cfloat2int Tchar)
  $ grep -o 'Ecast (Cfloat2int Tchar8)' test_23_cpp.v
  Ecast (Cfloat2int Tchar8)
  $ grep -o 'Estatic_cast (Cfloat2int t1) t1' test_23_cpp.v
  Estatic_cast (Cfloat2int t1) t1
  $ grep -o 'Ecast (Cint2float Tfloat128)' test_23_cpp.v
  Ecast (Cint2float Tfloat128)
  $ grep -o 'Ecast Cl2r (Evar "e" t1)' test_23_cpp.v
  Ecast Cl2r (Evar "e" t1)
  $ grep -o 'Ecast Cl2r (Evar "e" t2)' test_23_cpp.v
  Ecast Cl2r (Evar "e" t2)
