  $ . ../../setup-cpp2v.sh
  $ check_cpp2v test.cpp
  cpp2v -v -check-types -names test_17_cpp_names.v -o test_17_cpp.v test.cpp -- -std=c++17 2>&1 | sed 's/^ *[0-9]* | //'
  $TESTCASE_ROOT/test.cpp:22:21: warning: magnitude of floating-point constant too large for type 'float'; maximum is 3.40282347E+38
          float overflow_f = 1e39f;
                             ^
  $TESTCASE_ROOT/test.cpp:23:22: warning: magnitude of floating-point constant too large for type 'double'; maximum is 1.7976931348623157E+308
          double overflow_d = 1e400;
                              ^
  2 warnings generated.
  coqc -w -notation-overridden -w -notation-incompatible-prefix test_17_cpp_names.v
  coqc -w -notation-overridden -w -notation-incompatible-prefix test_17_cpp.v
  $ grep -o 'Efloat Ffloat (fp_of_bits Ffloat 1065353216%Z) Tfloat' test_17_cpp.v
  Efloat Ffloat (fp_of_bits Ffloat 1065353216%Z) Tfloat
  $ grep -o 'Efloat Fdouble (fp_of_bits Fdouble 4607182418800017408%Z) Tdouble' test_17_cpp.v
  Efloat Fdouble (fp_of_bits Fdouble 4607182418800017408%Z) Tdouble
  $ grep -o 'Efloat Ffloat (fp_of_bits Ffloat 1036831949%Z) Tfloat' test_17_cpp.v
  Efloat Ffloat (fp_of_bits Ffloat 1036831949%Z) Tfloat
  $ grep -o 'Efloat Fdouble (fp_of_bits Fdouble 4591870180066957722%Z) Tdouble' test_17_cpp.v
  Efloat Fdouble (fp_of_bits Fdouble 4591870180066957722%Z) Tdouble
  $ grep -o 'Efloat Ffloat (fp_of_bits Ffloat 0%Z) Tfloat' test_17_cpp.v | head -1
  Efloat Ffloat (fp_of_bits Ffloat 0%Z) Tfloat
  $ grep -o 'Eunop Uminus (Efloat Ffloat (fp_of_bits Ffloat 0%Z) Tfloat) Tfloat' test_17_cpp.v
  Eunop Uminus (Efloat Ffloat (fp_of_bits Ffloat 0%Z) Tfloat) Tfloat
  $ grep -o 'Efloat Fdouble (fp_of_bits Fdouble 0%Z) Tdouble' test_17_cpp.v | head -1
  Efloat Fdouble (fp_of_bits Fdouble 0%Z) Tdouble
  $ grep -o 'Eunop Uminus (Efloat Fdouble (fp_of_bits Fdouble 0%Z) Tdouble) Tdouble' test_17_cpp.v
  Eunop Uminus (Efloat Fdouble (fp_of_bits Fdouble 0%Z) Tdouble) Tdouble
  $ grep -o 'Efloat Ffloat (fp_of_bits Ffloat 1%Z) Tfloat' test_17_cpp.v
  Efloat Ffloat (fp_of_bits Ffloat 1%Z) Tfloat
  $ grep -o 'Efloat Ffloat (fp_of_bits Ffloat 2139095040%Z) Tfloat' test_17_cpp.v
  Efloat Ffloat (fp_of_bits Ffloat 2139095040%Z) Tfloat
  $ grep -o 'Efloat Fdouble (fp_of_bits Fdouble 9218868437227405312%Z) Tdouble' test_17_cpp.v
  Efloat Fdouble (fp_of_bits Fdouble 9218868437227405312%Z) Tdouble
  $ grep -o 'Ecast (Cfloat Tdouble)' test_17_cpp.v
  Ecast (Cfloat Tdouble)
  $ grep -o 'Ecast (Cfloat Tfloat)' test_17_cpp.v
  Ecast (Cfloat Tfloat)
  $ grep -o 'Ecast (Cint2float Tfloat)' test_17_cpp.v
  Ecast (Cint2float Tfloat)
  $ grep -o 'Ecast (Cfloat2int Tint)' test_17_cpp.v
  Ecast (Cfloat2int Tint)
  $ grep -o 'Ecast (Cfloat2int Tbool)' test_17_cpp.v | head -1
  Ecast (Cfloat2int Tbool)
