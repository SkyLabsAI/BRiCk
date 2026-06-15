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
  $ grep -o 'Efloat Ffloat16 (fp_of_bits Ffloat16 15360%Z) Tfloat16' test_17_cpp.v
  Efloat Ffloat16 (fp_of_bits Ffloat16 15360%Z) Tfloat16
  $ grep -o 'Efloat Ffloat16 (fp_of_bits Ffloat16 0%Z) Tfloat16' test_17_cpp.v | head -1
  Efloat Ffloat16 (fp_of_bits Ffloat16 0%Z) Tfloat16
  $ grep -o 'Eunop Uminus (Efloat Ffloat16 (fp_of_bits Ffloat16 0%Z) Tfloat16) Tfloat16' test_17_cpp.v
  Eunop Uminus (Efloat Ffloat16 (fp_of_bits Ffloat16 0%Z) Tfloat16) Tfloat16
  $ grep -o 'Efloat Ffloat128 (fp_of_bits Ffloat128 85065399433376081038215121361612832768%Z) Tfloat128' test_17_cpp.v
  Efloat Ffloat128 (fp_of_bits Ffloat128 85065399433376081038215121361612832768%Z) Tfloat128
  $ grep -o 'Efloat Ffloat128 (fp_of_bits Ffloat128 0%Z) Tfloat128' test_17_cpp.v
  Efloat Ffloat128 (fp_of_bits Ffloat128 0%Z) Tfloat128
  $ grep -A4 'Dvar "double_from_half"' test_17_cpp.v | grep -o 'Ecast (Cfloat Tdouble)'
  Ecast (Cfloat Tdouble)
  $ grep -A4 'Dvar "half_from_double"' test_17_cpp.v | grep -o 'Ecast (Cfloat Tfloat16)'
  Ecast (Cfloat Tfloat16)
  $ grep -A4 'Dvar "quad_from_half"' test_17_cpp.v | grep -o 'Ecast (Cfloat Tfloat128)'
  Ecast (Cfloat Tfloat128)
  $ grep -A4 'Dvar "half_from_quad"' test_17_cpp.v | grep -o 'Ecast (Cfloat Tfloat16)'
  Ecast (Cfloat Tfloat16)
  $ grep -A4 'Dvar "quad_from_float"' test_17_cpp.v | grep -o 'Ecast (Cfloat Tfloat128)'
  Ecast (Cfloat Tfloat128)
  $ grep -A4 'Dvar "float_from_quad"' test_17_cpp.v | grep -o 'Ecast (Cfloat Tfloat)'
  Ecast (Cfloat Tfloat)
  $ grep -A4 'Dvar "half_from_int"' test_17_cpp.v | grep -o 'Ecast (Cint2float Tfloat16)'
  Ecast (Cint2float Tfloat16)
  $ grep -A4 'Dvar "quad_from_int"' test_17_cpp.v | grep -o 'Ecast (Cint2float Tfloat128)'
  Ecast (Cint2float Tfloat128)
  $ grep -A4 'Dvar "int_from_half"' test_17_cpp.v | grep -o 'Ecast (Cfloat2int Tint)'
  Ecast (Cfloat2int Tint)
  $ grep -A4 'Dvar "int_from_quad"' test_17_cpp.v | grep -o 'Ecast (Cfloat2int Tint)'
  Ecast (Cfloat2int Tint)
  $ grep -A4 'Dvar "bool_from_half"' test_17_cpp.v | grep -o 'Ecast (Cfloat2int Tbool)'
  Ecast (Cfloat2int Tbool)
  $ grep -A4 'Dvar "bool_from_quad"' test_17_cpp.v | grep -o 'Ecast (Cfloat2int Tbool)'
  Ecast (Cfloat2int Tbool)
