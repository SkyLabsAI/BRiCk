  $ . ../../setup-cpp2v.sh
  $ check_cpp2v test.cpp
  cpp2v -v -check-types -names test_17_cpp_names.v -o test_17_cpp.v test.cpp -- -std=c++17 2>&1 | sed 's/^ *[0-9]* | //'
  coqc -w -notation-overridden -w -notation-incompatible-prefix test_17_cpp_names.v
  coqc -w -notation-overridden -w -notation-incompatible-prefix test_17_cpp.v
  $ grep -o 'Efloat Ffloat (fp_of_bits Ffloat 1065353216%Z) Tfloat' test_17_cpp.v
  Efloat Ffloat (fp_of_bits Ffloat 1065353216%Z) Tfloat
  $ grep -o 'Efloat Fdouble (fp_of_bits Fdouble 4607182418800017408%Z) Tdouble' test_17_cpp.v
  Efloat Fdouble (fp_of_bits Fdouble 4607182418800017408%Z) Tdouble
