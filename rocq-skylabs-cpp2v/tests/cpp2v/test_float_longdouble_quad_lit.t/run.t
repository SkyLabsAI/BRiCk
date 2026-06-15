  $ . ../../setup-cpp2v.sh

Force IEEE-quad long double semantics on targets where Clang supports
`-mlong-double-128`; the default x86 target remains covered by the unsupported
negative test.
  $ cpp2v -v -check-types -names longdouble_quad_names.v -o longdouble_quad.v test.cpp -- -std=c++23 -mlong-double-128 2>&1 | sed 's/^ *[0-9]* | //'
  $ coqc $COQC_ARGS longdouble_quad_names.v
  $ coqc $COQC_ARGS longdouble_quad.v
  $ grep -o 'Efloat Flongdouble (fp_of_bits Flongdouble 85065399433376081038215121361612832768%Z) Tlongdouble' longdouble_quad.v
  Efloat Flongdouble (fp_of_bits Flongdouble 85065399433376081038215121361612832768%Z) Tlongdouble
  $ grep -o 'Efloat Flongdouble (fp_of_bits Flongdouble 0%Z) Tlongdouble' longdouble_quad.v
  Efloat Flongdouble (fp_of_bits Flongdouble 0%Z) Tlongdouble
