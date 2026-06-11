  $ . ../../setup-cpp2v.sh

Unsupported floating widths are translated by cpp2v but rejected by the
BRiCk support checker.
  $ cpp2v -v -check-types -names unsupported_names.v -o unsupported.v unsupported.cpp -- -std=c++23 2>&1 | sed 's/^ *[0-9]* | //'
  $ coqc $COQC_ARGS unsupported_names.v
  $ coqc $COQC_ARGS unsupported.v
  $ coqc $COQC_ARGS support_check.v
       = ("unsupported floating width"%pstring
          :: "unsupported floating width"%pstring
             :: "unsupported floating width"%pstring
                :: "unsupported floating width"%pstring
                   :: "unsupported floating width"%pstring
                      :: "unsupported floating width"%pstring
                         :: "unsupported floating width"%pstring
                            :: "unsupported floating width"%pstring
                               :: "unsupported floating width"%pstring
                                  :: "unsupported floating width"%pstring
                                     :: "unsupported floating width"%pstring
                                        :: "unsupported floating width"%pstring
                                           :: nil)%list
       : check.M

Invalid float operators and pointer-plus-float are rejected by clang before
translation.
  $ cpp2v -v -check-types -names invalid_names.v -o invalid.v invalid.cpp -- -std=c++17 2>&1 | sed 's/^ *[0-9]* | //'
  $TESTCASE_ROOT/invalid.cpp:1:48: error: invalid operands to binary expression ('float' and 'float')
  float invalid_mod(float a, float b) { return a % b; }
                                               ~ ^ ~
  $TESTCASE_ROOT/invalid.cpp:2:50: error: invalid operands to binary expression ('float' and 'float')
  int invalid_bitwise(float a, float b) { return a & b; }
                                                 ~ ^ ~
  $TESTCASE_ROOT/invalid.cpp:3:39: error: invalid operands to binary expression ('float' and 'int')
  int invalid_shift(float a) { return a << 1; }
                                      ~ ^  ~
  $TESTCASE_ROOT/invalid.cpp:4:61: error: invalid operands to binary expression ('int *' and 'float')
  int* invalid_pointer_plus_float(int* p, float f) { return p + f; }
                                                            ~ ^ ~
  4 errors generated.
  Error while processing $TESTCASE_ROOT/invalid.cpp.
