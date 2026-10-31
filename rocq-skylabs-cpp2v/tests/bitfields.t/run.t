Compiling the C++ code, use "make Q=" for debugging.
  $ make 2> /dev/null
  $ ls *.v | wc -l | sed -e 's/ //g'
  2

Compiling the generated Coq files.
  $ rocq c ${CHECK_CPP2V_ROCQC_ARGS} -Q . test test_cpp.v
  $ rocq c ${CHECK_CPP2V_ROCQC_ARGS} -Q . test test.v
       = ("MemberExpr"%pstring :: nil)%list
       : check.M
