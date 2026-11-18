  $ setup_project

Compiling the C++ code: cpp2v continues past the unsupported statements.
  $ make 2>&1 | sed -e 's/^.*test\.cpp/test.cpp/'
  $ ls *.v | wc -l | sed -e 's/ //g'
  2

Compiling the generated Coq files.
  $ dune build
       = ("AddrLabelExpr"%pstring
          :: "AddrLabelExpr"%pstring
             :: "unsupported statement: IndirectGotoStmt"%pstring
                :: "unsupported statement: CoroutineBodyStmt"%pstring
                   :: "template parameter pack"%pstring :: nil)%list
       : check.M
