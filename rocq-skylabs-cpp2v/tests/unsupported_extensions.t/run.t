Extensions that cpp2v cannot print faithfully become [Sunsupported],
[Eunsupported] or [Tunsupported]; each source is compiled with the flags that
enable its extension (see the Makefile). Diagnostics are not shown, since their
text varies with the clang version.
  $ setup_project

  $ make > make.log 2>&1

MS compatibility accepts a jump past an initialized declaration, with a warning.
  $ grep -c 'Microsoft extension' make.log
  1

Named loops: [named.sh] checks that `break outer;` and `continue outer;` print
as [Sunsupported] and that a plain `break` does not. The flag `-fnamed-loops`
exists from clang 22; before, the check is vacuous.
  $ sh named.sh
  named loops: ok

The support report does not look into pointee types, so the [__unaligned]
qualifier is checked in the generated AST.
  $ grep -q 'Tunsupported "[^"]*__unaligned' ms_cpp.v && echo '__unaligned: Tunsupported'
  __unaligned: Tunsupported

Assumptions, in each spelling, and the other statement attributes that are
promises to the compiler print unsupported (the second list below), while
statement attributes that are only hints stay [Sattr].
  $ grep -o 'Sattr ("[a-z_]*"' assume_cpp.v | sort -u
  Sattr ("fallthrough"
  Sattr ("likely"
  Sattr ("loop"
  Sattr ("noinline"
  Sattr ("nomerge"
  Sattr ("unlikely"
  Sattr ("unroll"

  $ dune build
       = ("asm goto"%pstring :: "inline assembly"%pstring :: nil)%list
       : check.M
       = ("statement attribute: assume"%pstring
          :: "builtin whose arguments are not evaluated: __builtin_assume"%pstring
             :: "statement attribute: assume"%pstring
                :: "loop hint: assume_safety"%pstring
                   :: "statement attribute: musttail"%pstring :: nil)%list
       : check.M
       = ("unsupported statement: CoroutineBodyStmt"%pstring
          :: "unsupported statement: CoroutineBodyStmt"%pstring
             :: "unsupported statement: CoroutineBodyStmt"%pstring
                :: "unsupported statement: CoroutineBodyStmt"%pstring
                   :: "template parameter pack"%pstring :: nil)%list
       : check.M
       = nil
       : check.M
       = ("unsupported local declaration: OMPAllocate"%pstring
          :: "unsupported statement: OMPAtomicDirective"%pstring
             :: "unsupported statement: OMPParallelForDirective"%pstring
                :: "unsupported statement: OMPCriticalDirective"%pstring
                   :: "unsupported local declaration: OMPDeclareReduction"%pstring
                      :: "unsupported statement: OMPParallelForDirective"%pstring
                         :: "unsupported statement: OMPParallelDirective"%pstring
                            :: "unsupported statement: OMPParallelSectionsDirective"%pstring
                               :: "unsupported statement: OMPSimdDirective"%pstring
                                  :: "unsupported statement: OMPTaskDirective"%pstring
                                     :: "static local variable"%pstring
                                        :: "unsupported local declaration: OMPThreadPrivate"%pstring
                                           :: "thread_local variable"%pstring
                                              :: nil)%list
       : check.M
       = ("builtin whose arguments are not evaluated: __builtin_constant_p"%pstring
          :: "builtin whose arguments are not evaluated: __assume"%pstring
             :: "builtin whose arguments are not evaluated: __noop"%pstring
                :: "PseudoObjectExpr"%pstring
                   :: "PseudoObjectExpr"%pstring
                      :: "CXXUuidofExpr"%pstring :: nil)%list
       : check.M
