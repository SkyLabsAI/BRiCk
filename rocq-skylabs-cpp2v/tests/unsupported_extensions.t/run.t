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

  $ dune build
       = ("asm goto"%pstring
          :: "label"%pstring :: "inline assembly"%pstring :: nil)%list
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
       = ("CallExpr"%pstring
          :: "CallExpr"%pstring
             :: "goto"%pstring
                :: "label"%pstring
                   :: "CallExpr"%pstring
                      :: "PseudoObjectExpr"%pstring
                         :: "PseudoObjectExpr"%pstring
                            :: "CXXUuidofExpr"%pstring :: nil)%list
       : check.M
