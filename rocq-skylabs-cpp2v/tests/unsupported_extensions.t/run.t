Extensions that cpp2v cannot print faithfully become [Sunsupported],
[Eunsupported] or [Tunsupported]; each source is compiled with the flags that
enable its extension (see the Makefile). Diagnostics are not shown, since their
text varies with the clang version.
  $ setup_project

  $ make > make.log 2>&1

Named loops: [named.sh] checks that `break outer;` and `continue outer;` print
as [Sunsupported] and that a plain `break` does not. The flag `-fnamed-loops`
exists from clang 22; before, the check is vacuous.
  $ sh named.sh
  named loops: ok

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
