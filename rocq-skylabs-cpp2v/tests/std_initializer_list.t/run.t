  $ . ../setup-project.sh

Compiling the C++ code, use "make Q=" for debugging.
  $ ulimit -S -s 40960
  $ make 2> /dev/null
  $ ls *.v | wc -l | sed -e 's/ //g'
  2

[test.v] states, per function of [test.cpp], where the [Einitlist_std] nodes are
and whether BRiCk supports that function. Both are scoped to the symbols
[test.cpp] defines, so nothing that <initializer_list> transitively drags in is
recorded here, and a regression is a build failure rather than a diff.
  $ dune build
