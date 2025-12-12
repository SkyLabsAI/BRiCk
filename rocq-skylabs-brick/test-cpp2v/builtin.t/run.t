  $ . ../setup-project.sh

Compiling the C++ code, use "make Q=" for debugging.
  $ ulimit -S -s 40960
  $ make
  $ ls *.v | wc -l | sed -e 's/ //g'
  1

Compiling the generated Coq files.
  $ dune build
