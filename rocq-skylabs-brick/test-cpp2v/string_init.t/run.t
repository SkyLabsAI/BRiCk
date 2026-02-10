  $ . ../setup-project.sh

Compiling the C++ code, use "make Q=" for debugging.
  $ make
  $ ls *.v | wc -l | sed -e 's/ //g'
  2

Compiling the generated Coq files.
  $ dune build
