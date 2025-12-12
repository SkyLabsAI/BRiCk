  $ . ../setup-project.sh

Compiling the C++ code, use "make Q=" for debugging.
  $ make
  make: Nothing to be done for 'all'.
  $ ls *.v | wc -l | sed -e 's/ //g'
  1

Compiling the generated Coq files.
  $ dune build
