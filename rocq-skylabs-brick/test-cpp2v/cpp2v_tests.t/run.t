  $ . ../setup-project.sh

Compiling the C++ code, use "make Q=" for debugging.
  $ make 2> stderr || cat stderr
  $ ls *.v | wc -l | sed -e 's/ //g'
  21

Compiling the generated Coq files.
  $ dune build
