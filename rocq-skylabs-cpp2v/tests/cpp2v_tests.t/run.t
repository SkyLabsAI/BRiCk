  $ setup_project

Compiling the C++ code, use "make Q=" for debugging.
  $ make 2> stderr || cat stderr
  $ ls *.v | wc -l | sed -e 's/ //g'
  11

Compiling the generated Coq files.
  $ dune build
