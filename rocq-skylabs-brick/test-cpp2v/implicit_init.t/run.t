  $ . ../setup-project.sh

Compiling the C++ code, use "make Q=" for debugging.
  $ make 2> /dev/null
  [2]
  $ ls *.v | wc -l | sed -e 's/ //g'
  5

Compiling the generated Coq files.
  $ dune build
  Success!
