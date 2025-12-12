  $ . ../setup-project.sh

Compiling the C++ code, use "make Q=" for debugging.
  $ make 2> /dev/null
  $ ls *.v | wc -l | sed -e 's/ //g'
  3

Compiling the generated Coq files.
  $ dune build
       = ("bitfields are not supported"%pstring :: nil)%list
       : check.M
