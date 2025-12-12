  $ . ../setup-project.sh

Compiling the C++ code, use "make Q=" for debugging.
  $ ulimit -S -s 40960
  $ make 2> /dev/null
  $ ls *.v | wc -l | sed -e 's/ //g'
  2

Compiling the generated Coq files.
  $ dune build
       = ["if consteval"%pstring; "if consteval"%pstring]
       : supported.check.M
