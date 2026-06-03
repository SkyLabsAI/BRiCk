  $ . ../setup-project.sh

Compiling the C++ code, use "make Q=" for debugging.
  $ make 2> /dev/null
  $ ls *.v | sort
  test.v
  test_cpp.v
  test_templates.v

Compiling the generated Coq files.
  $ dune build
       = nil
       : check.M
       = nil
       : check.M
