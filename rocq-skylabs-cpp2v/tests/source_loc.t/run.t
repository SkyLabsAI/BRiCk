  $ setup_project

Compiling the C++ code, use "make Q=" for debugging.
  $ make
  $ ls *.v | wc -l | sed -e 's/ //g'
  3

Compiling the generated Coq files.
  $ dune build
       = nil
       : check.M

Default arguments and member initializers use the outermost default's use site.
The explicit line directives also check that each scope is restored afterwards.
  $ clang++ -std=c++17 defaults.cpp -o defaults.exe
  $ ./defaults.exe
  $ tr '\n' ' ' < defaults_cpp.v | tr -s ' ' | grep -o 'Esource_loc "__builtin_LINE" (Eint [0-9]*' | sed 's/.*Eint //'
  3
  3
  51
  52
  100
  200
  300
  400
  500
  600
