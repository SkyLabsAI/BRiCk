  $ setup_project

Compiling the C++ code, use "make Q=" for debugging.
  $ make 2> /dev/null

Compiling the generated Coq files.
  $ dune build
       = [("U::operator=(U&&)"%cpp_name, "Defaulted");
          ("U::operator=(const U&)"%cpp_name, "Defaulted");
          ("U::U(U&&)"%cpp_name, "Defaulted");
          ("U::U(const U&)"%cpp_name, "Defaulted");
          ("U::U()"%cpp_name, "CompilerProvided")]
       : list (obj_name * string)
       = [("N::operator=(N&&)"%cpp_name, "none");
          ("N::operator=(const N&)"%cpp_name, "none");
          ("N::N(N&&)"%cpp_name, "none"); ("N::N(const N&)"%cpp_name, "none");
          ("N::N()"%cpp_name, "CompilerProvided")]
       : list (obj_name * string)
  Success!
