  $ setup_project

Compiling the C++ code, use "make Q=" for debugging.
  $ make 2> /dev/null
  $ ls *.v | wc -l | sed -e 's/ //g'
  4

Compiling the generated Coq files.
  $ dune build
       = [("T::~T()"%cpp_name, Some (CompilerProvided (Sseq [])));
          ("M::~M()"%cpp_name, None);
          ("B::~B()"%cpp_name, Some (CompilerProvided (Sseq [])));
          ("A::~A()"%cpp_name, Some (CompilerProvided (Sseq [])))]
       : list (obj_name * option (OrDefault Stmt))
       = [("T::~T()"%cpp_name, Some Defaulted); ("M::~M()"%cpp_name, None);
          ("B::~B()"%cpp_name, Some Defaulted);
          ("A::~A()"%cpp_name, Some Defaulted)]
       : list (obj_name * option (OrDefault Stmt))
       = [("T::~T()"%cpp_name, Some (CompilerProvided (Sseq [])));
          ("M::~M()"%cpp_name, None);
          ("B::~B()"%cpp_name, Some (CompilerProvided (Sseq [])));
          ("A::~A()"%cpp_name, Some (CompilerProvided (Sseq [])))]
       : list (obj_name * option (OrDefault Stmt))
  Success!
