  $ setup_project

Compiling the C++ code, use "make Q=" for debugging.
  $ make 2> /dev/null
  $ ls *.v | wc -l | sed -e 's/ //g'
  2

Compiling the generated Coq files.
  $ dune build
       = Some
           (Gopaque
              {|
                o_size := 4;
                o_alignment := 4;
                o_dtor := "C::~C()";
                o_trivially_destructible := true;
                o_delete := None;
                o_reason := "bitfields are not supported"
              |})
       : option GlobDecl
       = []
       : check.M
