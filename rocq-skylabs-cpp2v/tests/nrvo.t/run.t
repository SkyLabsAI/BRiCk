  $ setup_project

Compiling the C++ code, use "make Q=" for debugging.
  $ make 2> /dev/null
  $ ls *.v | wc -l | sed -e 's/ //g'
  2

Compiling the generated Coq files.
  $ dune build
       = ["static local variable"%pstring; "volatile object"%pstring]
       : check.M
       = [("two(int*, bool)"%cpp_name, ["x"%pstring; "y"%pstring]);
          ("trivial()"%cpp_name, ["x"%pstring]);
          ("templ()"%cpp_name, ["x"%pstring]);
          ("shadow(int*)"%cpp_name, ["x"%pstring]);
          ("make(int*)"%cpp_name, ["x"%pstring]);
          ("defaulted_move()"%cpp_name, ["x"%pstring]);
          ("copy_only()"%cpp_name, ["x"%pstring]);
          ("const_rvalue_ref()"%cpp_name, ["x"%pstring]);
          ("const_local(int*)"%cpp_name, ["x"%pstring])]
       : list (name * list localname)
       = [("make(int*)"%cpp_name,
           [Econstructor "S::S(S&&)" [Ecast (Cnoop "S&&") (Evar "x" "S")] "S"]);
          ("const_local(int*)"%cpp_name,
           [Econstructor "S::S(const S&)"
              [Ecast (Cnoop "const S&&") (Evar "x" "const S")] "S"]);
          ("const_rvalue_ref()"%cpp_name,
           [Econstructor "CR::CR(const CR&&)"
              [Ecast (Cnoop "const CR&&") (Evar "x" "CR")] "CR"]);
          ("copy_only()"%cpp_name,
           [Econstructor "Cp::Cp(const Cp&)"
              [Ecast (Cnoop "const Cp&&") (Evar "x" "Cp")] "Cp"]);
          ("defaulted_move()"%cpp_name,
           [Econstructor "Df::Df(Df&&)" [Ecast (Cnoop "Df&&") (Evar "x" "Df")]
              "Df"]);
          ("trivial()"%cpp_name,
           [Econstructor "Tr::Tr(Tr&&)" [Ecast (Cnoop "Tr&&") (Evar "x" "Tr")]
              "Tr"]);
          ("templ()"%cpp_name,
           [Econstructor "W<int>::W(W<int>&&)"
              [Ecast (Cnoop "W<int>&&") (Evar "x" "W<int>")] "W<int>"])]
       : list (name * list Expr)
