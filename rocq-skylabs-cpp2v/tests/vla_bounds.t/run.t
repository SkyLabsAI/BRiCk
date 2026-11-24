Clang evaluates the array bounds of a variably modified type where the type
is declared. For a typedef or an alias declaration, cpp2v prints them as a
[Dvla_bounds] declaration, and prints the forms it does not model as
unsupported. Diagnostics are not shown, since their text varies with the
clang version.
  $ setup_project

  $ make 2> /dev/null

  $ dune build
       = [("td_2d"%pstring,
           [Sdecl
              [Dvla_bounds
                 [Ecast Cl2r (Evar "a" "int"); Ecast Cl2r (Evar "b" "int")]]]);
          ("td_ptr"%pstring,
           [Sdecl [Dvla_bounds [Ecast Cl2r (Evar "a" "int")]]]);
          ("td_ref"%pstring,
           [Sdecl [Dvla_bounds [Ecast Cl2r (Evar "a" "int")]]]);
          ("td_const_outer"%pstring,
           [Sdecl [Dvla_bounds [Eint 3 "int"; Ecast Cl2r (Evar "a" "int")]]]);
          ("td_array_of_ptr"%pstring,
           [Sdecl
              [Dvla_bounds
                 [Ecast Cl2r (Evar "a" "int"); Ecast Cl2r (Evar "b" "int")]]]);
          ("td_declarators"%pstring,
           [Sdecl
              [Dvla_bounds [Ecast Cl2r (Evar "a" "int")];
               Dvla_bounds [Ecast Cl2r (Evar "b" "int")];
               Dvla_bounds [Ecast Cl2r (Evar "c" "int")]]]);
          ("td_alias"%pstring,
           [Sdecl
              [Dvla_bounds
                 [Ecast Cl2r (Evar "a" "int"); Ecast Cl2r (Evar "b" "int")]]]);
          ("td_paren"%pstring,
           [Sdecl [Dvla_bounds [Ecast Cl2r (Evar "a" "int")]]]);
          ("td_effect"%pstring,
           [Sdecl
              [Dvla_bounds
                 [Ecast Cl2r (Eassign (Evar "a" "int") (Eint 1 "int") "int")]]]);
          ("td_sequenced"%pstring,
           [Sdecl
              [Dvla_bounds [Epostinc (Evar "a" "int") "int"];
               Dvla_bounds [Epostinc (Evar "a" "int") "int"]]]);
          ("td_init"%pstring,
           [Sif (Some (Sdecl [Dvla_bounds [Ecast Cl2r (Evar "a" "int")]])) None
              (Ecast Cint2bool (Ecast Cl2r (Evar "a" "int"))) 
              (Sreturn None) (Sseq [])]);
          ("td_of_td"%pstring,
           [Sdecl [Dvla_bounds [Ecast Cl2r (Evar "a" "int")]]; 
            Sdecl []; Sdecl [];
            Sdecl [Dvla_bounds [Ecast Cl2r (Evar "b" "int")]]]);
          ("td_fn_param"%pstring, [Sdecl []]); ("td_plain"%pstring, [Sdecl []])]
       : list (ident * list Stmt)
       = [("td_typeof"%pstring,
           [Sunsupported "variably modified type: unsupported TypeOf type"]);
          ("td_typeof_expr"%pstring,
           [Sdecl [Dvla_bounds [Ecast Cl2r (Evar "a" "int")]];
            Sunsupported "variably modified type: unsupported TypeOfExpr type"]);
          ("td_decltype"%pstring,
           [Sdecl [Dvla_bounds [Ecast Cl2r (Evar "a" "int")]];
            Sunsupported "variably modified type: unsupported Decltype type"]);
          ("td_fn_ret"%pstring,
           [Sunsupported
              "variably modified type: unsupported FunctionProto type"]);
          ("td_atomic"%pstring,
           [Sunsupported "variably modified type: unsupported Atomic type"]);
          ("td_memptr"%pstring,
           [Sunsupported
              "variably modified type: unsupported MemberPointer type"]);
          ("td_tmp"%pstring,
           [Sunsupported "variably modified type: array bound with a temporary"]);
          ("td_triv"%pstring,
           [Sunsupported "variably modified type: array bound with a temporary"]);
          ("td_dflt"%pstring,
           [Sunsupported "variably modified type: array bound with a temporary"]);
          ("td_unsequenced"%pstring,
           [Sunsupported
              "variably modified type: unsequenced array bounds with a side effect"])]
       : list (ident * list Stmt)
