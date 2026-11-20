  $ setup_project

Compiling the C++ code, use "make Q=" for debugging.
  $ make 2> /dev/null
  $ ls *.v | wc -l | sed -e 's/ //g'
  3

Compiling the generated Coq files.
  $ dune build
       = Some
           [("a"%pstring,
             {|
               bf_run := "a";
               bf_width := 3;
               bf_signed := Signed;
               bf_type := "int"
             |});
            ("b"%pstring,
             {|
               bf_run := "a";
               bf_width := 5;
               bf_signed := Signed;
               bf_type := "int"
             |});
            ("u"%pstring,
             {|
               bf_run := "a";
               bf_width := 4;
               bf_signed := Unsigned;
               bf_type := "unsigned int"
             |});
            ("c"%pstring,
             {|
               bf_run := "c";
               bf_width := 2;
               bf_signed := Signed;
               bf_type := "int"
             |});
            ("d"%pstring,
             {|
               bf_run := "d";
               bf_width := 4;
               bf_signed := Signed;
               bf_type := "int"
             |});
            ("e"%pstring,
             {|
               bf_run := "d";
               bf_width := 1;
               bf_signed := Signed;
               bf_type := "int"
             |})]
       : option (list (ident * BitfieldInfo))
       = Some
           [("ok"%pstring,
             {|
               bf_run := "ok";
               bf_width := 4;
               bf_signed := Unsigned;
               bf_type := "unsigned int"
             |})]
       : option (list (ident * BitfieldInfo))
       = Some
           [("n"%pstring,
             {|
               bf_run := "n";
               bf_width := 4;
               bf_signed := Unsigned;
               bf_type := "unsigned char"
             |});
            ("s"%pstring,
             {|
               bf_run := "n";
               bf_width := 3;
               bf_signed := Signed;
               bf_type := "signed char"
             |});
            ("big"%pstring,
             {|
               bf_run := "n";
               bf_width := 40;
               bf_signed := Signed;
               bf_type := "long long"
             |})]
       : option (list (ident * BitfieldInfo))
       = Some
           [("g"%pstring,
             {|
               bf_run := "g";
               bf_width := 2;
               bf_signed := Signed;
               bf_type := "int"
             |})]
       : option (list (ident * BitfieldInfo))
       = Some []
       : option (list (ident * BitfieldInfo))
       = Some
           (Sseq
              [Sreturn
                 (Some
                    (Ecast Cl2r_bitfield
                       (Ebitfield false (Evar "s" "const S&") "a" "int")))])
       : option Stmt
       = Some
           (Sseq
              [Sreturn
                 (Some
                    (Ecast Cl2r_bitfield
                       (Ebitfield true (Ecast Cl2r (Evar "p" "const S*")) "u"
                          "unsigned int")))])
       : option Stmt
       = Some
           (Sseq
              [Sexpr
                 (Ebf_assign (Ebitfield false (Evar "s" "S&") "a" "int")
                    (Ecast Cl2r (Evar "v" "int")) "int")])
       : option Stmt
       = Some
           (Sseq
              [Sexpr
                 (Ebf_assign_op Badd
                    (Ebitfield false (Evar "s" "S&") "b" "int") 
                    (Eint 3 "int") "int")])
       : option Stmt
       = Some
           (Sseq
              [Sreturn
                 (Some
                    (Ecast Cl2r_bitfield
                       (Ebf_preinc (Ebitfield false (Evar "s" "S&") "a" "int")
                          "int")))])
       : option Stmt
       = Some
           (Sseq
              [Sreturn
                 (Some
                    (Ebf_postinc (Ebitfield false (Evar "s" "S&") "a" "int")
                       "int"))])
       : option Stmt
       = Some
           (Sseq
              [Sexpr
                 (Ebf_assign
                    (Ebf_comma (Evar "x" "int")
                       (Ebitfield false (Evar "s" "S&") "a" "int"))
                    (Eint 1 "int") "int")])
       : option Stmt
       = Some
           (Sseq
              [Sexpr
                 (Ebf_assign
                    (Ebf_assign (Ebitfield false (Evar "s" "S&") "a" "int")
                       (Eint 1 "int") "int")
                    (Eint 2 "int") "int")])
       : option Stmt
       = Some
           (Sseq
              [Sreturn
                 (Some
                    (Ecast Cl2r_bitfield
                       (Ebf_if (Ecast Cl2r (Evar "c" "bool"))
                          (Ebitfield false (Evar "s" "S&") "a" "int")
                          (Ebf_glvalue (Evar "x" "int&")) "int&")))])
       : option Stmt
       = Some
           (Sseq
              [Sexpr
                 (Ebf_assign
                    (Ebf_if (Ecast Cl2r (Evar "c" "bool"))
                       (Ebitfield false (Evar "s" "S&") "a" "int")
                       (Ebf_glvalue (Evar "x" "int&")) "int&")
                    (Eint 9 "int") "int")])
       : option Stmt
       = Some (Sseq [Sexpr (Ebitfield false (Evar "s" "S&") "a" "int")])
       : option Stmt
       = Some
           (Sseq
              [Sreturn
                 (Some
                    (Ebinop Badd
                       (Ebinop Badd
                          (Ecast Cl2r_bitfield
                             (Ebitfield false (Evar "b" "Bad&") "x" "int"))
                          (Ecast Cl2r_bitfield
                             (Ebitfield false (Evar "b" "Bad&") "m" "int"))
                          "int")
                       (Ecast (Cintegral "int")
                          (Ecast Cl2r_bitfield
                             (Ebitfield false (Evar "b" "Bad&") "ok"
                                "unsigned int")))
                       "int"))])
       : option Stmt
       = Some
           (Sseq
              [Sreturn
                 (Some
                    (Ecast Cl2r_bitfield
                       (Ebitfield false (Evar "u" "U&") "lo" "unsigned int")))])
       : option Stmt
       = []
       : check.M
