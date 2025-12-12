(*
 * Copyright (c) 2019-2025 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import Stdlib.ZArith.ZArith.

Require Import bluerock.prelude.bytestring.
Require bluerock.lang.cpp.syntax.
Require Import bluerock.lang.cpp.syntax.stmt.
Require Export bluerock.lang.cpp.syntax.expr_notations.
Require Export bluerock.lang.cpp.syntax.type_notations.

#[local] Open Scope Z_scope.
#[local] Open Scope bs_scope.

Module Export StmtNotationsInterface.
  Declare Custom Entry CPP_stmt.
  Declare Scope CPP_stmt_scope.
  Delimit Scope CPP_stmt_scope with cpp_stmt.

  Bind Scope CPP_stmt_scope with Stmt.
  Bind Scope CPP_stmt_scope with VarDecl.

  (* Injection from [constr] in case we're printing a subterm we don't recognize *)
  Notation "'{?:' s '};'"
      := s
         ( in custom CPP_stmt at level 0
         , s constr
         , format "'[hv' {?:  s }; ']'"
         , only printing).
  (* Injection into [constr] in case we're printing this at the top-level *)
  Notation "'{s:' s '}'"
      := (s)
         ( at level 0
         , s custom CPP_stmt at level 200
         , format "'[hv' {s:  s } ']'"
         , only printing)
    : CPP_stmt_scope.
End StmtNotationsInterface.

(* TODO (JH): Investigate which (if any) of the subsequent notations we can make
   printing/parsing
 *)

Module StmtNotations.
  (* Statements that provide their own line break

     NOTES (JH):
     - [Stmt]s will be enclosed in [{(stmt: ...)}], so we don't include curly braces here.
     - terminal [Stmt]s will have notations which insert semicolons (and the appropriate
       spacing after them).
   *)
  Notation "'//' 'end' 'block'"
      := (Sseq nil)
         ( in custom CPP_stmt at level 0
         , format "'[' //  end  block ']'"
         , only printing).
  Notation "s"
      := (Sseq (cons s nil))
         ( in custom CPP_stmt at level 0
         , s custom CPP_stmt at level 200
         , format "'[' s ']'"
         , only printing).
  Notation "s1 .. s2 '//' 'end' 'block'"
      := (Sseq (cons s1 .. (cons s2 nil) ..))
         ( in custom CPP_stmt at level 0
         , s1 custom CPP_stmt at level 200
         , s2 custom CPP_stmt at level 200
         , format "'[v' s1 '/' .. '/' s2 '//' //  end  block ']'"
         , only printing).

  (* TODO (JH): Notations for other [VarDecl] forms *)
  Notation "ty $ v ;"
      := (Dvar v%bs ty None)
         ( in custom CPP_stmt at level 0
         , ty custom CPP_type at level 200
         , v constr
         , format "'[' ty  $ v ; ']'"
         , only printing).
  Notation "ty $ v = e ;"
      := (Dvar v%bs ty (Some e))
         ( in custom CPP_stmt at level 0
         , e custom CPP_expr at level 200
         , ty custom CPP_type at level 200
         , v constr
         , format "'[' ty  $ v  =  e ; ']'"
         , only printing).

  Notation "'//' 'end' 'decl' 'block'"
      := (Sdecl nil)
         ( in custom CPP_stmt at level 0
         , format "//  end  decl  block"
         , only printing).
  Notation "d"
      := (Sdecl (cons d nil))
         ( in custom CPP_stmt at level 0
         , d custom CPP_stmt at level 200
         , format "'[' d ']'"
         , only printing).
  Notation "d1 .. d2"
      := (Sdecl (cons d1 .. (cons d2 nil) ..))
         ( in custom CPP_stmt at level 0
         , d1 custom CPP_stmt at level 200
         , d2 custom CPP_stmt at level 200
         , format "'[v' d1 '/' .. '/' d2 ']'"
         , only printing).

  Notation "'if' ( cond ) { thn } 'else' { els }"
      := (Sif None cond thn els)
         ( in custom CPP_stmt at level 200
         , cond custom CPP_expr at level 200
         , thn custom CPP_stmt at level 200
         , els custom CPP_stmt at level 200
         , format "'[hv' if  ( cond )  { '//'   thn '//' }  else  { '//'   els '//' } ']'"
         , only printing).
  Notation "'if' ( decl cond ) { thn } 'else' { els }"
      := (Sif (Some decl) cond thn els)
         ( in custom CPP_stmt at level 200
         , decl custom CPP_stmt
         , cond custom CPP_expr at level 200
         , thn custom CPP_stmt at level 200
         , els custom CPP_stmt at level 200
         , format "'[hv' if  ( '[hv   ' decl  '/' cond ']' )  { '//'   thn '//' }  else  { '//'   els '//' } ']'"
         , only printing).

  Notation "'while' ( cond ) { body }"
      := (Swhile None cond body)
         ( in custom CPP_stmt at level 200
         , cond custom CPP_expr at level 200
         , body custom CPP_stmt at level 200
         , format "'[hv' while  ( cond )  { '//'   body '//' } ']'"
         , only printing).
  Notation "'while' ( decl cond ) { body }"
      := (Swhile (Some decl) cond body)
         ( in custom CPP_stmt at level 200
         , decl custom CPP_stmt at level 200
         , cond custom CPP_expr at level 200
         , body custom CPP_stmt at level 200
         , format "'[hv' while  ( '[hv  ' decl  '/' cond ']' )  { '//'   body '//' } ']'"
         , only printing).

  Notation "'for' '(;;)' { body }"
      := (Sfor None None None body)
         ( in custom CPP_stmt at level 200
         , body custom CPP_stmt at level 200
         , format "'[hv' for  (;;)  { '//'   body '//' } ']'"
         , only printing).
  (* NOTE (JH): init will insert a semicolon since it will be a terminal stmt in realistic ASTs *)
  Notation "'for' ( init ';)' { body }"
      := (Sfor (Some init) None None body)
         ( in custom CPP_stmt at level 200
         , init custom CPP_stmt at level 200
         , body custom CPP_stmt at level 200
         , format "'[hv' for  ( init ;)  { '//'   body '//' } ']'"
         , only printing).
  Notation "'for' '(;' cond ';)' { body }"
      := (Sfor None (Some cond) None body)
         ( in custom CPP_stmt at level 200
         , cond custom CPP_expr at level 200
         , body custom CPP_stmt at level 200
         , format "'[hv' for  (;  cond ;)  { '//'   body '//' } ']'"
         , only printing).
  Notation "'for' '(;;' incr ) { body }"
      := (Sfor None None (Some incr) body)
         ( in custom CPP_stmt at level 200
         , incr custom CPP_expr at level 200
         , body custom CPP_stmt at level 200
         , format "'[hv' for  (;;  incr )  { '//'   body '//' } ']'"
         , only printing).
  (* NOTE (JH): init will insert a semicolon since it will be a terminal stmt in realistic ASTs *)
  Notation "'for' ( init cond ';)' { body }"
      := (Sfor (Some init) (Some cond) None body)
         ( in custom CPP_stmt at level 200
         , init custom CPP_stmt at level 200
         , cond custom CPP_expr at level 200
         , body custom CPP_stmt at level 200
         , format "'[hv' for  ( init  cond ;)  { '//'   body '//' } ']'"
         , only printing).
  (* NOTE (JH): init will insert a semicolon since it will be a terminal stmt in realistic ASTs *)
  Notation "'for' ( init ; incr ) { body }"
      := (Sfor (Some init) None (Some incr) body)
         ( in custom CPP_stmt at level 200
         , init custom CPP_stmt at level 200
         , incr custom CPP_expr at level 200
         , body custom CPP_stmt at level 200
         , format "'[hv' for  ( init ;  incr )  { '//'   body '//' } ']'"
         , only printing).
  Notation "'for' (; cond ; incr ) { body }"
      := (Sfor None (Some cond) (Some incr) body)
         ( in custom CPP_stmt at level 200
         , cond custom CPP_expr at level 200
         , incr custom CPP_expr at level 200
         , body custom CPP_stmt at level 200
         , format "'[hv' for  (;  cond ;  incr )  { '//'   body '//' } ']'"
         , only printing).
  (* NOTE (JH): init will insert a semicolon since it will be a terminal stmt in realistic ASTs *)
  Notation "'for' ( init cond ; incr ) { body }"
      := (Sfor (Some init) (Some cond) (Some incr) body)
         ( in custom CPP_stmt at level 200
         , init custom CPP_stmt at level 200
         , cond custom CPP_expr at level 200
         , incr custom CPP_expr at level 200
         , body custom CPP_stmt at level 200
         , format "'[hv' for  ( init  cond ;  incr )  { '//'   body '//' } ']'"
         , only printing).

  Notation "'do' { bod } 'while' ( e ) ;"
      := (Sdo bod e)
         ( in custom CPP_stmt at level 200
         , e custom CPP_expr at level 200
         , bod custom CPP_stmt at level 200
         , format "'[hv' do  { '//'   bod '//' }  while ( e ) ; ']'"
         , only printing).

  (* TODO (JH): [Sswitch]/[Scase]/[Sdefault] *)

  Notation "'break;'"
      := (Sbreak)
         ( in custom CPP_stmt at level 0
         , format "'[' break; ']'"
         , only printing).

  Notation "'continue;'"
      := (Scontinue)
         ( in custom CPP_stmt at level 0
         , format "'[' continue; ']'"
         , only printing).

  Notation "'return;'"
      := (Sreturn None)
         ( in custom CPP_stmt at level 0
         , format "'[' return; ']'"
         , only printing).
  Notation "'return' e ;"
      := (Sreturn (Some e))
         ( in custom CPP_stmt at level 0
         , e custom CPP_expr at level 200
         , format "'[' return  e ; ']'"
         , only printing).

  Notation "e ;"
      := (Sexpr e)
         ( in custom CPP_stmt at level 0
         , e custom CPP_expr at level 200
         , format "'[' e ; ']'"
         , only printing).

  Notation "s"
      := (Sattr nil s)
         ( in custom CPP_stmt at level 0
         , s custom CPP_stmt at level 200
         , format "'[' s ']'"
         , only printing).
  Notation "'[[' attr1 , .. , attr2 ']]' s"
      := (Sattr (cons attr1%bs .. (cons attr2%bs nil) ..) s)
         ( in custom CPP_stmt at level 0
         , attr1 constr
         , attr2 constr
         , s custom CPP_stmt at level 200
         , format "'[' [[ '[hv' attr1 ,  '/' .. ,  '/' attr2 ']' ]]  s ']'"
         , only printing).

  (* TODO (JH): [Sasm] *)

  Notation "'<LABEL:' lbl > s"
      := (Slabeled lbl%bs s)
         ( in custom CPP_stmt at level 0
         , lbl constr
         , s custom CPP_stmt at level 200
         , format "'[' <LABEL:  lbl >  s ']'"
         , only printing).

  Notation "'goto' lbl ;"
      := (Sgoto lbl%bs)
         ( in custom CPP_stmt at level 0
         , lbl constr
         , format "'[' goto  lbl ; ']'"
         , only printing).

  Notation "'{UNSUPPORTED:' msg '}'"
      := (Sunsupported msg%bs)
         ( in custom CPP_stmt at level 0
         , msg constr
         , format "'[hv   ' {UNSUPPORTED:  msg } ']'"
         , only printing).
End StmtNotations.
