(*
 * Copyright (c) 2019-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bluerock.lang.cpp.syntax.prelude.
Require Import bluerock.lang.cpp.syntax.core.
Require Export bluerock.lang.cpp.syntax.type_notations.

#[local] Open Scope Z_scope.

Module Export ExprNotationsInterface.
  Declare Custom Entry CPP_expr.
  Declare Scope CPP_expr_scope.
  Delimit Scope CPP_expr_scope with cpp_expr.

  Bind Scope CPP_expr_scope with Expr.
  Bind Scope CPP_expr_scope with UnOp.
  Bind Scope CPP_expr_scope with BinOp.
  Bind Scope CPP_expr_scope with BuiltinFn.

  (* Injection from [constr] in case we're printing a subterm we don't recognize *)
  Notation "'{?:' e '}'"
      := e
         ( in custom CPP_expr at level 0
         , e constr
         , format "'[hv' {?:  e } ']'"
         , only printing).
  (* Injection into [constr] in case we're printing this at the top-level *)
  Notation "'{e:' e '}'"
      := e
         ( at level 0
         , e custom CPP_expr at level 200
         , format "'[hv' {e:  e } ']'"
         , only printing)
    : CPP_expr_scope.
End ExprNotationsInterface.

(* TODO (JH): Investigate which (if any) of the subsequent notations we can make
   printing/parsing
 *)

Module ExprNotations.
  (* NOTE: precedences taken from cppreference
       (cf. https://en.cppreference.com/w/cpp/language/operator_precedence).
   *)

  Notation "$ v"
      := (Evar v _)
         ( in custom CPP_expr at level 0
         , v constr
         , format "'[' $ v ']'"
         , only printing).

  Notation "$ :: v"
      := (Eglobal v _)
         ( in custom CPP_expr at level 0
         , v constr
         , format "'[' $ :: v ']'"
         , only printing).

  Notation "$ :: t :: v"
      := (Eenum_const t v)
         ( in custom CPP_expr at level 0
         , t constr
         , v constr
         , format "'[' $ :: t :: v ']'"
         , only printing).

  Notation "'ASCII#' ascii_code"
      := (Echar ascii_code%N _)
         ( in custom CPP_expr at level 0
         , ascii_code constr
         , format "'[' ASCII# ascii_code ']'"
         , only printing).

  (** TODO: add an identity inductive type ([Estring_pretty]?) which is inserted
      into the AST and which can serve as an anchor for a [String Notation].
   *)
  Notation "STRING# bytes"
      := (Estring bytes%list _)
         ( in custom CPP_expr at level 0
         , bytes constr
         , format "'[' STRING# bytes ']'"
         , only printing).

  Notation "# v"
      := (Eint v%Z _)
         ( in custom CPP_expr at level 0
         , v constr
         , format "'[' # v ']'"
         , only printing).

  Notation "# v"
      := (Ebool v)
         ( in custom CPP_expr at level 0
         , v constr
         , format "'[' # v ']'"
         , only printing).

  Notation "'-'" := (Uminus) (in custom CPP_expr at level 0, only printing).
  Notation "'!'" := (Unot) (in custom CPP_expr at level 0, only printing).
  Notation "'~'" := (Ubnot) (in custom CPP_expr at level 0, only printing).
  Notation "'{:unop:UNSUPPORTED:' msg ':}'"
      := (Uunsupported msg)
         ( in custom CPP_expr at level 0
         , msg constr
         , format "'[hv  ' {:unop:UNSUPPORTED: msg :} ']'"
         , only printing).

  (* QUESTION (JH): Is this the right level? *)
  Notation "op x"
      := (Eunop op x _)
         ( in custom CPP_expr at level 30
         , x custom CPP_expr at level 200
         , op custom CPP_expr at level 0
         , format "'[' op x ']'"
         , only printing).

  Notation "'+'" := (Badd) (in custom CPP_expr at level 0, only printing).
  Notation "'&'" := (Band) (in custom CPP_expr at level 0, only printing).
  Notation "'<=>'" := (Bcmp) (in custom CPP_expr at level 0, only printing).
  Notation "'/'" := (Bdiv) (in custom CPP_expr at level 0, only printing).
  Notation "'=='" := (Beq) (in custom CPP_expr at level 0, only printing).
  Notation "'>='" := (Bge) (in custom CPP_expr at level 0, only printing).
  Notation "'>'" := (Bgt) (in custom CPP_expr at level 0, only printing).
  Notation "'<='" := (Ble) (in custom CPP_expr at level 0, only printing).
  Notation "'<'" := (Blt) (in custom CPP_expr at level 0, only printing).
  Notation "'*'" := (Bmul) (in custom CPP_expr at level 0, only printing).
  Notation "'!='" := (Bneq) (in custom CPP_expr at level 0, only printing).
  Notation "'|'" := (Bor) (in custom CPP_expr at level 0, only printing).
  Notation "'%'" := (Bmod) (in custom CPP_expr at level 0, only printing).
  Notation "'<<'" := (Bshl) (in custom CPP_expr at level 0, only printing).
  (* NOTE (JH): The following [Bshr] notation conflicts with parsing nested [ptr<ptr<...>>]
     [type]s, so we leave it disabled and provide explicit notations for the [Ebinop] and
     [Eassign_op] notations.
   *)
  (* Notation "'>>'" := (Bshr) (in custom CPP_expr at level 0, only printing). *)
  Notation "'-'" := (Bsub) (in custom CPP_expr at level 0, only printing).
  Notation "'^'" := (Bxor) (in custom CPP_expr at level 0, only printing).
  Notation "'.*'" := (Bdotp) (in custom CPP_expr at level 0, only printing).
  Notation "'->*'" := (Bdotip) (in custom CPP_expr at level 0, only printing).

  Notation "'(' x .* y ')'"
      := (Ebinop Bdotp x y _)
         ( in custom CPP_expr at level 40
         , x custom CPP_expr at level 200
         , y custom CPP_expr at level 200
         , format "'[hv   ' ( x '/' .* y ) ']'"
         , only printing).
  Notation "'(' x ->* y ')'"
      := (Ebinop Bdotip x y _)
         ( in custom CPP_expr at level 40
         , x custom CPP_expr at level 200
         , y custom CPP_expr at level 200
         , format "'[hv   ' ( x '/' ->* y ) ']'"
         , only printing).

  Notation "'(' x >> y ')'"
      := (Ebinop Bshr x y _)
         ( in custom CPP_expr at level 70
         , x custom CPP_expr at level 200
         , y custom CPP_expr at level 200
         , format "'[hv   ' ( x  '/' >>  y ) ']'"
         , only printing).

  (* QUESTION (JH): Is this the right level? Do we need to consider the precedences of the
     different operators?
   *)
  Notation "'(' x bop y ')'"
      := (Ebinop bop x y _)
         ( in custom CPP_expr at level 160
         , x custom CPP_expr at level 200
         , bop custom CPP_expr at level 0
         , y custom CPP_expr at level 200
         , format "'[hv   ' ( x  '/' bop  y ) ']'"
         , only printing).

  Notation "* e"
      := (Ederef e _)
         ( in custom CPP_expr at level 30
         , e custom CPP_expr at level 200
         , format "'[' * e ']'"
         , only printing).

  Notation "& e"
      := (Eaddrof e)
         ( in custom CPP_expr at level 30
         , e custom CPP_expr at level 200
         , format "'[' & e ']'"
         , only printing).

  Notation "v = e"
      := (Eassign v e _)
         ( in custom CPP_expr at level 160
         , e custom CPP_expr at level 200
         , v custom CPP_expr at level 200
         , format "'[hv  ' v  =  '/' e ']'"
         , only printing).

  Notation "v >>= e"
      := (Eassign_op Bshr v e _)
         ( in custom CPP_expr at level 159
         , e custom CPP_expr at level 200
         , v custom CPP_expr at level 200
         , format "'[hv  ' v  >>=  '/' e ']'"
         , only printing).
  Notation "v bop = e"
      := (Eassign_op bop v e _)
         ( in custom CPP_expr at level 160
         , e custom CPP_expr at level 200
         , v custom CPP_expr at level 200
         , bop custom CPP_expr at level 0
         , format "'[hv  ' v  bop =  '/' e ']'"
         , only printing).

  Notation "++ e"
      := (Epreinc e _)
         ( in custom CPP_expr at level 30
         , e custom CPP_expr at level 200
         , format "'[' ++ e ']'"
         , only printing).
  Notation "e ++"
      := (Epostinc e _)
         ( in custom CPP_expr at level 30
         , e custom CPP_expr at level 200
         , format "'[' e ++ ']'"
         , only printing).
  Notation "-- e"
      := (Epredec e _)
         ( in custom CPP_expr at level 30
         , e custom CPP_expr at level 200
         , format "'[' -- e ']'"
         , only printing).
  Notation "e --"
      := (Epostdec e _)
         ( in custom CPP_expr at level 30
         , e custom CPP_expr at level 200
         , format "'[' e -- ']'"
         , only printing).

  Notation "'(' e1 && e2 ')'"
      := (Eseqand e1 e2)
         ( in custom CPP_expr at level 140
         , e1 custom CPP_expr at level 200
         , e2 custom CPP_expr at level 200
         , format "'[hv   ' ( e1  '/' &&  e2 ) ']'"
         , only printing).

  Notation "'(' e1 || e2 ')'"
      := (Eseqor e1 e2)
         ( in custom CPP_expr at level 150
         , e1 custom CPP_expr at level 200
         , e2 custom CPP_expr at level 200
         , format "'[hv   ' ( e1  '/' ||  e2 ) ']'"
         , only printing).

  Notation "'{:comma:' e1 , e2 ':}'"
      := (Ecomma e1 e2)
         ( in custom CPP_expr at level 170
         , e1 custom CPP_expr at level 200
         , e2 custom CPP_expr at level 200
         , format "'[hv   ' {:comma: e1 ,  e2 :} ']'"
         , only printing).

  Notation "e '()'"
      := (Ecall e nil _)
         ( in custom CPP_expr at level 20
         , e custom CPP_expr at level 200
         , format "'[' e () ']'"
         , only printing).
  Notation "e ( a1 , .. , a2 )"
      := (Ecall e (cons a1 (.. (cons a2 nil) .. )) _)
         ( in custom CPP_expr at level 20
         , e custom CPP_expr at level 200
         , a1 custom CPP_expr at level 200
         , a2 custom CPP_expr at level 200
         , format "'[' e ( '[hv' a1 ,  '/' .. ,  '/' a2 ']' ) ']'"
         , only printing).

  (* TODO (JH): Determine which casts we actually want to print something for *)
  Notation "e"
      := (Ecast _ e)
         ( in custom CPP_expr at level 0
         , e custom CPP_expr at level 200
         , only printing).
  Notation "( t ) e"
    := (Eexplicit_cast cast_style.c t e)
         ( in custom CPP_expr at level 0
         , e custom CPP_expr at level 200
         , only printing).
  Notation "t ( e )"
    := (Eexplicit_cast cast_style.functional t e)
         ( in custom CPP_expr at level 0
         , e custom CPP_expr at level 200
         , only printing).
  Notation "'static_cast<' t '>(' e )"
    := (Eexplicit_cast cast_style.static t e)
         ( in custom CPP_expr at level 0
         , e custom CPP_expr at level 200
         , only printing).
  Notation "'const_cast<' t '>(' e )"
    := (Eexplicit_cast cast_style.const t e)
         ( in custom CPP_expr at level 0
         , e custom CPP_expr at level 200
         , only printing).
  Notation "'reinterpret_cast<' t '>(' e )"
    := (Eexplicit_cast cast_style.reinterpret t e)
         ( in custom CPP_expr at level 0
         , e custom CPP_expr at level 200
         , only printing).
  Notation "'dynamic_cast<' t '>(' e )"
    := (Eexplicit_cast cast_style.dynamic t e)
         ( in custom CPP_expr at level 0
         , e custom CPP_expr at level 200
         , only printing).

  Notation "e . fld"
      := (Emember e fld _ _)
         ( in custom CPP_expr at level 20
         , e custom CPP_expr at level 200
         , fld constr
         , format "'[' e . fld ']'"
         , only printing).

  (* NOTE (JH): [Emember_call (inr ...) ...] doesn't seem to be used so we don't
     include a notation for it.
   *)
  Notation "e . fn ()"
      := (Emember_call (inl (fn, _, _)) e nil _)
         ( in custom CPP_expr at level 20
         , e custom CPP_expr at level 200
         , fn constr
         , format "'[' e . fn () ']'"
         , only printing).
  Notation "e . fn ( a1 , .. , a2 )"
      := (Emember_call (inl (fn, _, _)) e (cons a1 .. (cons a2 nil) ..) _)
         ( in custom CPP_expr at level 20
         , e custom CPP_expr at level 200
         , a1 custom CPP_expr at level 200
         , a2 custom CPP_expr at level 200
         , fn constr
         , format "'[' e . fn ( '[hv' a1 ,  '/' .. ,  '/' a2 ']' ) ']'"
         , only printing).

  Notation "e [ n ]"
      := (Esubscript e n _)
         ( in custom CPP_expr at level 20
         , e custom CPP_expr at level 200
         , n custom CPP_expr at level 200
         , format "'[' e [ n ] ']'"
         , only printing).

  Notation "'sizeof(ty:' ty )"
      := (Esizeof (inl ty) _)
         ( in custom CPP_expr at level 200
         , ty custom CPP_type at level 200
         , format "'[' sizeof(ty:  ty ) ']'"
         , only printing).
  Notation "'sizeof(expr:' e )"
      := (Esizeof (inr e) _)
         ( in custom CPP_expr at level 200
         , e custom CPP_expr at level 200
         , format "'[' sizeof(expr:  e ) ']'"
         , only printing).

  Notation "'alignof(ty:' ty )"
      := (Ealignof (inl ty) _)
         ( in custom CPP_expr at level 200
         , ty custom CPP_type at level 200
         , format "'[' alignof(ty:  ty ) ']'"
         , only printing).
  Notation "'alignof(expr:' e )"
      := (Ealignof (inr e) _)
         ( in custom CPP_expr at level 200
         , e custom CPP_expr at level 200
         , format "'[' alignof(expr:  e ) ']'"
         , only printing).

  Notation "'offsetof(' cls , fld ')'"
      := (Eoffsetof cls fld _)
         ( in custom CPP_expr at level 200
         , fld constr
         , format "'[' offsetof( cls , fld ) ']'"
         , only printing).

  Notation "'#' cls ()"
      := (Econstructor cls nil _)
         ( in custom CPP_expr at level 20
         , cls constr
         , format "'[' # cls () ']'"
         , only printing).
  Notation "'#' cls ( a1 , .. , a2 )"
      := (Econstructor cls (cons a1 .. (cons a2 nil) ..) _)
         ( in custom CPP_expr at level 20
         , a1 custom CPP_expr at level 200
         , a2 custom CPP_expr at level 200
         , cls constr
         , format "'[' # cls ( '[hv' a1 ,  '/' .. ,  '/' a2 ']' ) ']'"
         , only printing).

  Notation "e"
      := (Eimplicit e)
         ( in custom CPP_expr at level 0
         , e custom CPP_expr at level 200
         , only printing).
  Notation "ty '{{VALUE' 'INIT}}'"
      := (Eimplicit_init ty)
         ( in custom CPP_expr at level 0
         , ty custom CPP_type at level 200
         , format "'[' ty {{VALUE  INIT}} ']'"
         , only printing).

  Notation "c ? t : e"
      := (Eif c t e _ _)
         ( in custom CPP_expr at level 160
         , c custom CPP_expr at level 200
         , t custom CPP_expr at level 200
         , e custom CPP_expr at level 200
         , format "'[hv   ' c  '/' ?  t  '/' :  e ']'"
         , only printing).

  Notation "'this'" := (Ethis _) (in custom CPP_expr at level 0, only printing).
  Notation "'nullptr'" := (Enull) (in custom CPP_expr at level 0, only printing).

  (* NOTE: [Einitlist nil (Some _) _] corresponds to an ill-formed program
     (cf. the [Lt] case of [wp_array_init_fill])
   *)
  Notation "( ty ){}"
      := (Einitlist nil None ty)
         ( in custom CPP_expr at level 100
         , ty custom CPP_type at level 200
         , format "'[' ( ty ){} ']'"
         , only printing).
  Notation "( ty ){ e1 , .. , e2 }"
      := (Einitlist (cons e1 .. (cons e2 nil) ..) None ty)
         ( in custom CPP_expr at level 100
         , e1 custom CPP_expr at level 200
         , e2 custom CPP_expr at level 200
         , ty custom CPP_type at level 200
         , format "'[' ( ty ){ '[hv' e1 ,  '/' .. ,  '/' e2 ']' } ']'"
         , only printing).
  Notation "( ty ){ e1 , .. , e2 '}{default:' edefault '}'"
      := (Einitlist (cons e1 .. (cons e2 nil) ..) (Some edefault) ty)
         ( in custom CPP_expr at level 100
         , e1 custom CPP_expr at level 200
         , e2 custom CPP_expr at level 200
         , edefault custom CPP_expr at level 200
         , ty custom CPP_type at level 200
         , format "'[' ( ty ){ '[hv' e1 ,  '/' .. ,  '/' e2 ']' }{default:  '/' edefault } ']'"
         , only printing).

  Notation "'new' ty"
      := (Enew _ nil _ ty None _)
         ( in custom CPP_expr at level 30
         , ty custom CPP_type at level 200
         , format "'[' new  ty ']'"
         , only printing).
  Notation "'new' ( a1 , .. , a2 ) ty"
      := (Enew _ (cons a1 .. (cons a2 nil) ..) _ ty None _)
         ( in custom CPP_expr at level 30
         , a1 custom CPP_expr at level 200
         , a2 custom CPP_expr at level 200
         , ty custom CPP_type at level 200
         , format "'[' new  ( '[hv' a1 ,  '/' .. ,  '/' a2 ']' )  ty ']'"
         , only printing).

  Notation "'new' ty [ esz ]"
      := (Enew _ nil _ ty (Some esz) _)
         ( in custom CPP_expr at level 30
         , esz custom CPP_expr at level 200
         , ty custom CPP_type at level 200
         , format "'[' new  ty [ esz ] ']'"
         , only printing).

  Notation "'new' ( a1 , .. , a2 ) ty [ esz ]"
      := (Enew _ (cons a1 .. (cons a2 nil) ..) _ ty (Some esz) _)
         ( in custom CPP_expr at level 30
         , a1 custom CPP_expr at level 200
         , a2 custom CPP_expr at level 200
         , esz custom CPP_expr at level 200
         , ty custom CPP_type at level 200
         , format "'[' new  ( '[hv' a1 ,  '/' .. ,  '/' a2 ']' )  ty [ esz ] ']'"
         , only printing).

  Notation "'delete' e"
      := (Edelete false _ e _)
         ( in custom CPP_expr at level 30
         , e custom CPP_expr at level 200
         , format "'[' delete  e ']'"
         , only printing).

  Notation "'delete[]' e"
      := (Edelete true _ e _)
         ( in custom CPP_expr at level 30
         , e custom CPP_expr at level 200
         , format "'[' delete[]  e ']'"
         , only printing).

  (* QUESTION (JH): should we have notations which display sequence points? *)
  Notation "e"
      := (Eandclean e)
         ( in custom CPP_expr at level 0
         , e custom CPP_expr at level 200
         , only printing).
  Notation "e"
      := (Ematerialize_temp e _)
         ( in custom CPP_expr at level 0
         , e custom CPP_expr at level 200
         , only printing).

  (* TODO (JH): [Eatomic] *)

  Notation "'__builtin_vaarg(' e , t )"
      := (Eva_arg e t)
         ( in custom CPP_expr at level 0
         , e custom CPP_expr at level 200
         , t custom CPP_expr at level 200
         , format "'[' __builtin_vaarg( e ,  t ) ']'"
         , only printing).

  Notation "e ->~ ty ()"
      := (Epseudo_destructor true ty e)
         ( in custom CPP_expr at level 0
         , ty custom CPP_type at level 200
         , e custom CPP_expr at level 200
         , format "'[' e ->~ ty () ']'"
         , only printing).
  Notation "e .~ ty ()"
      := (Epseudo_destructor false ty e)
         ( in custom CPP_expr at level 0
         , ty custom CPP_type at level 200
         , e custom CPP_expr at level 200
         , format "'[' e .~ ty () ']'"
         , only printing).



  (* TODO (JH): [Earrayloop_init]/[Earrayloop_index]/[Eopaque_ref] *)

  Notation "'{UNSUPPORTED:' msg '}'"
      := (Eunsupported msg _ _)
         ( in custom CPP_expr at level 0
         , msg constr
         , format "'[hv   ' {UNSUPPORTED:  msg } ']'"
         , only printing).
End ExprNotations.
