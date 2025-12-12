(*
 * Copyright (c) 2019-2023 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bluerock.lang.cpp.syntax.
Require Import bluerock.lang.cpp.logic.
Require Import bluerock.lang.cpp.logic.atomics.
Require Import bluerock.lang.cpp.logic.builtins.

Require bluerock.lang.cpp.code_notations.
Import type_notations.TypeNotationsInterface.
Import expr_notations.ExprNotationsInterface.
Import stmt_notations.StmtNotationsInterface.

Module Export RegionNotationsInterface.
  Declare Custom Entry CPP_region.
  Declare Scope CPP_region_scope.
  Delimit Scope CPP_region_scope with cpp_region.

  Bind Scope CPP_region_scope with region.
End RegionNotationsInterface.

Module Export RegionNotations.
  (* Injection into [constr] in case we're printing this at the top-level *)
  Notation "'[region:' ρ ]"
      := (ρ)
         ( at level 0
         , ρ custom CPP_region at level 30
         , format "'[hv  ' [region:  '/' '[' ρ ']' ] ']'")
    : CPP_region_scope.

  (* [Remp othisp ovarargp rty] *)
  Notation "'return' rty"
      := (Remp None None rty)
         ( in custom CPP_region at level 0
         , rty custom CPP_type at level 200
         , format "'[  ' return  rty ']'").
  Notation "[ 'this' := thisp ] ; 'return' rty"
      := (Remp (Some thisp) None rty)
         ( in custom CPP_region at level 10
         , thisp constr
         , rty custom CPP_type at level 200
         , format "'[' [ this  :=  thisp ] ']' ;  '/' '[  ' return  '/' rty ']'").
  Notation "[ 'variadic' := varargp ] ; 'return' rty"
      := (Remp None (Some varargp) rty)
         ( in custom CPP_region at level 10
         , varargp constr
         , rty custom CPP_type at level 200
         , format "'[' [ variadic  :=  varargp ] ']' ;  '/' '[  ' return  '/' rty ']'").
  Notation "[ 'this' := thisp ] ; [ 'variadic' := varargp ] ; 'return' rty"
      := (Remp (Some thisp) (Some varargp) rty)
         ( in custom CPP_region at level 20
         , thisp constr
         , varargp constr
         , rty custom CPP_type at level 200
         , format "'[' [ this  :=  thisp ] ']' ;  '/' '[' [ variadic  :=  varargp ] ']' ;  '/' '[  ' return  '/' rty ']'").

  (* [Rbind nm p ρ] *)
  Notation "v @ p ';' ρ "
      := (Rbind v p ρ)
         (in custom CPP_region at level 30
         , v constr
         , p constr
         , ρ custom CPP_region at level 30
         , format "'[' v  @  p ']' ;  '/' ρ").
End RegionNotations.

(* NOTES (JH):
   - we intentionally use [constr] for all [Compact]/[Verbose] notations to ensure
     that the [region]/[Expr]/[Stmt]s are printed in the appropriate
     "quotation" (e.g. [expr:{{...}}], [[region: ...]], [stmt:{{...}}].
   - [Compact]/[Verbose] alternatives for [type]/[Expr]/[Stmt] might provide
     an ad-hoc way of "disabling" a notation (by importing a new [Module] which
     fully shadows the notations you wish to "swap out".
 *)

Module Export Compact.
  (* [Stmt] WP *)
  Notation "'::wpS' ρ s"
      := (wp _ ρ s _)
         ( at level 10
         , s at level 0
         , format "'[hv  ' ::wpS  '/' '[hv' ρ  '/' s ']' ']'"
         , only printing).
  Notation "'::wpD' ρ decl"
      := (wp_decl _ ρ decl _)
         ( at level 10
         , decl at level 0
         , format "'[hv  ' ::wpD  '/' '[hv' ρ  '/' decl ']' ']'"
         , only printing).

  (* Special WPs*)
  Notation "'::wpAtomic' '(Mask' ↦ M ; 'Type' ↦ ty ) '{e:' atomic '()}'"
      := (wp_atom M atomic ty%cpp_type nil _)
         ( at level 10
         , ty custom CPP_type at level 200
         , atomic at level 200
         , format "'[hv  ' ::wpAtomic  '/' '[hv' '[hv' (Mask  ↦  M ;  '/' Type  ↦  ty )  ']' '/' '[' {e:  atomic ()} ']' ']' ']'"
         , only printing).
  Notation "'::wpAtomic' '(Mask' ↦ M ; 'Type' ↦ ty ) '{e:' atomic '(' v1 , .. , v2 ')}'"
      := (wp_atom M atomic ty%cpp_type (cons v1 (.. (cons v2 nil) ..)) _)
         ( at level 10
         , ty custom CPP_type at level 200
         , atomic at level 200
         , format "'[hv  ' ::wpAtomic  '/' '[hv' '[hv' (Mask  ↦  M ;  '/' Type  ↦  ty )  ']' '/' '[' {e:  atomic ( '[hv' v1 ,  '/' .. ,  '/' v2 ']' )} ']' ']' ']'"
         , only printing).

  Notation "'::wpBuiltin' '(Type' ↦ ty ) '{e:' builtin '()}'"
      := (wp_builtin builtin%pstring ty%cpp_type nil _)
         ( at level 10
         , ty custom CPP_type at level 200
         , builtin at level 200
         , format "'[hv  ' ::wpBuiltin  '/' '[hv' '[hv' (Type  ↦  ty )  ']' '/' '[' {e:  builtin ()} ']' ']' ']'"
         , only printing).
  Notation "'::wpBuiltin' '(Type' ↦ ty ) '{e:' builtin '(' v1 , .. , v2 ')}'"
      := (wp_builtin builtin%pstring ty%cpp_type (cons v1 (.. (cons v2 nil) ..)) _)
         ( at level 10
         , ty custom CPP_type at level 200
         , builtin at level 200
         , format "'[hv  ' ::wpBuiltin  '/' '[hv' '[hv' (Type  ↦  ty )  ']' '/' '[' {e:  builtin ( '[hv' v1 ,  '/' .. ,  '/' v2 ']' )} ']' ']' ']'"
         , only printing).

  (* Destruction/cleanup-interpretation of temporaries *)
  Notation "'::destroy_val' '{pointer:' p ';' 'type:' ty '}'"
      := (destroy_val _ ty%cpp_type p _)
         ( at level 10
         , ty custom CPP_type at level 200
         , format "'[hv  ' ::destroy_val  '/' '[hv   ' {pointer:  p ; '/'  type:  ty } ']' ']'"
         , only printing).
  Notation "'::destroy_val' '{pointer:' p ';' 'qualifiers:' cv ';' 'type:' ty '}'"
      := (wp_destroy_val _ cv%cpp_type ty%cpp_type p _)
         ( at level 10
         , cv custom CPP_type at level 200
         , ty custom CPP_type at level 200
         , format "'[hv  ' ::destroy_val  '/' '[hv   ' {pointer:  p ; '/'  qualifiers:  cv ; '/'  type:  ty } ']' ']'"
         , only printing).
  (* NOTE (JH): large [free]s are printed a bit strangely (cf. [NOTATIONS_interp_wrap]) *)
  Notation "'::interp' { free }"
        := (interp _ free _)
           ( at level 10
           , format "'[hv  ' ::interp  '/' {  free  } ']'"
           , only printing).

  (* Expression WPs *)
  Notation "'::wpL' ρ e"
        := (wp_lval _ ρ e _)
           ( at level 10
           , e at level 0
           , format "'[hv  ' ::wpL  '/' '[hv' ρ  '/' e ']' ']'"
           , only printing).
  Notation "'::wpPRᵢ' ρ '(Pointer' ↦ p ) e"
        := (wp_init _ ρ _ p e _)
           ( at level 10
           , e at level 0
           , format "'[hv  ' ::wpPRᵢ  '/' '[hv' ρ  '/' '[' (Pointer  ↦  p )  ']' '/' e ']' ']'"
           , only printing).
  Notation "'::wpPR' ρ e"
        := (wp_prval _ ρ e _)
           ( at level 10
           , e at level 0
           , format "'[hv  ' ::wpPR  '/' '[hv' ρ  '/' e ']' ']'"
           , only printing).
  Notation "'::wpOperand' ρ e"
        := (wp_operand _ ρ e _)
           ( at level 10
           , e at level 0
           , format "'[hv  ' ::wpOperand  '/' '[hv' ρ  '/' e ']' ']'"
           , only printing).
  Notation "'::wpX' ρ e"
        := (wp_xval _ ρ e _)
           ( at level 10
           , e at level 0
           , format "'[hv  ' ::wpX  '/' '[hv' ρ  '/' e ']' ']'"
           , only printing).
  Notation "'::wpGL' ρ e"
        := (wp_glval _ ρ e _)
           ( at level 10
           , e at level 0
           , format "'[hv  ' ::wpGL  '/' '[hv' ρ  '/' e ']' ']'"
           , only printing).
  Notation "'::wpGLₓ' ρ e"
        := (wp_discard _ ρ e _)
           ( at level 10
           , e at level 0
           , format "'[hv  ' ::wpGLₓ  '/' '[hv' ρ  '/' e ']' ']'"
           , only printing).
  (* NOTE (JH): There isn't anything great to print from [Func] since the name was erased *)
  Notation "'::wpFunc'"
        := (wp_func _ _ _)
           ( at level 0
           , format "'[hv  ' ::wpFunc ']'"
           , only printing).
  (* NOTE (JH): There isn't anything great to print from [Method] since the name was erased *)
  Notation "'::wpMethod'"
        := (wp_method _ _ _)
           ( at level 0
           , format "'[hv  ' ::wpMethod ']'"
           , only printing).
  (* NOTE (JH): There isn't anything great to print from [Ctor] since the name is erased *)
  Notation "'::wpCtor'"
        := (wp_ctor _ _ _)
           ( at level 0
           , format "'[hv  ' ::wpCtor ']'"
           , only printing).
  (* NOTE (JH): There isn't anything great to print from [Dtor] since the name is erased *)
  Notation "'::wpDtor'"
        := (wp_dtor _ _ _)
           ( at level 0
           , format "'[hv  ' ::wpDtor ']'"
           , only printing).
  (* TODO (JH): print something more useful *)
  Notation "'::wpArgs' ρ"
        := (wp_args _ ρ _ _ _)
           ( at level 10
           , ρ at level 0
           , format "'[hv  ' ::wpArgs  '/' ρ ']'"
           , only printing).
  Notation "'::wpInitialize' ρ ( p '|->' 'type_ptrR' ty ) e"
        := (wp_initialize _ ρ ty%cpp_type p e _)
           ( at level 10
           , e at level 0
           , ty custom CPP_type at level 200
           , format "'[hv  ' ::wpInitialize  '/' ρ  '/' '[hv   ' ( p  |->  '/' type_ptrR  ty ) ']'  '/' e ']'"
           , only printing).
  Notation "'::wpCond' ρ ( T )"
        := (wp_cond _ ρ (T:=T) _)
           ( at level 10
           , format "'[hv  ' ::wpCond  '/' ρ  '/' '[' ( T ) ']' ']'"
           , only printing).
  (* TODO (JH): print something more useful *)
  Notation "'::wpCall' ρ"
        := (wp_call _ ρ _ _ _ _)
           ( at level 10
           , ρ at level 0
           , format "'[hv  ' ::wpCall  '/' ρ ']'"
           , only printing).
  (* TODO (JH): print something more useful *)
  Notation "'::wpMCall' ρ"
        := (wp_mcall _ ρ _ _ _ _ _ _)
           ( at level 10
           , ρ at level 0
           , format "'[hv  ' ::wpMCall  '/' ρ ']'"
           , only printing).
End Compact.

Module Verbose.
  (* [Stmt] WP *)
  Notation "'::wpS' ρ s K"
      := (wp _ ρ s K)
         ( at level 10
         , s at level 0
         , K at level 0
         , format "'[hv  ' ::wpS  '/' '[hv' ρ  '/' s ']'  '/' K ']'"
         , only printing).
  Notation "'::wpD' ρ decl Q"
      := (wp_decl _ ρ decl Q)
         ( at level 10
         , ρ at level 0
         , decl at level 0
         , Q at level 0
         , format "'[hv  ' ::wpD  '/' '[hv' ρ  '/' decl ']'  '/' Q ']'"
         , only printing).

  (* Special WPs*)
  Notation "'::wpAtomic' '(Mask' ↦ M ; 'Type' ↦ ty ) '{e:' atomic '()}' Q"
      := (wp_atom M atomic ty%cpp_type nil Q)
         ( at level 10
         , Q at level 0
         , ty custom CPP_type at level 200
         , format "'[hv  ' ::wpAtomic  '/' '[hv' '[hv' (Mask  ↦  M ;  '/' Type  ↦  ty )  ']' '/'  '[' {e:  atomic ()} ']' ']'  '/' Q ']'"
         , only printing).
  Notation "'::wpAtomic' '(Mask' ↦ M ; 'Type' ↦ ty ) '{e:' atomic '(' v1 , .. , v2 ')}' Q"
      := (wp_atom M atomic ty%cpp_type (cons v1 (.. (cons v2 nil) ..)) Q)
         ( at level 10
         , Q at level 0
         , ty custom CPP_type at level 200
         , format "'[hv  ' ::wpAtomic  '/' '[hv' '[hv' (Mask  ↦  M ;  '/' Type  ↦  ty )  ']' '/'  '[' {e:  atomic ( '[hv' v1 ,  '/' .. ,  '/' v2 ']' )} ']' ']'  '/' Q ']'"
         , only printing).

  Notation "'::wpBuiltin' '(Type' ↦ ty ) '{e:' builtin '()}' Q"
      := (wp_builtin builtin%cpp_expr ty%cpp_type nil Q)
         ( at level 10
         , Q at level 0
         , ty custom CPP_type at level 200
         , format "'[hv  ' ::wpBuiltin  '/' '[hv' '[hv' (Type  ↦  ty )  ']' '/' '[' {e:  builtin ()} ']' ']'  '/' Q ']'"
         , only printing).
  Notation "'::wpBuiltin' '(Type' ↦ ty ) '{e:' builtin '(' v1 , .. , v2 ')}' Q"
      := (wp_builtin builtin%cpp_expr ty%cpp_type (cons v1 (.. (cons v2 nil) ..)) Q)
         ( at level 10
         , Q at level 0
         , ty custom CPP_type at level 200
         , format "'[hv  ' ::wpBuiltin  '/' '[hv' '[hv' (Type  ↦  ty )  ']' '/' '[' {e:  builtin ( '[hv' v1 ,  '/' .. ,  '/' v2 ']' )} ']' ']'  '/' Q ']'"
         , only printing).

  (* Destruction/cleanup-interpretation of temporaries *)
  Notation "'::destroy_val' '{pointer:' p ';' 'type:' ty '}' E"
      := (destroy_val _ ty%cpp_type p E)
         ( at level 10
         , E at level 0
         , ty custom CPP_type at level 200
         , format "'[hv  ' ::destroy_val  '/' '[hv   ' {pointer:  p ; '/'  type:  ty } ']'  '/' E ']'"
         , only printing).
  (* Destruction/cleanup-interpretation of temporaries *)
  Notation "'::destroy_val' '{pointer:' p ';' 'qualifiers:' cv ';' 'type:' ty '}' E"
      := (wp_destroy_val _ cv%cpp_type ty%cpp_type p E)
         ( at level 10
         , E at level 0
         , cv custom CPP_type at level 200
         , ty custom CPP_type at level 200
         , format "'[hv  ' ::destroy_val  '/' '[hv   ' {pointer:  p ; '/'  qualifiers:  cv ; '/'  type:  ty } ']'  '/' E ']'"
         , only printing).
  (* NOTE (JH): large [free]s are printed a bit strangely (cf. [NOTATIONS_interp_wrap]) *)
  Notation "'::interp' { free } E"
        := (interp _ free E)
           ( at level 10
           , E at level 0
           , format "'[hv  ' ::interp  '/' {  free  }   '/' E ']'"
           , only printing).

  (* Expression WPs *)
  Notation "'::wpL' ρ e Q"
        := (wp_lval _ ρ e Q)
           ( at level 10
           , ρ at level 0
           , e at level 0
           , Q at level 0
           , format "'[hv  ' ::wpL  '/' '[hv' ρ  '/' e ']'  '/' Q ']'"
           , only printing).
  Notation "'::wpPRᵢ' ρ '(Pointer' ↦ p ) e Q"
        := (wp_init _ ρ _ p e Q)
           ( at level 10
           , ρ at level 0
           , e at level 0
           , Q at level 0
           , format "'[hv  ' ::wpPRᵢ  '/' '[hv' ρ  '/' '[' (Pointer  ↦  p )  ']' '/' e ']'  '/' Q ']'"
           , only printing).
  Notation "'::wpPR' ρ e Q"
        := (wp_prval _ ρ e Q)
           ( at level 10
           , ρ at level 0
           , e at level 0
           , Q at level 0
           , format "'[hv  ' ::wpPR  '/' '[hv' ρ  '/' e ']'  '/' Q ']'"
           , only printing).
  Notation "'::wpOperand' ρ e Q"
        := (wp_operand _ ρ e Q)
           ( at level 10
           , ρ at level 0
           , e at level 0
           , Q at level 0
           , format "'[hv  ' ::wpOperand  '/' '[hv' ρ  '/' e ']'  '/' Q ']'"
           , only printing).
  Notation "'::wpX' ρ e Q"
        := (wp_xval _ ρ e Q)
           ( at level 10
           , ρ at level 0
           , e at level 0
           , Q at level 0
           , format "'[hv  ' ::wpX  '/' '[hv' ρ  '/' e ']'  '/' Q ']'"
           , only printing).
  Notation "'::wpGL' ρ e Q"
        := (wp_glval _ ρ e Q)
           ( at level 10
           , ρ at level 0
           , e at level 0
           , Q at level 0
           , format "'[hv  ' ::wpGL  '/' '[hv' ρ  '/' e ']'  '/' Q ']'"
           , only printing).
  Notation "'::wpGLₓ' ρ e Q"
        := (wp_discard _ ρ e Q)
           ( at level 10
           , ρ at level 0
           , e at level 0
           , Q at level 0
           , format "'[hv  ' ::wpGLₓ  '/' '[hv' ρ  '/' e ']'  '/' Q ']'"
           , only printing).
  (* NOTE (JH): There isn't anything great to print from [Func] since the name was erased *)
  Notation "'::wpFunc' Q"
        := (wp_func _ _ _ Q)
           ( at level 10
           , Q at level 0
           , format "'[hv  ' ::wpFunc  '/' Q ']'"
           , only printing).
  (* NOTE (JH): There isn't anything great to print from [Method] since the name was erased *)
  Notation "'::wpMethod' Q"
        := (wp_method _ _ _ Q)
           ( at level 10
           , Q at level 0
           , format "'[hv  ' ::wpMethod  '/' Q ']'"
           , only printing).
  (* NOTE (JH): There isn't anything great to print from [Ctor] since the name is erased *)
  Notation "'::wpCtor' Q"
        := (wp_ctor _ _ _ Q)
           ( at level 10
           , Q at level 0
           , format "'[hv  ' ::wpCtor  '/' Q ']'"
           , only printing).
  (* NOTE (JH): There isn't anything great to print from [Dtor] since the name is erased *)
  Notation "'::wpDtor' Q"
        := (wp_dtor _ _ _ Q)
           ( at level 10
           , Q at level 0
           , format "'[hv  ' ::wpDtor  '/' Q ']'"
           , only printing).
  (* TODO (JH): print something more useful *)
  Notation "'::wpArgs' ρ Q"
        := (wp_args _ ρ _ _ Q)
           ( at level 10
           , ρ at level 0
           , Q at level 0
           , format "'[hv  ' ::wpArgs  '/' ρ   '/' Q ']'"
           , only printing).
  Notation "'::wpInitialize' ρ ( p '|->' 'type_ptrR' ty ) e Q"
        := (wp_initialize _ ρ ty%cpp_type p e Q)
           ( at level 10
           , e at level 0
           , Q at level 0
           , ty custom CPP_type at level 200
           , format "'[hv  ' ::wpInitialize  '/' ρ  '/' '[hv   ' ( p  |->  '/' type_ptrR  ty ) ']'  '/' e  '/' Q ']'"
           , only printing).
  Notation "'::wpCond' ρ ( T ) Q"
        := (wp_cond _ ρ (T:=T) Q)
           ( at level 10
           , ρ at level 0
           , Q at level 0
           , format "'[hv  ' ::wpCond  '/' ρ  '/' '[' ( T ) ']'  '/' Q ']'"
           , only printing).
  (* TODO (JH): print something more useful *)
  Notation "'::wpCall' ρ Q"
        := (wp_call _ ρ _ _ _ Q)
           ( at level 10
           , ρ at level 0
           , Q at level 0
           , format "'[hv  ' ::wpCall  '/' ρ  '/' Q ']'"
           , only printing).
  (* TODO (JH): print something more useful *)
  Notation "'::wpMCall' ρ Q"
        := (wp_mcall _ ρ _ _ _ _ _ Q)
           ( at level 10
           , ρ at level 0
           , Q at level 0
           , format "'[hv  ' ::wpMCall  '/' ρ  '/' Q ']'"
           , only printing).
End Verbose.
