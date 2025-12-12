(*
 * Copyright (c) 2019-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bluerock.lang.cpp.syntax.prelude.
Require Import bluerock.lang.cpp.syntax.core.
Require Import bluerock.lang.cpp.syntax.notations.

#[local] Open Scope Z_scope.

Module Export TypeNotationsInterface.
  Declare Custom Entry CPP_type.

  Bind Scope cpp_type_scope with type.
  Bind Scope cpp_type_scope with type_qualifiers.

  (* Injection from [constr] in case we're printing a subterm we don't recognize *)
  Notation "'{?:' ty '}'"
      := ty
         ( in custom CPP_type at level 0
         , ty constr
         , format "'[hv' {?:  ty } ']'"
         , only printing).
  (* Injection into [constr] in case we're printing this at the top-level *)
  Notation "'{t:' ty '}'"
      := ty
         ( at level 200
         , ty custom CPP_type at level 200
         , format "'[hv' {t:  ty } ']'"
         , only printing)
    : cpp_type_scope.
End TypeNotationsInterface.

(* NOTE (JH): [tests/type_notation_tests.v] contains tests of parsing/printing notations
   as well as [Check]s whose output is compared against a reference file.
 *)

Module Export TypeNotations.
  (* [type_qualifiers] - leaf nodes get the highest priority *)
  Notation "'mut'" := QM (in custom CPP_type at level 0, only printing).
  Notation "'const'" := QC (in custom CPP_type at level 0, only printing).
  Notation "'volatile'" := QV (in custom CPP_type at level 0, only printing).
  Notation "'const' 'volatile'"
      := QCV
         ( in custom CPP_type at level 0
         , format "'[' const  volatile ']'"
         , only printing).

  (* [Tqualified] types *)
  Notation "'mut' ty"
      := (Tmut ty)
         ( in custom CPP_type at level 100
         , ty custom CPP_type at level 200
         , right associativity
         , format "'[' mut  ty ']'"
         , only printing).
  Notation "'const' ty"
      := (Tconst ty)
         ( in custom CPP_type at level 100
         , ty custom CPP_type at level 200
         , right associativity
         , format "'[' const  ty ']'"
         , only printing).
  Notation "'volatile' ty"
      := (Tvolatile ty)
         ( in custom CPP_type at level 100
         , ty custom CPP_type at level 200
         , right associativity
         , format "'[' volatile  ty ']'"
         , only printing).
  Notation "'const' 'volatile' ty"
      := (Tconst_volatile ty)
         ( in custom CPP_type at level 100
         , ty custom CPP_type at level 200
         , right associativity
         , format "'[' const  volatile  ty ']'"
         , only printing).

  (* [char_type.t] variants *)
  Notation "'char'" := Tchar (in custom CPP_type at level 0, only printing).
  Notation "'wchar'" := Twchar (in custom CPP_type at level 0, only printing).
  Notation "'char8'" := Tchar8 (in custom CPP_type at level 0, only printing).
  Notation "'char16'" := Tchar16 (in custom CPP_type at level 0, only printing).
  Notation "'char32'" := Tchar32 (in custom CPP_type at level 0, only printing).

  (* The rest of the [type]s *)
  Notation "'ptr<' ty '>'"
      := (Tptr ty)
         ( in custom CPP_type at level 100
         , ty custom CPP_type at level 200
         , left associativity
         , format "'[' ptr< ty > ']'"
         , only printing).
  Notation "'ref&<' ty '>'"
      := (Tref ty)
         ( in custom CPP_type at level 100
         , ty custom CPP_type at level 200
         , left associativity
         , format "'[' ref&< ty > ']'"
         , only printing).
  Notation "'ref&&<' ty '>'"
      := (Trv_ref ty)
         ( in custom CPP_type at level 100
         , ty custom CPP_type at level 200
         , left associativity
         , format "'[' ref&&< ty > ']'"
         , only printing).
  Notation "'void'" := Tvoid (in custom CPP_type at level 0, only printing).
  Notation "ty [ n ]"
      := (Tarray ty n%N)
         ( in custom CPP_type at level 80
         , ty custom CPP_type
         , n constr
         , format "'[' ty [ n ] ']'", only printing).
  Notation "nm" := (Tnamed nm%pstring) (in custom CPP_type at level 0, nm constr, only printing).
  Notation "'extern' cc '???()' '->' rty"
      := (Tfunction (@FunctionType _ cc Ar_Definite rty nil))
         ( in custom CPP_type at level 100
         , cc constr at level 0
         , rty custom CPP_type at level 200
         , format "'[' extern  cc  ???()  ->  rty ']'"
         , only printing).
  Notation "'extern' cc '???(' aty1 , .. , aty2 ')' '->' rty"
      := (Tfunction (@FunctionType _ cc Ar_Definite rty (cons aty1 .. (cons aty2 nil) ..)))
         ( in custom CPP_type at level 100
         , cc constr at level 0
         , rty custom CPP_type at level 200
         , aty1 custom CPP_type at level 200
         , aty2 custom CPP_type at level 200
         , format "'[' extern  cc  ???( '[hv' aty1 ,  '/' .. ,  '/' aty2 ']' )  ->  rty ']'"
         , only printing).
  Notation "'extern' cc '???()(...)' '->' rty"
      := (@Tfunction (@FunctionType _ cc Ar_Variadic rty nil))
         ( in custom CPP_type at level 100
         , cc constr at level 0
         , rty custom CPP_type at level 200
         , format "'[' extern  cc  ???()(...)  ->  rty ']'"
         , only printing).
  Notation "'extern' cc '???(' aty1 , .. , aty2 ')(...)' '->' rty"
      := (@Tfunction (@FunctionType _ cc Ar_Variadic rty (cons aty1 .. (cons aty2 nil) ..)))
         ( in custom CPP_type at level 100
         , cc constr at level 0
         , rty custom CPP_type at level 200
         , aty1 custom CPP_type at level 200
         , aty2 custom CPP_type at level 200
         , format "'[' extern  cc  ???( '[hv' aty1 ,  '/' .. ,  '/' aty2 ']' )(...)  ->  rty ']'"
         , only printing).
  Notation "'bool'" := Tbool (in custom CPP_type at level 0, only printing).
  Notation "'ptr[' nm ']<' ty '>'"
      := (Tmember_pointer nm ty)
         ( in custom CPP_type at level 100
         , nm constr
         , ty custom CPP_type
         , left associativity
         , format "'[' ptr[ nm ]< ty > ']'"
         , only printing).
  Notation "'{float:' sz '}'"
      := (Tfloat sz)
         ( in custom CPP_type at level 0
         , sz constr
         , format "'[hv' {float:  sz } ']'"
         , only printing).
  Notation "'(' qual ty ')'"
      := (Tqualified qual ty)
         ( in custom CPP_type at level 100
         , qual custom CPP_type at level 0
         , ty custom CPP_type at level 200
         , format "'[' ( qual  ty ) ']'"
         , only printing).
  Notation "'nullptr_t'" := Tnullptr (in custom CPP_type at level 0, only printing).
  Notation "'{arch:' nm '}'"
      := (Tarch None nm)
         ( in custom CPP_type at level 0
         , nm constr
         , format "'[hv' {arch:  nm } ']'"
         , only printing).
  Notation "'{arch:' nm ';' 'size:' sz '}'"
      := (Tarch (Some sz) nm)
         ( in custom CPP_type at level 0
         , sz constr
         , nm constr
         , format "'[hv' {arch:  nm ;  size:  sz } ']'"
         , only printing).
End TypeNotations.

(*
Module Export TypeNotationsParsing.
  (* [type_qualifiers] - leaf nodes get the highest priority *)
  Notation "'mut'" := QM (in custom CPP_type at level 0).
  Notation "'const'" := QC (in custom CPP_type at level 0).
  Notation "'volatile'" := QV (in custom CPP_type at level 0).
  Notation "'const' 'volatile'"
      := QCV
         ( in custom CPP_type at level 0
         , format "'[' const  volatile ']'").

  (* [Tqualified] types *)
  Notation "'mut' ty"
      := (Tmut ty)
         ( in custom CPP_type at level 100
         , ty custom CPP_type at level 200
         , right associativity
         , format "'[' mut  ty ']'").
  Notation "'const' ty"
      := (Tconst ty)
         ( in custom CPP_type at level 100
         , ty custom CPP_type at level 200
         , right associativity
         , format "'[' const  ty ']'").
  Notation "'volatile' ty"
      := (Tmut_volatile ty)
         ( in custom CPP_type at level 100
         , ty custom CPP_type at level 200
         , right associativity
         , format "'[' volatile  ty ']'").
  Notation "'const' 'volatile' ty"
      := (Tconst_volatile ty)
         ( in custom CPP_type at level 100
         , ty custom CPP_type at level 200
         , right associativity
         , format "'[' const  volatile  ty ']'").

  (* [Tnum] variants *)
  Notation "'int8'" := Tschar (in custom CPP_type at level 0).
  Notation "'uint8'" := Tuchar (in custom CPP_type at level 0).
  Notation "'int16'" := Tshort (in custom CPP_type at level 0).
  Notation "'uint16'" := Tushort (in custom CPP_type at level 0).
  Notation "'int32'" := Tint (in custom CPP_type at level 0).
  Notation "'uint32'" := Tuint (in custom CPP_type at level 0).
  Notation "'int64'" := Tlonglong (in custom CPP_type at level 0).
  Notation "'uint64'" := Tulonglong (in custom CPP_type at level 0).
  Notation "'int128'" := Tint128 (in custom CPP_type at level 0).
  Notation "'uint128'" := Tuint128 (in custom CPP_type at level 0).

  (* The rest of the [type]s *)
  Notation "'ptr<' ty '>'"
      := (Tptr ty)
         ( in custom CPP_type at level 100
         , ty custom CPP_type at level 200
         , left associativity
         , format "'[' ptr< ty > ']'").
  Notation "'ref&<' ty '>'"
      := (Tref ty)
         ( in custom CPP_type at level 100
         , ty custom CPP_type at level 200
         , left associativity
         , format "'[' ref&< ty > ']'").
  Notation "'ref&&<' ty '>'"
      := (Trv_ref ty)
         ( in custom CPP_type at level 100
         , ty custom CPP_type at level 200
         , left associativity
         , format "'[' ref&&< ty > ']'").
  Notation "'void'" := Tvoid (in custom CPP_type at level 0).
  Notation "ty [ n ]"
      := (Tarray ty n%N)
         ( in custom CPP_type at level 80
         , ty custom CPP_type
         , n constr
         , format "'[' ty [ n ] ']'").
  Notation "nm" := (Tnamed nm) (in custom CPP_type at level 0, nm constr).
  Notation "'extern' cc '???()' '->' rty"
      := (@Tfunction cc Ar_Definite rty nil)
         ( in custom CPP_type at level 100
         , cc constr at level 0
         , rty custom CPP_type at level 200
         , format "'[' extern  cc  ???()  ->  rty ']'").
  Notation "'extern' cc '???(' aty1 , .. , aty2 ')' '->' rty"
      := (@Tfunction cc Ar_Definite rty (cons aty1 .. (cons aty2 nil) ..))
         ( in custom CPP_type at level 100
         , cc constr at level 0
         , rty custom CPP_type at level 200
         , aty1 custom CPP_type at level 200
         , aty2 custom CPP_type at level 200
         , format "'[' extern  cc  ???( '[hv' aty1 ,  '/' .. ,  '/' aty2 ']' )  ->  rty ']'").
  Notation "'extern' cc '???()(...)' '->' rty"
      := (@Tfunction cc Ar_Variadic rty nil)
         ( in custom CPP_type at level 100
         , cc constr at level 0
         , rty custom CPP_type at level 200
         , format "'[' extern  cc  ???()(...)  ->  rty ']'").
  Notation "'extern' cc '???(' aty1 , .. , aty2 ')(...)' '->' rty"
      := (@Tfunction cc Ar_Variadic rty (cons aty1 .. (cons aty2 nil) ..))
         ( in custom CPP_type at level 100
         , cc constr at level 0
         , rty custom CPP_type at level 200
         , aty1 custom CPP_type at level 200
         , aty2 custom CPP_type at level 200
         , format "'[' extern  cc  ???( '[hv' aty1 ,  '/' .. ,  '/' aty2 ']' )(...)  ->  rty ']'").
  Notation "'bool'" := Tbool (in custom CPP_type at level 0).
  Notation "'ptr[' nm ']<' ty '>'"
      := (Tmember_pointer nm ty)
         ( in custom CPP_type at level 100
         , nm constr
         , ty custom CPP_type
         , left associativity
         , format "'[' ptr[ nm ]< ty > ']'").
  Notation "'float:{{' sz '}}'"
      := (Tfloat sz)
         ( in custom CPP_type at level 0
         , sz constr
         , format "'[hv' float:{{ sz }} ']'").
  Notation "'(' qual ty ')'"
      := (Tqualified qual ty)
         ( in custom CPP_type at level 100
         , qual custom CPP_type at level 0
         , ty custom CPP_type at level 200
         , format "'[' ( qual  ty ) ']'").
  Notation "'nullptr_t'" := Tnullptr (in custom CPP_type at level 0).
  Notation "'arch:{{' nm '}}'"
      := (Tarch None nm)
         ( in custom CPP_type at level 0
         , nm constr
         , format "'[hv' arch:{{ nm }} ']'").
  Notation "'arch:{{' nm ';' 'size:' sz '}}'"
      := (Tarch (Some sz) nm)
         ( in custom CPP_type at level 0
         , sz constr
         , nm constr
         , format "'[hv' arch:{{ nm ;  size:  sz }} ']'").
End TypeNotationsParsing.
*)
