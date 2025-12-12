(*
 * Copyright (c) 2024-2025 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bluerock.prelude.base.
Require Import bluerock.prelude.bytestring_core.
Require Import bluerock.prelude.bytestring.
Require Import bluerock.upoly.base.
Require Import bluerock.upoly.upoly.
Require Import bluerock.lang.cpp.syntax.core.
Require Import bluerock.lang.cpp.syntax.types.
Require Import bluerock.lang.cpp.syntax.pretty.

(* UPSTREAM? *)
Module showN.
  #[local] Open Scope pstring_scope.
  Definition showZ (z : Z) : PrimString.string :=
    (if bool_decide (z < 0)%Z then
      "-" ++ showN (Z.to_N $ Z.opp z)
    else showN $ Z.to_N z).
End showN.

(** Pretty printing of C++ names
    This printer is quite similar to the <pretty.v> printer, but this one is more
    restricted becuase it is important that this function is invertible by the parser
    in <parser.v>.
 *)
Section with_lang.
  Import UPoly.
  #[local] Open Scope pstring_scope.
  Fixpoint sepBy (sep : PrimString.string) (ls : list PrimString.string) : PrimString.string :=
    match ls with
    | nil => ""
    | l :: nil => l
    | l :: ls => l ++ sep ++ sepBy sep ls
    end.
  Definition parens (b : PrimString.string) : PrimString.string := "(" ++ b ++ ")".
  Definition angles (b : PrimString.string) : PrimString.string := "<" ++ b ++ ">".

  Definition prefix : PrimString.string -> PrimString.string -> PrimString.string := PrimString.cat.
  Definition postfix (a b : PrimString.string) : PrimString.string := PrimString.cat b a.

  Section atomic_name.
    Context {type Expr : Set} (printType : type -> option PrimString.string) (printExpr : Expr -> option PrimString.string).
    Variable top : option PrimString.string.

    #[local] Open Scope monad_scope.
    Definition printAN inst (an : atomic_name_ type) : option PrimString.string :=
      match an return option PrimString.string with
      | Nid id =>
          if bool_decide (id = "") then mfail else mret $ id ++ inst
      | Nfunction quals nm args =>
          let* args := traverse (F:=eta option) printType args in
          mret $ nm ++ inst ++ parens (sepBy ", " args) ++
                 pretty.with_space (pretty.printFQ quals)
      | Nctor args =>
          let* args := traverse (F:=eta option) printType args in
          match top with
          | None => mfail
          | Some cls => mret $ cls ++ inst ++ parens (sepBy ", " args)
          end
      | Ndtor =>
          match top with
          | None => mfail
          | Some cls => mret $ "~" ++ cls ++ "()"
          end
      | Nop q oo args =>
          let* args := traverse (F:=eta option) printType args in
          mret $ "operator" ++ printOO oo ++ inst ++ parens (sepBy ", " args) ++
            pretty.with_space (pretty.printFQ q)
      | Nop_conv q ty =>
          let* ty := printType ty in
          mret $ "operator " ++ ty ++ "()" ++ pretty.with_space (pretty.printFQ q)
      | Nop_lit i args =>
          let* args := traverse (F:=eta option) printType args in
          mret $ "operator """"_" ++ i ++ parens (sepBy ", " args)
      | Nanonymous =>
          if bool_decide (inst = "") then mret "(anon)" else None
      | Nanon n => mret $ "@" ++ showN n ++ inst
      | Nfirst_decl n => mret $ "@" ++ n ++ inst
      | Nfirst_child n => mret $ "." ++ n ++ inst
      | Nunsupported_atomic note => mfail
      end.
  End atomic_name.

  Fixpoint topName (nm : name) : option PrimString.string :=
    match nm with
    | Nglobal (Nid id) => Some id
    | Nscoped _ (Nid id) => Some id
    | Ninst nm _ => topName nm
    | _ => None
    end.

  Definition printUO (o : overloadable.RUnOp) : PrimString.string :=
    match o with
    | overloadable.Rpreinc => "(++_)"
    | overloadable.Rpostinc => "(_++)"
    | overloadable.Rpredec => "(--_)"
    | overloadable.Rpostdec => "(_--)"
    | overloadable.Rstar => "*"
    | overloadable.Rarrow => "->"
    | overloadable.Runop op =>
        match op with
        | Uminus => "-"
        | Uplus => "+"
        | Unot => "!"
        | Ubnot => "~"
        | Uunsupported n => n
        end
    end.

  Definition printBO (o : overloadable.RBinOp) : option PrimString.string :=
    let printBO o :=
      match o with
      | Badd => mret "+"
      | Band => mret "&&"
      | Bcmp => mret "<=>"
      | Bdiv => mret "/"
      | Beq => mret "=="
      | Bge => mret ">="
      | Bgt => mret ">"
      | Ble => mret "<="
      | Blt => mret "<"
      | Bmul => mret "*"
      | Bneq => mret "!="
      | Bor => mret "||"
      | Bmod => mret "%"
      | Bshl => mret "<<"
      | Bshr => mret ">>"
      | Bsub => mret "-"
      | Bxor => mret "^"
      | Bdotp => mret ".*"
      | Bdotip => mret "->*"
      | Bunsupported b => mfail
      end
    in
    match o with
    | overloadable.Rbinop b => printBO b
    | overloadable.Rassign => mret "="
    | overloadable.Rassign_op b => (fun a => a ++ "=") <$> printBO b
    | overloadable.Rsubscript => mret "[]"
    end.

  Fixpoint printN (inst : PrimString.string) (nm : name) : option PrimString.string :=
    match nm with
    | Nglobal an => printAN printT None inst an
    | Ndependent an => (fun b => "typename " ++ b) <$> printT an
    | Nscoped base n =>
        (fun b n => b ++ "::" ++ n) <$> printN "" base <*> printAN printT (topName base) inst n
    | Ninst base i =>
        let fix printTA ta :=
          match ta with
          | Atype t => printT t
          | Avalue e => printE e
          | Apack ts =>
              ((fun tas => "..." ++ (angles $ sepBy ", " tas)) <$> traverse printTA ts)
          | Atemplate nm =>
              (fun b => "template " ++ b) <$> printN "" nm
          | Aunsupported note => mfail
          end
        in
        ((fun tas => angles $ sepBy ", " tas) <$> traverse printTA i) ≫= fun tas =>
        printN tas base
    | Nunsupported note => mfail
    end

  with printT (ty : type) : option PrimString.string :=
    match ty with
    | Tint => mret "int"
    | Tuint => mret "unsigned int"
    | Tchar => mret "char"
    | Tuchar => mret "unsigned char"
    | Tschar => mret "signed char"
    | Tshort => mret "short"
    | Tushort => mret "unsigned short"
    | Tlong => mret "long"
    | Tulong => mret "unsigned long"
    | Tlonglong => mret "long long"
    | Tulonglong => mret "unsigned long long"
    | Tnum int_rank.I128 Signed => mret "int128_t"
    | Tnum int_rank.I128 Unsigned => mret "uint128_t"
    | Twchar => mret "wchar_t"
    | Tchar8 => mret "char8_t"
    | Tchar16 => mret "char16_t"
    | Tchar32 => mret "char32_t"
    | Tfloat => mret "float"
    | Tfloat16 => mret "float16"
    | Tfloat128 => mret "float128"
    | Tdouble => mret "double"
    | Tlongdouble => mret "long double"
    | Tbool => mret "bool"
    | Tnullptr => mret "nullptr_t"
    | Tptr (Tfunction (@FunctionType _ cc ar ret args)) =>
        if cc is CC_C then
          let add_dots (ls : list PrimString.string) :=
            match ar with
            | Ar_Variadic => (ls ++ ["..."])%list
            | _ => ls
            end
          in
          (fun ret args => ret ++ "(*)(" ++ sepBy "," (add_dots args) ++ ")")
            <$> printT ret <*> traverse printT args
        else mfail
    | Tptr t => postfix "*" <$> printT t
    | Tref t =>
        match t with
        | Tref _ | Trv_ref _ => postfix " &" <$> printT t
        | _ => postfix "&" <$> printT t
        end
    | Trv_ref t =>
        match t with
        | Tref _ | Trv_ref _ => postfix " &&" <$> printT t
        | _ => postfix "&&" <$> printT t
        end
    | Tmember_pointer cls t => (fun t c => t ++ " " ++ c ++ "::*") <$> printT t <*> printT cls
    | Tqualified QM _ => mfail
    | Tqualified _q (Tqualified _ _) => mfail
       (* ^^ we reject sequences of [Tqualified] because it is not invertible *)
    | Tqualified cv t =>
        let q_ls := ((if q_const cv then ["const"] else []) ++
                    (if q_volatile cv then ["volatile"] else []))%list in
        match t with
        | Tptr _ | Tref _ | Trv_ref _ => fun t => sepBy " " $ t :: q_ls
        | _ => fun t => sepBy " " $ q_ls ++ [t]
        end%list <$> printT t
    | Tvoid => mret "void"
    | Tarray t n => (fun t => t ++ "[" ++ showN n ++ "]") <$> printT t
    | Tincomplete_array t => postfix "[]" <$> printT t
    | Tvariable_array t e => (fun t n => t ++ "[" ++ n ++ "]") <$> printT t <*> printE e
    | Tdecltype e => (fun e => "decltype((" ++ e ++ "))") <$> printE e
    | Texprtype e => (fun e => "decltype(" ++ e ++ ")") <$> printE e
    | Tnamed nm => printN "" nm
    | Tenum nm => prefix "enum " <$> printN "" nm
    | Tfunction ft =>
        let add_dots (ls : list PrimString.string) :=
          match ft.(ft_arity) with
          | Ar_Variadic => (ls ++ ["..."])%list
          | _ => ls
          end
        in
        if ft.(ft_cc) is CC_C then
          (fun t tas => t ++ parens (sepBy ", " $ add_dots tas))
            <$> printT ft.(ft_return)
            <*> traverse (T:=eta list) (F:=eta option) printT ft.(ft_params)
        else mfail
    | Tarch _ note => mfail
    | Tunsupported note => mfail
    | Tparam nm => mret $ "$" ++ nm
    | _ => mfail
    end

  with printE (e : Expr) : option PrimString.string :=
    match e with
    | Eglobal nm _ =>
      (* We can not support this in an invertible manner because of the type. *)
      mfail
    | Eint z ty => (fun suffix => showN.showZ z ++ suffix) <$>
        match ty with
        | Tint => mret ""
        | Tuint => mret "u"
        | Tlong => mret "l"
        | Tulong => mret "ul"
        | Tlonglong => mret "ll"
        | Tulonglong => mret "ull"
        | Tbool => mret "b"
        | _ => mfail
        end
    | Ebool b => mret $ if b then "true" else "false"
    | Enull => mret "nullptr"
    | Eparam b => mret $ "`" ++ b
    | _ => mfail
    end.

End with_lang.

Definition print_name (input : name) : option PrimString.string :=
  printN "" input.

Definition print_type (input : type) : option PrimString.string :=
  printT input.

Module Type TESTS.
  #[local] Definition TEST (input : PrimString.string) (nm : name) : Prop :=
    print_name nm = Some input.

  #[local] Definition Msg : name := Nglobal $ Nid "Msg".

  Succeed Example _0 : TEST "Msg" Msg := eq_refl.
  Succeed Example _0 : TEST "Msg::@0" (Nscoped Msg (Nanon 0)) := eq_refl.
  Succeed Example _0 : TEST "Msg::Msg()" (Nscoped Msg (Nctor [])) := eq_refl.
  Succeed Example _0 : TEST "Msg::~Msg()" (Nscoped Msg Ndtor) := eq_refl.

  Succeed Example _0 : TEST "Msg::Msg(int& &)" (Nscoped Msg (Nctor [Tref (Tref Tint)])) := eq_refl.
  Succeed Example _0 : TEST "Msg::Msg(int&& &)" (Nscoped Msg (Nctor [Tref (Trv_ref Tint)])) := eq_refl.
  Succeed Example _0 : TEST "Msg::Msg(int& &&)" (Nscoped Msg (Nctor [Trv_ref (Tref Tint)])) := eq_refl.
  Succeed Example _0 : TEST "Msg::Msg(int&& &&)" (Nscoped Msg (Nctor [Trv_ref (Trv_ref Tint)])) := eq_refl.


  Succeed Example _0 :
    let targs := Avalue <$> [Eint 1 Tulong;
                             Eint (-2) Tlong;
                             Eint 3 Tulonglong;
                             Eint (-4) Tlonglong;
                             Eint 5 Tuint;
                             Eint 6 Tint] in
    TEST "Msg<1ul, -2l, 3ull, -4ll, 5u, 6>::Msg()" (Nscoped (Ninst Msg targs) (Nctor [])) := eq_refl.
  Succeed Example _0 :
    let targs := Atype <$> [Tulong;
                            Tlong;
                            Tulonglong;
                            Tlonglong;
                            Tuint; Tint] in
    TEST "Msg<unsigned long, long, unsigned long long, long long, unsigned int, int>::Msg()" (Nscoped (Ninst Msg targs) (Nctor [])) := eq_refl.
  Succeed Example _0 : TEST "Msg::Msg(int)" (Nscoped Msg (Nctor [Tint])) := eq_refl.
  Succeed Example _0 : TEST "Msg::Msg(long)" (Nscoped Msg (Nctor [Tlong])) := eq_refl.
  Succeed Example _0 : TEST "Msg::operator=(const Msg&)" (Nscoped Msg (Nop function_qualifiers.N OOEqual [Tref (Tconst (Tnamed $ Nglobal (Nid "Msg")))])) := eq_refl.
  Succeed Example _0 : TEST "Msg::operator=(const Msg&&)" (Nscoped Msg (Nop function_qualifiers.N OOEqual [Trv_ref (Tconst (Tnamed $ Nglobal (Nid "Msg")))])) := eq_refl.
  Succeed Example _0 : TEST "Msg::operator new()" (Nscoped Msg (Nop function_qualifiers.N (OONew false) [])) := eq_refl.
  Succeed Example _0 : TEST "Msg::operator new[]()" (Nscoped Msg (Nop function_qualifiers.N (OONew true) [])) := eq_refl.
  Succeed Example _0 : TEST "Msg::operator delete[]()" (Nscoped Msg (Nop function_qualifiers.N (OODelete true) [])) := eq_refl.
  Succeed Example _0 : TEST "Msg::operator int()" (Nscoped Msg (Nop_conv function_qualifiers.N Tint)) := eq_refl.
  Succeed Example _0 : TEST "foo_client(int[2]&, const int*, bool*, int**, char*)" (Nglobal (Nfunction function_qualifiers.N "foo_client" [Tref (Tarray Tint 2); Tptr (Tconst Tint); Tptr Tbool; Tptr (Tptr Tint); Tptr Tchar])) := eq_refl.
  Succeed Example _0 : TEST "DlistInternal::iterator::operator!=(const DlistInternal::iterator&) const"
                 (Nscoped (Nscoped (Nglobal (Nid "DlistInternal")) (Nid "iterator"))
                    (Nop function_qualifiers.Nc OOExclaimEqual [Tref (Tqualified QC (Tnamed (Nscoped (Nglobal (Nid "DlistInternal")) (Nid "iterator"))))])) := eq_refl.
  Succeed Example _0 : TEST "intrusive::List_internal::iterator::iterator(intrusive::List_internal::Node*)"
                 (Nscoped (Nscoped (Nscoped (Nglobal (Nid "intrusive")) (Nid "List_internal")) (Nid "iterator"))
                    (Nctor [Tptr (Tnamed (Nscoped (Nscoped (Nglobal (Nid "intrusive")) (Nid "List_internal")) (Nid "Node")))])) := eq_refl.
  Succeed Example _0 : TEST "span<const int, 1ull>::span(const int*, unsigned long)"
                         (Nscoped (Ninst (Nglobal (Nid "span")) [Atype (Tqualified QC Tint);
                                                                 Avalue (Eint 1 Tulonglong)])
                            (Nctor [Tptr (Tqualified QC Tint); Tulong])) := eq_refl.
  Succeed Example _0 : TEST "integral" (Nglobal $ Nid "integral") := eq_refl.
  Succeed Example _0 : TEST "f<int>(int, int)" (Ninst (Nglobal $ Nfunction function_qualifiers.N "f" [Tint; Tint]) [Atype Tint]) := eq_refl.
  Succeed Example _0 : TEST "f<int>(enum @1, enum en)" (Ninst (Nglobal $ Nfunction function_qualifiers.N "f" [Tenum (Nglobal (Nanon 1)); Tenum (Nglobal (Nid "en"))]) [Atype Tint]) := eq_refl.
  Succeed Example _0 : TEST "f<int>(int(*)())" (Ninst (Nglobal $ Nfunction function_qualifiers.N "f" [Tptr (Tfunction (FunctionType Tint []))]) [Atype Tint]) := eq_refl.
  Succeed Example _0 : TEST "f<int>(int())" (Ninst (Nglobal $ Nfunction function_qualifiers.N "f" [Tfunction (FunctionType Tint [])]) [Atype Tint]) := eq_refl.
  Succeed Example _0 : TEST "f<int>(int(int))" (Ninst (Nglobal $ Nfunction function_qualifiers.N "f" [Tfunction (FunctionType Tint [Tint])]) [Atype Tint]) := eq_refl.

  Succeed Example _0 : TEST "C<1b, 0b>" (Ninst (Nglobal (Nid "C")) [Avalue (Eint 1 Tbool); Avalue (Eint 0 Tbool)]) := eq_refl.
  Succeed Example _0 : TEST "C<1, 0>" (Ninst (Nglobal (Nid "C")) [Avalue (Eint 1 Tint); Avalue (Eint 0 Tint)]) := eq_refl.
  Succeed Example _0 : TEST "C<1, ...<int, long>>" (Ninst (Nglobal (Nid "C")) [Avalue (Eint 1 Tint); Apack [Atype Tint; Atype Tlong]]) := eq_refl.

End TESTS.
