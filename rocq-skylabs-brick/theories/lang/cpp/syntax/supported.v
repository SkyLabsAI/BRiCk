(*
 * Copyright (c) 2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bluerock.prelude.base.
Require Import bluerock.lang.cpp.syntax.core.
Require Import bluerock.lang.cpp.syntax.translation_unit.
Require Import bluerock.lang.cpp.syntax.templates.

Module check.
Section with_monad.

  Definition M := list PrimString.string.
  Definition op : M -> M -> M := List.app.
  Definition OK : M := [].
  Definition FAIL (msg : PrimString.string) : M := msg :: nil.

  #[local] Infix "<+>" := op (at level 30).
  #[local] Notation opt f := (from_option f OK).
  #[local] Notation lst f xs := (List.concat (List.map f xs)).

  Definition atomic_name (type : type -> M) (an : atomic_name) : M :=
    match an with
    | Nid _ => OK
    | Nfunction _ _ ts => lst type ts
    | Nctor ts => lst type ts
    | Ndtor => OK
    | Nop _ _ ts => lst type ts
    | Nop_conv _ t => type t
    | Nop_lit _ ts => lst type ts
    | Nanon _
    | Nanonymous
    | Nfirst_decl _ | Nfirst_child _ => OK
    | Nunsupported_atomic msg => FAIL msg
    end.

  Section temp_arg.
    Context (name : name -> M) (type : type -> M) (expr : Expr -> M).
    Fixpoint temp_arg  (a : temp_arg) : M :=
      match a with
      | Atype t => type t
      | Avalue e => expr e
      | Apack xs => lst temp_arg xs
      | Atemplate n => name n
      | Aunsupported msg => FAIL msg
      end.
  End temp_arg.

  Section temp_param.
    Context (name : name -> M) (type : type -> M) (expr : Expr -> M).
    Definition temp_param  (a : temp_param) : M :=
      match a with
      | Ptype _ => OK
      | Pvalue _ t => type t
      | Punsupported msg => FAIL msg
      end.
  End temp_param.

  Fixpoint name (n : name) : M :=
    match n with
    | Ninst n ii => name n <+> lst (temp_arg name type expr) ii
    | Nglobal an => atomic_name type an
    | Nscoped n s => name n <+> atomic_name type s
    | Ndependent t => type t
    | Nunsupported msg => FAIL msg
    end

  with type (t : type) : M :=
    match t with
    | Tunsupported msg => FAIL msg
    | Tparam _
    | Tresult_param _ => OK
    | Tresult_global n => name n
    | Tresult_unop _ t => type t
    | Tresult_binop _ t1 t2 => type t1 <+> type t2
    | Tresult_call nm ts => name nm <+> lst type ts
    | Tresult_member_call nm t ts => name nm <+> type t <+> lst type ts
    | Tresult_parenlist t ts => type t <+> lst type ts
    | Tresult_member t _ => type t
    | Tauto => OK
    | Tptr t | Tref t | Trv_ref t | Tarray t _ | Tincomplete_array t => type t
    | Tnum _ _ | Tchar_ _ | Tvoid | Tbool | Tfloat_ _ | Tnullptr => OK
    | Tvariable_array t e => type t <+> expr e
    | Tfunction (FunctionType t ts) => type t <+> lst type ts
    | Tmember_pointer t1 t2 => type t1 <+> type t2
    | Tqualified _ t => type t
    | Tarch _ _ => OK
    | Tdecltype e | Texprtype e => expr e
    | Tnamed n | Tenum n => name n
    end

  with expr (e : Expr) : M :=
    match e with
    | Evar _ t => type t
    | Eenum_const n _ => name n
    | Eglobal n t | Eglobal_member n t => name n <+> type t
    | Echar _ t | Estring _ t | Eint _ t => type t
    | Ebool _ => OK
    | Eunop _ e t => expr e <+> type t
    | Ebinop _ e1 e2 t => expr e1 <+> type t
    | Ederef e t => expr e <+> type t
    | Eaddrof e => expr e
    | Esubscript e1 e2 t => expr e1 <+> expr e2 <+> type t
    | Esizeof et t
    | Ealignof et t =>
        match et with
        | inr e => expr e
        | inl t => type t
        end <+> type t
    | Eoffsetof t1 _ t2 => type t1 <+> type t2
    | Eassign e1 e2 t | Eassign_op _ e1 e2 t => expr e1 <+> expr e2 <+> type t
    | Epreinc e t | Epostinc e t | Epredec e t | Epostdec e t => expr e <+> type t
    | Eseqand e1 e2 | Eseqor e1 e2 | Ecomma e1 e2 => expr e1 <+> expr e2
    | Ecall e es => expr e <+> lst expr es
    | Eoperator_call _ _ es => lst expr es
    | Epseudo_destructor _ t e => type t <+> expr e
    | Einitlist es oe t => lst expr es <+> opt expr oe <+> type t
    | Einitlist_union _ oe t => opt expr oe <+> type t
    | Emember_call _ mr e es =>
        match mr with
        | inr e => expr e
        | inl _ => OK
        end <+> expr e <+> lst expr es
    | Enew (n, t) es _ t1 oe1 oe2 =>
        name n <+> type t <+> lst expr es <+> type t1 <+> opt expr oe1 <+> opt expr oe2
    | Edelete _ n e t => name n <+> expr e <+> type t
    | Eexplicit_cast _ t e => type t <+> expr e
    | Ecast c e => cast c <+> expr e
    | Emember _ e an _ t => expr e <+> atomic_name type an <+> type t
    | Estmt s t => stmt s <+> type t
    | Enull => OK
    | Eopaque_ref _ t => type t
    | Eva_arg e t => expr e <+> type t
    | Eatomic _ es t => lst expr es <+> type t
    | Eandclean e => expr e
    | Ematerialize_temp e _ => expr e
    | Ethis t => type t
    | Eif e1 e2 e3 t => expr e1 <+> expr e2 <+> expr e3 <+> type t
    | Eif2 _ e1 e2 e3 e4 t => expr e1 <+> expr e2 <+> expr e3 <+> expr e4 <+> type t
    | Elambda nm es => name nm <+> lst expr es
    | Econstructor nm es t => name nm <+> lst expr es <+> type t
    | Eimplicit e => expr e
    | Emember_ignore _ _ e => expr e
    | Eimplicit_init t => type t
    | Eparam _ => OK
    | Eunresolved_global n => name n
    | Eunresolved_unop _ e => expr e
    | Eunresolved_binop _ e1 e2 => expr e1 <+> expr e2
    | Eunresolved_call n es => name n <+> lst expr es
    | Eunresolved_member_call _ _ _
    | Eunresolved_parenlist _ _
    | Eunresolved_member _ _ => OK
    | Earrayloop_init _ e _ _ e2 t => expr e <+> expr e2 <+> type t
    | Earrayloop_index _ t => type t
    | Eunsupported msg t => FAIL msg
    end

  with stmt (s : Stmt) : M :=
    match s with
    | Sseq ss => lst stmt ss
    | Sdecl ds => lst var_decl ds
    | Sif ovd e s1 s2 => opt var_decl ovd <+> expr e <+> stmt s1 <+> stmt s2
    | Sif_consteval _ _ => FAIL "if consteval"
    | Swhile ovd e s => opt var_decl ovd <+> expr e <+> stmt s
    | Sdo s e => stmt s <+> expr e
    | Sfor os oe1 oe2 s =>
        opt stmt os <+> opt expr oe1 <+> opt expr oe2 <+> stmt s
    | Sswitch ovd e s => opt var_decl ovd <+> expr e <+> stmt s
    | Scase _ => OK
    | Sdefault | Sbreak | Scontinue => OK
    | Sreturn oe => opt expr oe
    | Sexpr e => expr e
    | Sasm _ _ lpe1 lpe2 _ => lst (expr ∘ snd) lpe1 <+> lst (expr ∘ snd) lpe2
    | Sattr _ s => stmt s
    | Slabeled _ s => stmt s
    | Sgoto _ => FAIL "goto"
    | Sunsupported msg => FAIL msg
    end

  with var_decl (v : VarDecl) : M :=
    match v with
    | Dvar _ t oe => type t <+> opt expr oe
    | Ddecompose e _ bds => expr e <+> lst binding_decl bds
    | Dinit _ n t None => name n <+> type t
    | Dinit _ n t (Some e) => name n <+> type t <+> expr e
    end

  with binding_decl (b : BindingDecl) : M :=
    match b with
    | Bvar _ t e => type t <+> expr e
    | Bbind _ t e => type t <+> expr e
    end

  with cast (c : Cast) : M :=
    match c with
    | Cdependent t | Cbitcast t | Clvaluebitcast t | Cnoop t | Cint2ptr t | Cptr2int t
    | Cintegral t
    | Cnull2ptr t | Cnull2memberptr t
    | Cbuiltin2fun t | Cctor t | Cdynamic t => type t
    | Cderived2base ts t | Cbase2derived ts t => lst type ts <+> type t
    | Cfloat _ | Cint2float _ | Cfloat2int _ => FAIL "float"
    | Cl2r_bitcast _ => FAIL "l2r_bitcast"
    | _ => OK
    end.

  Definition function_body (b : FunctionBody) : M :=
    match b with
    | Impl s => stmt s
    | Builtin _ => OK
    end.
  Definition or_default {T : Set} (f : T -> M) (o : OrDefault T) : M :=
    match o with
    | Defaulted => OK
    | UserDefined v => f v
    end.

  Definition classname : classname -> M := name.

  Definition obj_value (o : ObjValue) : M :=
    let params (ps : list (localname * core.type)) : M :=
      lst (type ∘ snd) ps
    in
    match o with
    | Ovar t ie => type t
    | Ofunction (Build_Func t args _ _ exc ob) =>
        type t <+> params args <+> opt function_body ob
        <+> if exc is exception_spec.Unknown
            then match ob with
                 | None => OK
                 | _ => FAIL "unknown exception spec"
                 end
            else OK
    | Omethod m =>
        type m.(m_return) <+> classname m.(m_class)
        <+> params m.(m_params)
        <+> opt (or_default stmt) m.(m_body)
        <+> if m.(m_exception) is exception_spec.Unknown
            then match m.(m_body) with
                 | None => OK
                 | _ => FAIL "unknown exception spec"
                 end
            else OK

    | Oconstructor c =>
        let check_body '(li, s) := lst (expr ∘ init_init) li <+> stmt s in
        classname c.(c_class) <+> params c.(c_params)
        <+> opt (or_default check_body) c.(c_body)
        <+> if c.(c_exception) is exception_spec.Unknown
            then match c.(c_body) with
                 | None => OK
                 | _ => FAIL "unknown exception spec"
                 end
            else OK

    | Odestructor d =>
        classname d.(d_class) <+> opt (or_default stmt) d.(d_body)
        <+> if d.(d_exception) is exception_spec.Unknown
            then match d.(d_body) with
                 | None => OK
                 | _ => FAIL "unknown exception spec"
                 end
            else OK

    end.

  Definition glob_decl (gd : GlobDecl) : M :=
    match gd with
    | Gunsupported msg => FAIL msg
    | _ => OK
    end.

  Definition translation_unit (tu : translation_unit) : M :=
    let symbol '(nm, obj) := obj_value obj in
    let gd '(nm, gd) := glob_decl gd in
    lst gd (namemap.NM.elements tu.(types)) <+>
    lst symbol (namemap.NM.elements tu.(symbols)).

  Definition template_unit (mtu : Mtranslation_unit) : M :=
    let symbol '(nm, t_obj) :=
      lst (temp_param type) t_obj.(template_params)
      <+> obj_value t_obj.(template_value)
    in
    let gd '(nm, t_gd) :=
      lst (temp_param type) t_gd.(template_params)
      <+> glob_decl t_gd.(template_value)
    in
    lst gd (namemap.NM.elements mtu.(mtypes)) <+>
    lst symbol (namemap.NM.elements mtu.(msymbols)).

End with_monad.
End check.
