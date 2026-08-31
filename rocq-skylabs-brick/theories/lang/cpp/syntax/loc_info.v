(*
 * Copyright (c) 2024-2025 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import skylabs.lang.cpp.syntax.prelude.
Require Import skylabs.lang.cpp.syntax.core.

Module LocInfo.
  (** Remove only leading location-information wrappers. Unlike the recursive
      [erase_*] functions below, these functions do not traverse the whole AST. *)
  Fixpoint drop_atomic_name (an : atomic_name) : atomic_name :=
    match an with
    | ANLocInfo _ an => drop_atomic_name an
    | _ => an
    end.

  Fixpoint drop_name (n : name) : name :=
    match n with
    | NLocInfo _ n => drop_name n
    | _ => n
    end.

  Fixpoint drop_temp_arg (arg : temp_arg) : temp_arg :=
    match arg with
    | ALocInfo _ arg => drop_temp_arg arg
    | _ => arg
    end.

  Fixpoint drop_expr (e : Expr) : Expr :=
    match e with
    | ELocInfo _ e => drop_expr e
    | _ => e
    end.

  Fixpoint drop_stmt (s : Stmt) : Stmt :=
    match s with
    | SLocInfo _ s => drop_stmt s
    | _ => s
    end.

  Fixpoint drop_var_decl (d : VarDecl) : VarDecl :=
    match d with
    | DLocInfo _ d => drop_var_decl d
    | _ => d
    end.

  Fixpoint drop_binding_decl (d : BindingDecl) : BindingDecl :=
    match d with
    | BLocInfo _ d => drop_binding_decl d
    | _ => d
    end.

  #[global] Arguments drop_atomic_name !_ / : simpl nomatch, assert.
  #[global] Arguments drop_name !_ / : simpl nomatch, assert.
  #[global] Arguments drop_temp_arg !_ / : simpl nomatch, assert.
  #[global] Arguments drop_expr !_ / : simpl nomatch, assert.
  #[global] Arguments drop_stmt !_ / : simpl nomatch, assert.
  #[global] Arguments drop_var_decl !_ / : simpl nomatch, assert.
  #[global] Arguments drop_binding_decl !_ / : simpl nomatch, assert.

  Fixpoint erase_atomic_name (an : atomic_name) {struct an} : atomic_name :=
    match an with
    | Nid id => Nid id
    | Nfunction qs id ts => Nfunction qs id (List.map erase_type ts)
    | Nctor ts => Nctor (List.map erase_type ts)
    | Ndtor => Ndtor
    | Nop qs op ts => Nop qs op (List.map erase_type ts)
    | Nop_conv qs t => Nop_conv qs (erase_type t)
    | Nop_lit id ts => Nop_lit id (List.map erase_type ts)
    | Nanon n => Nanon n
    | Nanonymous => Nanonymous
    | Nfirst_decl id => Nfirst_decl id
    | Nfirst_child id => Nfirst_child id
    | Nunsupported_atomic msg => Nunsupported_atomic msg
    | ANLocInfo _ an => erase_atomic_name an
    end

  with erase_name (n : name) {struct n} : name :=
    match n with
    | Ninst n args => Ninst (erase_name n) (List.map erase_temp_arg args)
    | Nglobal an => Nglobal (erase_atomic_name an)
    | Ndependent t => Ndependent (erase_type t)
    | Nscoped n an => Nscoped (erase_name n) (erase_atomic_name an)
    | Nunsupported msg => Nunsupported msg
    | NLocInfo _ n => erase_name n
    end

  with erase_temp_arg (arg : temp_arg) {struct arg} : temp_arg :=
    match arg with
    | Atype t => Atype (erase_type t)
    | Avalue e => Avalue (erase_Expr e)
    | Apack args => Apack (List.map erase_temp_arg args)
    | Atemplate n => Atemplate (erase_name n)
    | Atemplate_param id => Atemplate_param id
    | Aunsupported msg => Aunsupported msg
    | ALocInfo _ arg => erase_temp_arg arg
    end

  with erase_type (t : type) {struct t} : type :=
    match t with
    | Tparam id => Tparam id
    | Tresult_param id => Tresult_param id
    | Tresult_global n => Tresult_global (erase_name n)
    | Tresult_unop op t => Tresult_unop op (erase_type t)
    | Tresult_binop op t1 t2 => Tresult_binop op (erase_type t1) (erase_type t2)
    | Tresult_call n ts => Tresult_call (erase_name n) (List.map erase_type ts)
    | Tresult_member_call n t ts =>
        Tresult_member_call (erase_name n) (erase_type t) (List.map erase_type ts)
    | Tresult_parenlist t ts => Tresult_parenlist (erase_type t) (List.map erase_type ts)
    | Tresult_member t n => Tresult_member (erase_type t) (erase_name n)
    | Tauto => Tauto
    | Tptr t => Tptr (erase_type t)
    | Tref t => Tref (erase_type t)
    | Trv_ref t => Trv_ref (erase_type t)
    | Tnum rank sign => Tnum rank sign
    | Tchar_ char => Tchar_ char
    | Tvoid => Tvoid
    | Tarray t n => Tarray (erase_type t) n
    | Tincomplete_array t => Tincomplete_array (erase_type t)
    | Tvariable_array t e => Tvariable_array (erase_type t) (erase_Expr e)
    | Tnamed n => Tnamed (erase_name n)
    | Tenum n => Tenum (erase_name n)
    | Tfunction ft =>
        Tfunction (@FunctionType _ ft.(ft_cc) ft.(ft_arity)
          (erase_type ft.(ft_return)) (List.map erase_type ft.(ft_params)))
    | Tbool => Tbool
    | Tmember_pointer class t => Tmember_pointer (erase_type class) (erase_type t)
    | Tfloat_ float => Tfloat_ float
    | Tqualified qualifiers t => Tqualified qualifiers (erase_type t)
    | Tnullptr => Tnullptr
    | Tarch size name => Tarch size name
    | Tdecltype e => Tdecltype (erase_Expr e)
    | Texprtype e => Texprtype (erase_Expr e)
    | Tunsupported msg => Tunsupported msg
    end

  with erase_Expr (e : Expr) {struct e} : Expr :=
    match e with
    | Eparam id => Eparam id
    | Eunresolved_global n => Eunresolved_global (erase_name n)
    | Eunresolved_sizeof_pack id t => Eunresolved_sizeof_pack id (erase_type t)
    | Eunresolved_unop op e => Eunresolved_unop op (erase_Expr e)
    | Eunresolved_binop op l r => Eunresolved_binop op (erase_Expr l) (erase_Expr r)
    | Eunresolved_call n args => Eunresolved_call (erase_name n) (List.map erase_Expr args)
    | Eunresolved_member_call n obj args =>
        Eunresolved_member_call (erase_name n) (erase_Expr obj) (List.map erase_Expr args)
    | Eunresolved_parenlist t args =>
        Eunresolved_parenlist (option_map erase_type t) (List.map erase_Expr args)
    | Eunresolved_initlist t args =>
        Eunresolved_initlist (option_map erase_type t) (List.map erase_Expr args)
    | Eunresolved_member e n => Eunresolved_member (erase_Expr e) (erase_name n)
    | Eunresolved_string_literal t => Eunresolved_string_literal (erase_type t)
    | Evar name t => Evar name (erase_type t)
    | Eenum_const n id => Eenum_const (erase_name n) id
    | Eglobal n t => Eglobal (erase_name n) (erase_type t)
    | Eglobal_member n t => Eglobal_member (erase_name n) (erase_type t)
    | Echar c t => Echar c (erase_type t)
    | Estring s t => Estring s (erase_type t)
    | Eint n t => Eint n (erase_type t)
    | Ebool b => Ebool b
    | Efloat ft value => Efloat ft value
    | Eunop op e t => Eunop op (erase_Expr e) (erase_type t)
    | Ebinop op e1 e2 t => Ebinop op (erase_Expr e1) (erase_Expr e2) (erase_type t)
    | Ederef e t => Ederef (erase_Expr e) (erase_type t)
    | Eaddrof e => Eaddrof (erase_Expr e)
    | Eassign e1 e2 t => Eassign (erase_Expr e1) (erase_Expr e2) (erase_type t)
    | Eassign_op op e1 e2 t => Eassign_op op (erase_Expr e1) (erase_Expr e2) (erase_type t)
    | Epreinc e t => Epreinc (erase_Expr e) (erase_type t)
    | Epostinc e t => Epostinc (erase_Expr e) (erase_type t)
    | Epredec e t => Epredec (erase_Expr e) (erase_type t)
    | Epostdec e t => Epostdec (erase_Expr e) (erase_type t)
    | Eseqand e1 e2 => Eseqand (erase_Expr e1) (erase_Expr e2)
    | Eseqor e1 e2 => Eseqor (erase_Expr e1) (erase_Expr e2)
    | Ecomma e1 e2 => Ecomma (erase_Expr e1) (erase_Expr e2)
    | Ecall f args => Ecall (erase_Expr f) (List.map erase_Expr args)
    | Eexplicit_cast style t e => Eexplicit_cast style (erase_type t) (erase_Expr e)
    | Ecast cast e => Ecast (erase_Cast cast) (erase_Expr e)
    | Emember arrow obj field mut t =>
        Emember arrow (erase_Expr obj) (erase_atomic_name field) mut (erase_type t)
    | Emember_ignore arrow obj result => Emember_ignore arrow (erase_Expr obj) (erase_Expr result)
    | Emember_call arrow method obj args =>
        Emember_call arrow
          (match method with
           | inl (name, dispatch, t) => inl (erase_name name, dispatch, erase_type t)
           | inr e => inr (erase_Expr e)
           end)
          (erase_Expr obj) (List.map erase_Expr args)
    | Eoperator_call op impl args =>
        Eoperator_call op
          (match impl with
           | operator_impl.Func name t =>
               operator_impl.Func (erase_name name) (erase_type t)
           | operator_impl.MFunc name dispatch t =>
               operator_impl.MFunc (erase_name name) dispatch (erase_type t)
           end)
          (List.map erase_Expr args)
    | Esubscript e1 e2 t => Esubscript (erase_Expr e1) (erase_Expr e2) (erase_type t)
    | Esizeof arg t =>
        Esizeof
          (match arg with
           | inl t => inl (erase_type t)
           | inr e => inr (erase_Expr e)
           end)
          (erase_type t)
    | Ealignof arg t =>
        Ealignof
          (match arg with
           | inl t => inl (erase_type t)
           | inr e => inr (erase_Expr e)
           end)
          (erase_type t)
    | Eoffsetof class field t => Eoffsetof (erase_type class) field (erase_type t)
    | Econstructor n args t =>
        Econstructor (erase_name n) (List.map erase_Expr args) (erase_type t)
    | Einherited_constructor n args t =>
        Einherited_constructor (erase_name n) args (erase_type t)
    | Elambda n captures => Elambda (erase_name n) (List.map erase_Expr captures)
    | Eimplicit e => Eimplicit (erase_Expr e)
    | Eimplicit_init t => Eimplicit_init (erase_type t)
    | Eif cond thn els t =>
        Eif (erase_Expr cond) (erase_Expr thn) (erase_Expr els) (erase_type t)
    | Eif2 n common cond thn els t =>
        Eif2 n (erase_Expr common) (erase_Expr cond) (erase_Expr thn) (erase_Expr els)
          (erase_type t)
    | Ethis t => Ethis (erase_type t)
    | Enull => Enull
    | Einitlist args default t =>
        Einitlist (List.map erase_Expr args) (option_map erase_Expr default) (erase_type t)
    | Einitlist_union field init t =>
        Einitlist_union (erase_atomic_name field) (option_map erase_Expr init) (erase_type t)
    | Enew new_fn args pass_align alloc_ty array_size init =>
        Enew (erase_name new_fn.1, erase_type new_fn.2) (List.map erase_Expr args) pass_align
          (erase_type alloc_ty) (option_map erase_Expr array_size) (option_map erase_Expr init)
    | Edelete is_array del_fn arg deleted_type =>
        Edelete is_array (erase_name del_fn) (erase_Expr arg) (erase_type deleted_type)
    | Eandclean e => Eandclean (erase_Expr e)
    | Ematerialize_temp e category => Ematerialize_temp (erase_Expr e) category
    | Eatomic op args t => Eatomic op (List.map erase_Expr args) (erase_type t)
    | Estmt stmt t => Estmt (erase_Stmt stmt) (erase_type t)
    | Eva_arg e t => Eva_arg (erase_Expr e) (erase_type t)
    | Epseudo_destructor is_arrow t e =>
        Epseudo_destructor is_arrow (erase_type t) (erase_Expr e)
    | Earrayloop_init name src level length init t =>
        Earrayloop_init name (erase_Expr src) level length (erase_Expr init) (erase_type t)
    | Earrayloop_index level t => Earrayloop_index level (erase_type t)
    | Eopaque_ref name t => Eopaque_ref name (erase_type t)
    | Eunsupported msg t => Eunsupported msg (erase_type t)
    | ELocInfo _ e => erase_Expr e
    end

  with erase_Stmt (stmt : Stmt) {struct stmt} : Stmt :=
    match stmt with
    | Sseq stmts => Sseq (List.map erase_Stmt stmts)
    | Sdecl decls => Sdecl (List.map erase_VarDecl decls)
    | Sif init decl test thn els =>
        Sif (option_map erase_Stmt init) (option_map erase_VarDecl decl)
          (erase_Expr test) (erase_Stmt thn) (erase_Stmt els)
    | Sif_consteval thn els => Sif_consteval (erase_Stmt thn) (erase_Stmt els)
    | Swhile decl test body =>
        Swhile (option_map erase_VarDecl decl) (erase_Expr test) (erase_Stmt body)
    | Sfor init guard increment body =>
        Sfor (option_map erase_Stmt init) (option_map erase_Expr guard)
          (option_map erase_Expr increment) (erase_Stmt body)
    | Sdo body test => Sdo (erase_Stmt body) (erase_Expr test)
    | Sswitch init decl test body =>
        Sswitch (option_map erase_Stmt init) (option_map erase_VarDecl decl)
          (erase_Expr test) (erase_Stmt body)
    | Scase branch => Scase branch
    | Sdefault => Sdefault
    | Sbreak => Sbreak
    | Scontinue => Scontinue
    | Sreturn result => Sreturn (option_map erase_Expr result)
    | Sexpr e => Sexpr (erase_Expr e)
    | Sattr attrs stmt => Sattr attrs (erase_Stmt stmt)
    | Sasm code volatile inputs outputs clobbers =>
        Sasm code volatile
          (List.map (fun '(name, e) => (name, erase_Expr e)) inputs)
          (List.map (fun '(name, e) => (name, erase_Expr e)) outputs)
          clobbers
    | Slabeled label stmt => Slabeled label (erase_Stmt stmt)
    | Sgoto label => Sgoto label
    | Sunsupported msg => Sunsupported msg
    | SLocInfo _ stmt => erase_Stmt stmt
    end

  with erase_VarDecl (decl : VarDecl) {struct decl} : VarDecl :=
    match decl with
    | Dvar name t init => Dvar name (erase_type t) (option_map erase_Expr init)
    | Ddecompose e anon bindings =>
        Ddecompose (erase_Expr e) anon (List.map erase_BindingDecl bindings)
    | Dinit thread_safe name t init =>
        Dinit thread_safe (erase_name name) (erase_type t) (option_map erase_Expr init)
    | DLocInfo _ decl => erase_VarDecl decl
    end

  with erase_BindingDecl (decl : BindingDecl) {struct decl} : BindingDecl :=
    match decl with
    | Bvar name t init => Bvar name (erase_type t) (erase_Expr init)
    | Bbind name t init => Bbind name (erase_type t) (erase_Expr init)
    | BLocInfo _ decl => erase_BindingDecl decl
    end

  with erase_Cast (cast : Cast) {struct cast} : Cast :=
    match cast with
    | Cdependent t => Cdependent (erase_type t)
    | Cbitcast t => Cbitcast (erase_type t)
    | Clvaluebitcast t => Clvaluebitcast (erase_type t)
    | Cl2r => Cl2r
    | Cl2r_bitcast t => Cl2r_bitcast (erase_type t)
    | Cnoop t => Cnoop (erase_type t)
    | Carray2ptr => Carray2ptr
    | Cfun2ptr => Cfun2ptr
    | Cint2ptr t => Cint2ptr (erase_type t)
    | Cptr2int t => Cptr2int (erase_type t)
    | Cptr2bool => Cptr2bool
    | Cintegral t => Cintegral (erase_type t)
    | Cint2bool => Cint2bool
    | Cfloat2bool => Cfloat2bool
    | Cfloat2int t => Cfloat2int (erase_type t)
    | Cint2float t => Cint2float (erase_type t)
    | Cfloat t => Cfloat (erase_type t)
    | Cnull2ptr t => Cnull2ptr (erase_type t)
    | Cnull2memberptr t => Cnull2memberptr (erase_type t)
    | Cbuiltin2fun t => Cbuiltin2fun (erase_type t)
    | C2void => C2void
    | Cctor t => Cctor (erase_type t)
    | Cuser => Cuser
    | Cdynamic t => Cdynamic (erase_type t)
    | Cderived2base path t => Cderived2base (List.map erase_type path) (erase_type t)
    | Cbase2derived path t => Cbase2derived (List.map erase_type path) (erase_type t)
    | Cunsupported msg t => Cunsupported msg (erase_type t)
    end.
End LocInfo.
