(*
 * Copyright (c) 2023-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bluerock.lang.cpp.syntax.prelude.
Require Import bluerock.lang.cpp.syntax.core.
Require Import bluerock.lang.cpp.syntax.types.

#[local] Open Scope monad_scope.
#[local] Notation M := option.

Module decltype.

  (**
  [to_exprtype] decomposes a declaration type into a value category
  and expression type. This is delicate because xvalue references to
  function types induce lvalue expressions.

  [to_valcat] is similar, but keeps only the value category. Matching
  on [to_valcat t] is simpler than matching on [t] when [t] might be
  an xvalue reference to a function type.
  *)
  Definition to_exprtype (t : decltype) : ValCat * exprtype :=
    match drop_qualifiers t with
    | Tref u => (Lvalue, u)
    | Trv_ref u =>
      match drop_qualifiers u with
      | Tfunction _ as f =>
        (**
        Both "a function call or an overloaded operator expression,
        whose return type is rvalue reference to function" and "a cast
        expression to rvalue reference to function type" are lvalue
        expressions.

        This also applies to <<__builtin_va_arg>> (an extension).

        https://en.cppreference.com/w/cpp/language/value_category#lvalue
        https://www.eel.is/c++draft/expr.call#13
        https://www.eel.is/c++draft/expr.static.cast#1
        https://www.eel.is/c++draft/expr.reinterpret.cast#1
        https://www.eel.is/c++draft/expr.cast#1 (C-style casts)

        NOTE: We return the function type without qualifiers in light
        of "A function or reference type is always cv-unqualified."
        <https://www.eel.is/c++draft/basic.type.qualifier#1>
        *)
        (Lvalue, f)
      | _ => (Xvalue, u)
      end
    | _ => (Prvalue, t)	(** Promote sharing, rather than normalize qualifiers *)
    end.
  Definition to_valcat (t : decltype) : ValCat := (to_exprtype t).1.

  (**
  Compute a declaration type from a value category and expression
  type.

  Up to dropping qualifiers on reference and function types, this is
  intended to be a partial inverse of [to_exprtype].
  *)
  Definition of_exprtype (vc : ValCat) (t : exprtype) : decltype :=
    (**
    As [t : Mexprtype], we do not need [tref], [trv_ref].
    *)
    match vc with
    | Lvalue => Tref t
    | Xvalue => Trv_ref t
    | Prvalue => t
    end.

  Module internal.
  Section with_lang.
    (**
    The declaration type of an explicit cast to type [t] or a call to
    a function or overloaded operator returning type [t] or a
    [__builtin_va_arg] of type [t].
    *)
    Definition normalize (t : decltype) : decltype :=
      let p := to_exprtype t in
      of_exprtype p.1 p.2.

    (** Function return type *)
    Definition from_function_type (ft : function_type) : decltype :=
      normalize ft.(ft_return).
    Definition from_functype (t : functype) : M decltype :=
      match t with
      | Tfunction ft => mret $ from_function_type ft
      | _ => mfail
      end.

    Definition requireL (t : decltype) : M exprtype :=
      match drop_qualifiers t with
      | Tref t => mret t
      | _ => mfail
      end.

    Definition requireGL (t : decltype) : M exprtype :=
      match drop_qualifiers t with
      | Tref t => mret t
      | Trv_ref t => mret t
      | _ => mfail
      end.

    Section fixpoint.
      Context (of_expr : Expr -> M decltype).

      Definition of_cast (base : decltype) (c : Cast) : M decltype :=
        match c with
        | Cdependent t
        | Cbitcast t
        | Clvaluebitcast t => mret t
        | Cl2r => drop_qualifiers <$> requireGL base
        | Cl2r_bitcast t => mret t
        | Cnoop t => mret t
        | Carray2ptr =>
            let k cv base :=
              match base with
              | Tarray ty _
              | Tincomplete_array ty
              | Tvariable_array ty _ =>
                  mret $ Tptr $ tqualified cv ty
              | _ => mfail
              end
            in
            requireGL base >>= qual_norm k
        | Cfun2ptr => Tptr <$> requireL base
        | Cint2ptr t
        | Cptr2int t => mret t
        | Cptr2bool => mret Tbool
        | Cderived2base _ ty
        | Cbase2derived _ ty => mret ty
        | Cintegral t => mret t
        | Cint2bool => mret Tbool
        | Cfloat2int t
        | Cint2float t
        | Cfloat t
        | Cnull2ptr t
        | Cnull2memberptr t
        | Cbuiltin2fun t
        | Cctor t => mret t
        | C2void => mret Tvoid
        | Cuser => mret base
        | Cdynamic to => mret to
        | Cunsupported _ t => mret t
        end.

      Definition of_binop (op : BinOp) (l : Expr) (t : exprtype) : M decltype :=
        match op with
        | Bdotp =>
          (**
          The value category of [e1.*e2] is (i) that of [e1] (xvalue
          or lvalue) when [e2] points to a field and (ii) prvalue when
          [e2] points to a method.

          We need only address (i) here because when [e2] is a method,
          the result of [e1.*e2] must be immediately applied, and
          cpp2v emits [Emember_call] rather than [Ebinop] for indirect
          method calls.

          https://www.eel.is/c++draft/expr.mptr.oper#6
          *)
          let* lt := to_exprtype <$> of_expr l in
          match lt.1 with
          | Lvalue => mret $ tref QM t
          | Xvalue => mret $ trv_ref QM t
          | _ => mfail
          end
        | Bdotip => mret $ tref QM t	(* derived from [Bdotp] *)
        | _ => mret t
        end.

      Definition of_addrof (e : Expr) : M decltype :=
        let* t := of_expr e in
        let '(vc, et) := to_exprtype t in
        let* _ := guard (vc <> Prvalue) in
        mret $ Tptr et.

      Definition of_call (f : Expr) : M decltype :=
        let* '(_, t) := to_exprtype <$> of_expr f in
        match t with
        | Tptr ft => from_functype ft
        | _ => mfail
        end.

      Definition of_member (arrow : bool) (e : Expr) (mut : bool) (t : decltype) : M decltype :=
        let '(ref, et) := to_exprtype t in
        match ref with
        | Lvalue | Xvalue => mret $ Tref et
        | Prvalue =>
          let* '(lval, oty) :=
            let* et := to_exprtype <$> of_expr e in
            if arrow then
              match et.1 , et.2 with
              | Prvalue , Tptr t => mret (true, t)
              | _ , _ => mfail
              end
            else
              match et.1 with
              | Lvalue => mret (true, et.2)
              | Xvalue => mret (false, et.2)
              | _ => mfail
              end
          in
          let qual :=
            let '(ocv, _) := decompose_type oty in
            CV (if mut then false else q_const ocv) (q_volatile ocv)
          in
          let ty := tqualified qual et in
          mret $ if lval : bool then Tref ty else Trv_ref ty
        end.

      Definition of_member_call (f : MethodRef) : M decltype :=
        match f with
        | inl (_, _, ft) =>
            from_functype ft
        | inr e =>
            let* et := of_expr e in
            match et with
            | Tmember_pointer cls ft => from_functype ft
            | _ => mfail
            end
        end.

      Definition from_operator_impl (f : operator_impl) : M decltype :=
        from_functype $ operator_impl.functype f.

      Definition of_subscript (e1 e2 : Expr) (t : exprtype) : M decltype :=
        let* t1 := of_expr e1 in
        let* t2 := of_expr e2 in
        let arithmetic t := guard (Is_true $ is_arithmetic t) in
        match drop_qualifiers t1 , drop_qualifiers t2 with
        | Tref aty , other => const (tref QM) <$> arithmetic other <*> array_type aty
        | Trv_ref aty , other => const (trv_ref QM) <$> arithmetic other <*> array_type aty
        | Tptr ety , other => const (Tref ety) <$> arithmetic other
        | other , Tref aty => const (tref QM) <$> arithmetic other <*> array_type aty
        | other , Trv_ref aty => const (trv_ref QM) <$> arithmetic other <*> array_type aty
        | other , Tptr ety => const (Tref ety) <$> arithmetic other
        | _ , _ => mfail
        end.

      (**
      TODO: Does [Ematerialize_temp] ever have a value category other
      than [Xvalue]? In the preceeding definition of [of_binop] we
      seem to assume "no". If we are indeed making that assumption,
      and if that assumption is correct, we should simplify the AST.
      *)
      Definition of_materialize_temp (e : Expr) (vc : ValCat) : M decltype :=
        let* t := of_expr e in
        let t := drop_reference t in
        mret $ of_exprtype vc t.

      #[local] Notation traverse_list := mapM.

      Definition cast_result : decltype -> decltype :=
        qual_norm (fun cv t =>
          match t with
          | Tnamed _
          | Tarray _ _
          | Tincomplete_array _
          | Tvariable_array _ _
          | Tenum _ => tqualified cv t
          | _ => t
          end).

      Definition of_expr_body (e : Expr) : M decltype :=
        match e return M decltype with

        | Eparam X => mret $ Tresult_param X
        | Eunresolved_global on => mret $ Tresult_global on
        | Eunresolved_unop o e => Tresult_unop o <$> of_expr e
        | Eunresolved_binop o l r => Tresult_binop o <$> of_expr l <*> of_expr r
        | Eunresolved_call on es => Tresult_call on <$> traverse_list of_expr es
        | Eunresolved_member_call on obj es => Tresult_member_call on <$> of_expr obj <*> traverse_list of_expr es
        | Eunresolved_parenlist (Some t) es => Tresult_parenlist t <$> traverse_list of_expr es
        | Eunresolved_parenlist None _ => mfail
        | Eunresolved_member obj fld => Tresult_member <$> of_expr obj <*> mret fld

        | Evar _ t => mret $ tref QM t
        | Eenum_const n _ => mret $ Tenum n
        | Eglobal _ t => mret $ tref QM $ normalize_type t
        | Eglobal_member nm t =>
            match nm with
            | Nscoped cls _ => mret $ Tmember_pointer (Tnamed cls) t
            | _ => mfail
            end

        | Echar _ t => mret t
        | Estring chars t =>
            mret $ Tref $ Tarray (Tconst t) (1 + literal_string.lengthN chars)
        | Eint _ t => mret t
        | Ebool _ => mret Tbool
        | Eunop _ _ t => mret t
        | Ebinop op l _ t => of_binop op l t
        | Ederef _ t => mret $ Tref t
        | Eaddrof e => of_addrof e
        | Eassign _ _ t
        | Eassign_op _ _ _ t
        | Epreinc _ t => mret $ Tref t
        | Epostinc _ t => mret t
        | Epredec _ t => mret $ Tref t
        | Epostdec _ t => mret t
        | Eseqand _ _
        | Eseqor _ _ => mret Tbool
        | Ecomma _ e2 => of_expr e2
        | Ecall f _ => of_call f
        | Eexplicit_cast _ t e =>
            mret (cast_result t)
        | Ecast c e => of_expr e >>= fun t => of_cast t c
        | Emember arrow e _ mut t => of_member arrow e mut t
        | Emember_ignore arrow eobj e => of_expr e
        | Emember_call _ f _ _ => of_member_call f
        | Eoperator_call _ f _ => from_operator_impl f
        | Esubscript e1 e2 t => of_subscript e1 e2 t
        | Esizeof _ t
        | Ealignof _ t
        | Eoffsetof _ _ t
        | Econstructor _ _ t => mret t
        | Elambda n _ => mret $ Tnamed n
        | Eimplicit e => of_expr e
        | Eimplicit_init t =>
          (**
          "References cannot be value-initialized".

          https://en.cppreference.com/w/cpp/language/value_initialization
          *)
          mret t
        | Eif _ _ _ t
        | Eif2 _ _ _ _ _ t => mret t
        | Ethis t => mret t
        | Enull => mret Tnullptr
        | Einitlist _ _ t => mret t
        | Einitlist_union _ _ t => mret t
        | Enew _ _ _ aty _ _ => mret $ Tptr aty
        | Edelete _ _ _ _ => mret Tvoid
        | Eandclean e => of_expr e
        | Ematerialize_temp e vc => of_materialize_temp e vc
        | Eatomic _ _ t => mret t
        | Estmt _ t => mret t
        | Eva_arg _ t => mret $ normalize t
        | Epseudo_destructor _ _ _ => mret Tvoid
        | Earrayloop_init _ _ _ _ _ t
        | Earrayloop_index _ t => mret t
        | Eopaque_ref _ t
        | Eunsupported _ t => mret t
        end.
    End fixpoint.
  End with_lang.
  End internal.

  Fixpoint of_expr (e : Expr) : M decltype :=
    internal.of_expr_body of_expr e.

End decltype.

Module exprtype.

  Definition of_expr (e : Expr) : M (ValCat * exprtype) :=
    decltype.to_exprtype <$> decltype.of_expr e.

  Definition of_expr_drop (e : Expr) : M exprtype :=
    drop_reference <$> decltype.of_expr e.

  Definition of_expr_check (P : ValCat -> Prop) `{!∀ vc, Decision (P vc)}
      (e : Expr) : M exprtype :=
    of_expr e >>= fun p => guard (P p.1) ;; mret p.2.

End exprtype.

(**
Convenience functions
*)
Definition decltype_of_expr (e : Expr) : decltype :=
  default (Tunsupported "decltype_of_expr: cannot determine declaration type") $
  decltype.of_expr e.
Definition exprtype_of_expr (e : Expr) : ValCat * exprtype :=
  decltype.to_exprtype $ decltype_of_expr e.
Definition valcat_of (e : Expr) : ValCat := (exprtype_of_expr e).1.
Definition type_of (e : Expr) : exprtype := (exprtype_of_expr e).2.
