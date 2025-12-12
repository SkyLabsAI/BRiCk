(*
 * Copyright (c) 2023-2025 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bluerock.lang.cpp.syntax.prelude.
Require Import bluerock.lang.cpp.syntax.core.
Require Import bluerock.lang.cpp.syntax.types.
Require Import bluerock.lang.cpp.syntax.typing.
Require Import bluerock.lang.cpp.syntax.stmt.
Require Import bluerock.lang.cpp.syntax.namemap.
Require Import bluerock.lang.cpp.syntax.translation_unit.
Import UPoly.

#[local] Open Scope monad_scope.

(* TODO: a little "sloppy" with the errors *)
mlock Definition breadcrumb {t : Set} (_ : t) : Error.t := inhabitant.
mlock Definition Bad_allocation_function_args (_ : list type) : Error.t := inhabitant.
mlock Definition Can_initialize (dt it : decltype) : Error.t := inhabitant.

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
    Record ext_tu : Set :=
    { ext_symbols : name -> option decltype
    ; ext_types : name -> option GlobDecl }.

    #[local] Definition M : Set -> Type :=
      readerT.M (ext_tu * decltype * option exprtype * list (localname * decltype)) (trace.M Error.t).
    #[local] Instance M_Ret : MRet M := _.
    #[local] Instance M_Ap : Ap M := _.
    #[local] Instance M_Bind : MBind M := _.
    #[local] Instance M_Fail : MFail M := _.
    #[local] Instance M_Throw : Trace Error.t M := _.
    #[local] Hint Opaque M : typeclass_instances.

    Definition trace {T : Set} {U} (v : T) (m : M U) : M U :=
      trace (breadcrumb v) m.
    Definition throw {T : Set} {U} (v : T) : M U :=
      trace v mfail.

    Definition type_of_global (n : name) : M decltype :=
      let* osym := readerT.asks (fun '(tu, _, _, _) => tu.(ext_symbols) n) in
      match osym with
      | Some sym => mret sym
      | None => throw ("failed to find global "%bs, n)
      end.

    Definition global (n : name) : M GlobDecl :=
      let* osym := readerT.asks (fun '(tu, _, _, _) => tu.(ext_types) n) in
      match osym with
      | Some gd => mret gd
      | None => throw ("failed to find global "%bs, n)
      end.

    Definition type_of_constant (n : name) (id : ident) : M decltype :=
      let* osym := readerT.asks (fun '(tu, _, _, _) => tu.(ext_types) $ Nscoped n (Nid id)) in
      match osym with
      | Some (Gconstant ty _) => mret ty
      | Some ty => throw ("global symbol "%bs, Nscoped n (Nid id), " was not a constant "%bs, ty)
      | None => throw ("failed to find global "%bs, Nscoped n (Nid id))
      end.

    Definition ask_return : M decltype :=
      readerT.asks (fun '(_, a,_,_) => a).
    Definition ask_this : M exprtype :=
      let* rt := readerT.asks (fun '(_,this,_) => this) in
      match rt with
      | None => mfail
      | Some ty => mret ty
      end.
    Definition of_option {T : Set} (o : option T) : M T :=
      match o with
      | None => mfail
      | Some v => mret v
      end.

    (* Bindings *)
    Record bindings : Set := { _bindings : list (localname * decltype) }.
    Instance bindings_empty : Empty bindings := {| _bindings := nil |}.
    Definition with_var {T} (x : localname) (t : decltype) : M T -> M T :=
      readerT.local (fun '(ret, this, vars) => (ret, this, (x,t) :: vars)).
    Definition with_bindings {T} (b : bindings) (m : M T) : M T :=
      fold_right (fun xt => with_var xt.1 xt.2) m b.(_bindings).
    #[local] Instance bindings_monoid : monoid.Monoid bindings :=
      {| monoid.monoid_unit := bindings_empty
       ; monoid.monoid_op a b := {| _bindings := a.(_bindings) ++ b.(_bindings) |} |}.

    Definition var_type (n : localname) : M decltype :=
      let* vars := readerT.asks (fun '(_,_,vars) => vars) in
      match List.find (fun x => bool_decide (x.1 = n)) vars with
      | None => throw ("failed to find variable "%bs, n, " in "%bs, vars)
      | Some t => mret t.2
      end.

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
    Definition require_functype (t : decltype) : M function_type :=
      match t with
      | Tfunction ft => mret ft
      | _ => mfail
      end.
    Definition require_mfunctype (t : decltype) : M (decltype * function_type) :=
      match t with
      | Tmember_pointer nm ft => pair nm <$> require_functype ft
      | _ => mfail
      end.

    Section fixpoint.
      Context (of_expr : Expr -> M decltype).
      Context (of_stmt : Stmt -> M (option decltype)).

      Definition of_unop (op : UnOp) (t : exprtype) : M decltype :=
        match op with
        | Uminus | Uplus =>
          if is_arithmetic t then mret t else mfail (* TODO: check this *)
        | Unot => if is_arithmetic t then mret Tbool else mfail
        | Ubnot => if is_arithmetic t then mret t else mfail
        | Uunsupported _ => mfail
        end.

      Definition of_binop (op : BinOp) (l r : decltype) (t : exprtype) : M decltype :=
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
          match l with
          | Trv_ref _ => mret $ Trv_ref t
          | _ => mret $ Tref t
          end
        | Bdotip => mret $ Tref t	(* derived from [Bdotp] *)
        | _ => mret t
        end.

      Definition of_member (Et : bool * exprtype) (mut : bool) (t : decltype) : M decltype :=
        let '(ref, et) := to_exprtype t in
        match ref with
        | Lvalue | Xvalue => mret $ Tref et
        | Prvalue =>
          let oty := Et.2 in
          let qual :=
            let '(ocv, _) := decompose_type oty in
            CV (if mut then false else q_const ocv) (q_volatile ocv)
          in
          let ty := tqualified qual et in
          if Et.1 then mret $ Trv_ref ty else mret $ Tref ty
        end.

      Definition of_subscript (t1 t2 : decltype) (t : exprtype) : M decltype :=
        (* we need to handle arrays and pointers.
           Arrays can be lvalues or xvalues.
         *)
        let arithmetic t := guard (Is_true $ is_arithmetic t) in
        match drop_qualifiers t1 , drop_qualifiers t2 with
        | Tref aty , other => const (tref QM) <$> arithmetic other <*> of_option (array_type aty)
        | Trv_ref aty , other => const (trv_ref QM) <$> arithmetic other <*> of_option (array_type aty)
        | Tptr ety , other => const (Tref ety) <$> arithmetic other
        | other , Tref aty => const (tref QM) <$> arithmetic other <*> of_option (array_type aty)
        | other , Trv_ref aty => const (trv_ref QM) <$> arithmetic other <*> of_option (array_type aty)
        | other , Tptr ety => const (Tref ety) <$> arithmetic other
        | _ , _ => mfail
        end.

      Definition requireL (t : decltype) : M exprtype :=
        match t with
        | Tref t => mret t
        | _ => mfail
        end.
      Definition requireGL_get (t : decltype) : M (bool * exprtype) :=
        match t with
        | Tref t => mret (false, t)
        | Trv_ref t => mret (true, t)
        | _ => mfail
        end.
      Definition requireGL (t : decltype) : M exprtype :=
        match t with
        | Tref t | Trv_ref t => mret t
        | _ => mfail
        end.
      Definition requirePR (t : decltype) : M exprtype :=
        match t with
        | Tref _ | Trv_ref _ => mfail
        | _ => mret t
        end.
      Definition requireR (t : decltype) : M exprtype :=
        match t with
        | Tref _ => mfail
        | _ => mret t
        end.
      Definition require_eq {T : Set} {_ : EqDecision T} (l : T) (r : T) : M unit :=
        trace ("require equal "%bs, l, " = "%bs, r) $
        const () <$> guard (l = r).

      (* determine if this type can be used in an <<if>> *)
      Definition require_testable (t : exprtype) : M unit :=
        match t with
        | Tnum _ _
        | Tptr _
        | Tbool
        | Tnullptr
        | Tchar_ _
        | Tfloat_ _ => mret ()
        | _ => mfail
        end.

      Definition require_ptr (t : decltype) : M exprtype :=
        match t with
        | Tptr t => mret t
        | _ => mfail
        end.

      Definition arrow_deref (arrow : bool) : decltype -> M exprtype :=
        if arrow then require_ptr else requireGL.
      Definition arrow_deref_get (arrow : bool) : decltype -> M (bool * exprtype) :=
        if arrow then fun t => pair false <$> require_ptr t else requireGL_get.

      Notation "a >=> b" := (a >>= b) (at level 61, left associativity).

      (* TODO upstream *)
      Definition is_const (t : exprtype) : bool :=
        qual_norm (fun cv _ => q_const cv) t.
      Definition is_volatile (t : exprtype) : bool :=
        qual_norm (fun cv _ => q_volatile cv) t.

      Definition qualifiers (t : type) : type_qualifiers :=
        qual_norm (fun cv _ => cv) t.

      Succeed Example _0 : bool_decide (tq_le QM QC) := I.
      (* END upstream *)

      Definition can_initialize (dt : decltype) (t : decltype) : M unit :=
        let ref_conv dt t :=
          qual_norm (fun dq dt => qual_norm (fun q t =>
                                    let* _ := guard (tq_le q dq) in
                                    let* _ := guard (dt = t) in
                                    mret ()
            ) t) dt
        in
        let ptr_conv dt t :=
              qual_norm (fun dq dt => qual_norm (fun q t =>
                                                let* _ := guard (tq_le q dq) in
                                                let* _ := guard (dt = t \/ dt = Tvoid) in
                                                mret ()
                                     ) t) dt
        in
        trace (Can_initialize dt t) $
          match drop_qualifiers dt , drop_qualifiers t with
          | Tref dt , Tref t
          | Trv_ref dt , Trv_ref t =>
              ref_conv dt t
          | Tref dt , Trv_ref t =>
              if is_const dt
              then ref_conv dt t
              else mfail
          | Tptr dt , Tptr t =>
              ptr_conv dt t
          | dt , t =>
              let* _ := guard (dt = t) in mret ()
          end.

      Fixpoint check_args (ar : function_arity) (ts : list decltype) (tes : list decltype) : M unit :=
        match ts , tes with
        | nil , nil => mret ()
        | t :: ts , te :: tes =>
            (* toplevel qualifiers on arguments are ignored *)
            let* _ := can_initialize t te in
            check_args ar ts tes
        | nil , te :: tes =>
            match ar with
            | Ar_Variadic => mret () (* TODO: should check that all arguments can be passed as variadic arguments *)
            | _ => mfail
            end
        | _ , _ => mfail
        end.

      Definition gl_or_ptr (t : decltype) : M (ValCat * exprtype) :=
        match t with
        | Tptr t => mret (Prvalue, t)
        | Tref t => mret (Lvalue, t)
        | Trv_ref t => mret (Xvalue, t)
        | _ => mfail
        end.

      Definition vc_to_type (vc : ValCat) : exprtype -> decltype :=
        match vc with
        | Prvalue => Tptr
        | Lvalue => Tref
        | Xvalue => Trv_ref
        end.

      Fixpoint check_list' (from : name) (ts : list exprtype) (result : name) : M () :=
        let* (gd : GlobDecl) := global from in
        match gd with
        | Gstruct st =>
            let check nm :=
              List.existsb (fun '(b, _) => bool_decide (type_of_classname b = Tnamed nm)) st.(s_bases)
            in
            match ts with
            | nil =>
                if check result then
                  mret tt
                else
                  throw ("invalid base class "%bs, from, result)
            | Tnamed next :: ts =>
                if check next then
                  check_list' next ts result
                else
                  throw ("invalid base class "%bs, from, result)
            | t :: _ =>
                throw ("invalid class in chain "%bs, t)

            end
        | _ =>
            throw ("not a class "%bs, from)
        end.
      Definition check_list (from : exprtype) (ts : list exprtype) (result : exprtype) : M () :=
        match drop_qualifiers from , drop_qualifiers result with
        | Tnamed bc , Tnamed rc =>
            check_list' bc ts rc
        | _ , _ =>
            throw ("cast does not start and end on named types "%bs, from, result)
        end.

      Definition of_cast (c : Cast) (base : decltype) : M decltype :=
        let require_float t :=
          match t with
          | Tfloat_ _ => mret tt
          | _ => throw ("floating point required"%bs, t)
          end
        in
        let require_integral t :=
          match t with
          | Tnum _ _ | Tbool | Tchar_ _ => mret tt
          | _ => throw ("integral type required"%bs, t)
          end
        in
        match c with
        | Cdependent t
        | Cbitcast t
        | Clvaluebitcast t => mret t
        | Cl2r =>
            let* et := requireGL base in
            (* let* _ := requirePR dt >>= require_eq (drop_qualifiers et) in *)
            mret $ drop_qualifiers et
        | Cl2r_bitcast t =>
            let* et := requireGL base in
            (* let* _ := requirePR dt >>= require_eq (drop_qualifiers et) in *)
            mret $ drop_qualifiers t
        | Cnoop t => mret t
        | Carray2ptr =>
            let k cv base :=
              match base with
              | Tarray ty _
              | Tincomplete_array ty
              | Tvariable_array ty _ =>
                  let res := Tptr $ tqualified cv ty in
                  (* let* _ := require_eq t res in *)
                  mret res
              | _ => mfail
              end
            in
            requireGL base >>= qual_norm k
        | Cfun2ptr =>
            let* base := requireL base in
            let* _ := require_functype base in
            (* let* _ := require_eq t (Tptr base) in *)
            mret $ Tptr base
        | Cint2ptr t
        | Cptr2int t => mret t
        | Cptr2bool => mret Tbool
        | Cderived2base ls t =>
            let* '(bvc, bt) := gl_or_ptr base in
            qual_norm (fun cv t =>
                         let* '(rvc, rt) := gl_or_ptr t in
                         let* _ := guard (bvc = rvc \/ (bvc = Lvalue /\ rvc = Xvalue)) in
                         let* _ := check_list bt ls rt in
                         mret $ vc_to_type rvc $ tqualified cv rt) t

        | Cbase2derived ls t =>
            let* '(bvc, bt) := gl_or_ptr base in
            qual_norm (fun cv t =>
                         let* '(rvc, rt) := gl_or_ptr t in
                         let* _ := guard (bvc = rvc \/ (bvc = Lvalue /\ rvc = Xvalue)) in
                         let* _ := check_list rt ls bt in
                         mret $ vc_to_type rvc $ tqualified cv rt) t

        | Cintegral t => mret t
        | Cint2bool => mret Tbool
        | Cnull2ptr t =>
            let* _ :=
              match (to_exprtype base).2 with
              | Tnullptr | Tnum _ _ => mret tt
              | _ => throw ("source of null2ptr cast must be nullptr or integral type"%bs, base)
              end
            in
            let* _ :=
              match t with
              | Tptr _ | Tnullptr => mret ()
              | _ => throw ("destination of null2ptr cast must be a pointer"%bs, t)
              end
            in
            mret t
        | Cfloat2int t =>
            let* _ := require_float base in
            let* _ := require_integral t in
            mret t
        | Cint2float t =>
            let* _ := require_integral base in
            let* _ := require_float t in
            mret t
        | Cfloat t =>
            let* _ := require_float base in
            let* _ := require_float t in
            mret t
        | Cnull2memberptr t
        | Cbuiltin2fun t
        | Cctor t => mret t
        | C2void => mret Tvoid
        | Cuser => mret base
        | Cdynamic to => mret to
        | Cunsupported _ to => mret to
        end.

      Definition not_const (t : exprtype) : M _ :=
        guard (Is_true $ qual_norm (fun cv _ => negb $ q_const cv) t).

      Definition not_volatile (t : exprtype) : M _ :=
        guard (Is_true $ qual_norm (fun cv _ => negb $ q_const cv) t).


      Definition supports_inc_dec (t : exprtype) : M _ :=
        match t with
        | Tnum _ _
        | Tchar_ _
        | Tfloat_ _
        | Tptr _ => mret ()
        | _ => throw "can not increment or decrement bool"%bs
        end.

      Definition of_expr_body (e : Expr) : M decltype :=
        trace e $
        let* result :=
        match e return M decltype with
        | Eparam X => mret $ Tresult_param X
        | Eunresolved_global on => mret $ Tresult_global on
        | Eunresolved_unop o e => Tresult_unop o <$> of_expr e
        | Eunresolved_binop o l r => Tresult_binop o <$> of_expr l <*> of_expr r
        | Eunresolved_call on es => Tresult_call on <$> traverse (T:=eta list) of_expr es
        | Eunresolved_member_call on obj es => Tresult_member_call on <$> of_expr obj <*> traverse (T:=eta list) of_expr es
        | Eunresolved_parenlist (Some t) es => Tresult_parenlist t <$> traverse (T:=eta list) of_expr es
        | Eunresolved_parenlist None _ => mfail
        | Eunresolved_member obj fld => Tresult_member <$> of_expr obj <*> mret fld

        | Evar ln t =>
            let* vt := var_type ln in
            (* type type annotation on a variable is a [decltype]. *)
            let* _ := require_eq t vt in
            mret $ tref QM t
        | Eenum_const n c =>
            let* ct := type_of_constant n c in
            let* _ := require_eq (Tenum n) ct in
            mret $ Tenum n
        | Eglobal nm ty =>
            (* TODO NAMES TYPING:
               1. fields are not included, these are necessary for <<sizeof()>> (see cxx/bitvector)
             *)
            (*
            let* from_env := type_of_global nm in
            trace ("from_env = ", from_env))%bs $
            let* _ := require_eq from_env (normalize_type ty) in
            *)
            mret $ tref QM (normalize_type ty)
        | Eglobal_member nm ty =>
            match nm with
            | Nscoped cls _ =>
              mret $ Tmember_pointer (Tnamed cls) ty
            | _ => mfail
            end

        | Echar _ t =>
            match t with
            | Tchar_ _
            | Tuchar | Tschar => mret t
            | _ => mfail
            end
        | Estring chars t =>
            mret $ Tref $ Tarray (Tconst t) (1 + literal_string.lengthN chars)
        | Eint _ t =>
            let* _ := guard (t ∈ [Tchar;Tuchar;Tschar;Tshort;Tushort;Tint;Tuint;Tlong;Tulong;Tlonglong;Tulonglong]) in
            mret t
        | Ebool _ => mret Tbool
        | Eunop op e t =>
            let* et := of_expr e >>= requirePR in
            let* t' := of_unop op et >>= requirePR in
            let* _ := guard (t = t') in
            mret t
        | Ebinop op l r t =>
            (* TODO (NAMES): i still need to check that the operation is permitted at this type *)
            let* lt := of_expr l in
            let* rt := of_expr r in
            of_binop op lt rt t
        | Ederef e t =>
            let* t' := of_expr e >>= require_ptr in
            let* _ := guard (t = t') in (* TODO: redundant type *)
            mret $ Tref t
        | Eaddrof e =>
            let* t := of_expr e >>= requireGL in
            mret $ Tptr t
        | Eassign le re t =>
            let* lt := of_expr le >>= requireL in
            let* rt := of_expr re >>= requireR in
            let* _ := not_const lt in
            let* _ := require_eq (drop_qualifiers lt) rt in
            let* _ := require_eq lt t in
            mret $ Tref lt
        | Eassign_op op le re t =>
            (* TODO (NAMES): i still need to check that the operation is permitted at this type *)
            let* lt := of_expr le >>= requireL in
            let* rt := of_expr re >>= requireR in
            let* _ := guard (qualifiers lt = QM) in (* <<volatile>> accesses are not allowed to use <<op=>> *)
            let* _ := require_eq lt t in
            mret $ Tref lt

        | Epreinc e t
        | Epredec e t =>
            let* lt := of_expr e >>= requireL in
            let* _ := require_eq lt t in (* TODO: redundant type *)
            let* _ := supports_inc_dec lt in
            mret $ Tref lt
        | Epostinc e t
        | Epostdec e t =>
            let* lt := of_expr e >>= requireL in
            let* _ := require_eq lt t in (* TODO: redundant type *)
            let* _ := supports_inc_dec lt in
            mret lt

        | Eseqand le re
        | Eseqor le re =>
            let* _ := of_expr le >>= require_testable in
            let* _ := of_expr re >>= require_testable in
            mret Tbool
        | Ecomma e1 e2 =>
            let* _ := of_expr e1 in
            of_expr e2
        | Ecall f es =>
            let* ft := of_expr f >=> require_ptr >=> require_functype in
            let* ts := traverse (T:=eta list) of_expr es in
            let* _ :=
              trace ("checking arguments "%bs, ft.(ft_arity), ft.(ft_params), ts) $
              check_args ft.(ft_arity) ft.(ft_params) ts in
            mret ft.(ft_return)
        | Eexplicit_cast _ t e =>
            let cast_result :=
              qual_norm (fun cv t =>
                           match t with
                           | Tnamed _
                           | Tarray _ _
                           | Tincomplete_array _
                           | Tvariable_array _ _
                           | Tenum _ => tqualified cv t
                           | _ => t
                           end)
            in
            let* ct := of_expr e in
            let* _ := require_eq ct (cast_result t) in
            (* ^^ in the case of pr-values, type qualifiers do not need to match *)
            mret $ cast_result t
            (*   ^ we return [t] to match the shallow checker, but we would
                 probably prefer dropping qualifiers *)
        | Ecast c e => of_expr e >>= of_cast c
        | Emember arrow e _ mut t =>
            (* TODO NAMES TYPING: [Emember false Xvalue] is an [Xvalue] *)
            let* edt := of_expr e >>= arrow_deref_get arrow in
            of_member edt mut t
        | Emember_ignore arrow eobj e =>
            let* _ := of_expr eobj >>= if arrow then require_ptr else mret in
            of_expr e
        | Emember_call arrow f obj es =>
            let* objT := of_expr obj >>= arrow_deref arrow in
            let* tes := traverse (T:=eta list) of_expr es in
            let* ft :=
              match f with
              | inl (_, _, ft) => require_functype ft
              | inr e =>
                  let* ft := of_expr e in
                  match ft with
                  | Tmember_pointer cls (Tfunction ft) =>
                      mret ft
                  | _ => mfail
                  end
              end
            in
            let* _ :=
              trace ("checking arguments "%bs, ft.(ft_arity), ft.(ft_params), tes) $
              check_args ft.(ft_arity) ft.(ft_params) tes in
            mret ft.(ft_return)

        | Eoperator_call _ f es =>
            let* tes := traverse (T:=eta list) of_expr es in
            let* '(result, fargs) :=
              match f with
              | operator_impl.Func _ ft =>
                  let* ft := require_functype ft in
                  mret (ft.(ft_return), ft.(ft_params))
              | operator_impl.MFunc _ _ ft =>
                  (* TODO: the type of the member function does not currently
                     contain the [Tmember_pointer] type *)
                  let* objT :=
                    match tes with
                    | obj :: _ => mret [obj]
                    | _ => mret []
                    end
                  in
                  let* ft := require_functype ft in
                  mret (ft.(ft_return), objT ++ ft.(ft_params))
              end
            in
            let* _ := check_args Ar_Definite fargs tes in
            mret result
        | Esubscript e1 e2 t =>
            let* t1 := of_expr e1 in
            let* t2 := of_expr e2 in
            of_subscript t1 t2 t
        | Esizeof te t
        | Ealignof te t =>
            let* _ :=
              match te with
              | inl t => mret ()
              | inr e => const () <$> of_expr e
                              (* TODO NAMES TYPING: the expression can refer to a field. *)
              end
            in
            const Tsize_t <$> guard (t = Tsize_t)
        | Eoffsetof _ _ t => mret t
        | Econstructor f es t =>
            (* TODO: check the type of the constructor [f] *)
            let* tes := traverse (T:=eta list) of_expr es in
            mret t
        | Elambda n es =>
            let* tes := traverse (T:=eta list) of_expr es in
            (* TODO: check the arguments to the constructor / the fields *)
            mret $ Tnamed n
        | Eimplicit e => of_expr e
        | Eimplicit_init t =>
            (**
          "References cannot be value-initialized".

          https://en.cppreference.com/w/cpp/language/value_initialization
             *)

            let* _ := requirePR t in
            mret t
        | Eif tst thn els t =>
            let* _ := of_expr tst >>= require_testable in
            let* tthn := of_expr thn >>= require_eq t in
            let* tels := of_expr els >>= require_eq t in
            mret t
        | Eif2 x lete tst thn els t =>
            let* lt := of_expr lete in
            with_var (localname.anon x) lt $
              let* _ := of_expr tst >>= require_testable in
              let* tthn := of_expr thn in
              let* _ := of_expr els >>= require_eq tthn in
              let* _ := guard (t = tthn) in
              mret t
        | Ethis t =>
            let* pt := require_ptr t in
            let* _ := ask_this >>= require_eq pt in
            mret t
        | Enull => mret Tnullptr
        | Einitlist es oe t =>
            let* _ := traverse (T:=eta list) of_expr es in
            let* _ :=
              match oe with
              | None => mret tt
              | Some e => const tt <$> of_expr e
              end
            in
            mret t
        | Einitlist_union _ oe t =>
            let* _ :=
              match oe with
              | None => mret tt
              | Some e => const tt <$> of_expr e
              end
            in
            mret t
        | Enew (alloc, alloc_ty) aes nf aty osz oinit =>
            let* ats := traverse (T:=eta list) of_expr aes in
            let* afty := require_functype alloc_ty in
            let* _ :=
              let* _ := guard (afty.(ft_return) = Tptr Tvoid) in
              let* params :=
                match afty.(ft_params) return M (list decltype) with
                | Tsize_t :: params => mret params
                | args => trace (Bad_allocation_function_args args) $ mfail
                end
              in
              let* params :=
                if nf is new_form.Allocating true then
                  match params with
                  | Talign_t :: params => mret params
                  | _ => trace (Bad_allocation_function_args afty.(ft_params)) mfail
                  end
                else
                  mret params
              in
              check_args afty.(ft_arity) params ats
            in
            let* _ :=
              match osz with
              | None => mret tt
              | Some sz =>
                  let* tsz := of_expr sz in
                  if is_arithmetic tsz then mret tt else mfail
              end
            in
            let* _ :=
              match oinit with
              | None => mret tt
              | Some init => let* _ := of_expr init in mret tt (* TODO: check result type against [aty] *)
              end
            in
            mret $ Tptr aty
        | Edelete _ del e ty =>
            let* et := of_expr e >>= require_ptr in
            let* _ := guard (ty = et) in (* TODO: constness check? *)
            mret Tvoid
        | Eandclean e => of_expr e
        | Ematerialize_temp e vc =>
            let* _ := guard (vc <> Prvalue) in
            of_exprtype vc <$> (of_expr e >>= requirePR)
        | Eatomic _ es t =>
            let* tes := traverse (T:=eta list) of_expr es in
            mret t
        | Estmt s t =>
            let* st := of_stmt s in
            let* _ := require_eq st (Some t) in
            mret t
        | Eva_arg e t =>
            let* _ := of_expr e in (* TODO: what type should this have? *)
            mret $ normalize t
        | Epseudo_destructor arr t e =>
            let* et := of_expr e >>= arrow_deref arr in
            let* _ := require_eq t (drop_qualifiers et) in
            mret Tvoid
        | Earrayloop_init n e level _ e2 t =>
            let* _ := of_expr e in
            let* _ :=
              with_var (localname.arrayloop_index level) Tsize_t $
                       with_var (localname.opaque n) t $
                of_expr e2 in
            mret t
        | Earrayloop_index n t =>
            let* _ := var_type (localname.arrayloop_index n) >>= require_eq t in
            mret t (* always pr-values? *)
        | Eopaque_ref n t =>
            let* vt := var_type (localname.opaque n) in
            let* _ := requireGL t >>= can_initialize vt in
            (* ^^ in practice, the type and the recorded variable type
               differ by <<const>> qualifiers in instance-specific ways *)
            mret t
        | Eunsupported _ t => mret t
        end
        in
        let* _ :=
          match decltype.of_expr e with
          | None =>
              throw ("shallow failed to typecheck (term, expected)"%bs, e, result)
          | Some shallow =>
            trace ("type mismatch"%bs, result, shallow) $ require_eq result shallow
          end
        in
        mret result.
    End fixpoint.

    Definition big_op `{Mon : monoid.Monoid m} `{Traverse T} (ls : T m) : m :=
      writer.value $ traverse (F:=writer.M m) (T:=T) (writer.tell) ls.

    Section var_decl.
      Context (of_expr : Expr -> M decltype).

      Definition check_binding (d : BindingDecl) : M bindings :=
        match d with
        | Bvar lname ty init =>
            let* _ := of_expr init >>= can_initialize ty in
            mret ({| _bindings := [(lname, ty)] |})
        | Bbind lname ty init =>
            let* _ := (of_expr init >>= requireGL) >>= can_initialize ty in
            mret ({| _bindings := [(lname, ty)] |})
        end.

      Definition check_decl (d : VarDecl) : M bindings :=
        trace d
        match d with
        | Dvar lname ty oinit =>
            let* _ :=
              match oinit with
              | None => mret tt
              | Some init =>
                  let* _ := with_var lname ty $ of_expr init >>= can_initialize ty in
                  mret tt
              end
            in
            mret ({| _bindings := [(lname, ty)] |})
        | Ddecompose e v ds =>
            let* t := of_expr e in
            let* (bindings : list bindings) := with_var v t $ traverse (T:=eta list) check_binding ds in
            mret $ big_op bindings
        | Dinit _ nm ty oinit =>
            let* _ :=
              match oinit with
              | None => mret tt
              | Some init =>
                  let* _ := of_expr init >>= can_initialize ty in
                  mret tt
              end
            in
            mret monoid.monoid_unit
        end.

    End var_decl.

    Section stmt.
      Context (of_expr : Expr -> M decltype).

      Notation check_decl := (check_decl of_expr) (only parsing).

      Definition check_decls (ds : list VarDecl) : M bindings :=
        big_op (T:=eta list) <$> traverse (F:=M) (T:=eta list) check_decl ds.

      Fixpoint check_stmt_body (s : Stmt) : M (bindings * option decltype) :=
        let check_stmt := check_stmt_body in
        trace s
        match s with
        | Sgoto _ => mret (∅, None)
        | Slabeled _ s => check_stmt s
        | Sexpr e =>
            pair monoid.monoid_unit ∘ Some <$> of_expr e
        | Sdefault | Scase _ | Sbreak | Scontinue => mret (∅, None)
        | Sseq ss =>
            (fix block ss :=
               match ss with
               | nil => mret (∅, None)
               | s :: ss =>
                   let* '(b,d) := check_stmt s in
                   with_bindings b $ block ss
               end) ss
        | Sif vd tst thn els =>
            let* ds := from_option check_decl (mret monoid.monoid_unit) vd in
            let* _ :=
              with_bindings ds $
                let* _ := of_expr tst >>= require_testable in
                let* _ := check_stmt thn in
                check_stmt els
            in mret (∅, None)
        | Sif_consteval thn els =>
            let* _ := check_stmt thn in
            check_stmt els
        | Sswitch vd tst b =>
            let* ds := from_option check_decl (mret monoid.monoid_unit) vd in
            let _ :=
              with_bindings ds $
                let* _ := of_expr tst >>= require_eq Tint in (* TODO: BAD *)
                check_stmt b
            in mret (∅, None)
        | Swhile vd tst body =>
            let* ds := from_option check_decl (mret monoid.monoid_unit) vd in
            let k :=
              with_bindings ds $
                let* _ := of_expr tst >>= require_testable in
                check_stmt body
            in mret (∅, None)
        | Sdo s tst =>
            let* _ := check_stmt s in
            let* _ := of_expr tst >>= require_testable in (* TODO *)
            mret (∅, None)
        | Sfor vd otst oincr body =>
            let* '(ds, _) := from_option check_stmt (mret (monoid.monoid_unit, None)) vd in
            let* _ :=
              with_bindings ds $
                let* _ := from_option (fun e => of_expr e >>= require_testable) (mret tt) $ otst in
                let* _ := from_option (fun e => let* _ := of_expr e in mret tt) (mret tt) $ oincr in
                check_stmt body
            in mret (∅, None)
        | Sdecl ds =>
            let* b := check_decls ds in
            mret (b, None)
        | Sreturn None =>
            let* _ := ask_return >>= require_eq Tvoid in
            mret (∅, None)
        | Sreturn (Some e) =>
            let* ret := ask_return in
            let* _ := of_expr e >>= can_initialize ret in
            mret (∅, None)
        | Sattr _ s =>
            check_stmt s (* TODO: confirm scope *)
        | Sasm _ _ ins outs args =>
            let* _ := traverse (T:=eta list) (fun ab => of_expr ab.2) ins in
            let* _ := traverse (T:=eta list) (fun ab => of_expr ab.2) outs in
            mret (∅, None)
        | Sunsupported _ => mfail
        end.
    End stmt.

    Fixpoint of_expr (e : Expr) : M decltype :=
      of_expr_body of_expr check_stmt e
    with check_stmt (s : Stmt) : M (option decltype) :=
      snd <$> check_stmt_body of_expr s.


    Definition Merr : Set -> Set :=
      readerT.M ext_tu (trace.M Error.t).

    Definition lift_reader {S S' T M} (f : S -> S') (m : readerT.M S' M T) : readerT.M S M T :=
      readerT.mk $ fun s => readerT.run m (f s).

    Definition check_func (f : Func) : Merr unit :=
      match f.(f_body) with
      | None => mret ()
      | Some (Impl body) =>
          readerT.mk $ fun tu =>
            const () <$> readerT.run (with_bindings {| _bindings := f.(f_params) |} $ check_stmt body)
              (tu, f.(f_return), None, [])
      | Some (Builtin _) => mret ()
      end.

    Definition classname_to_type : classname -> type :=
      Tnamed.

    Definition check_method (m : Method) : Merr unit :=
      match m.(m_body) with
      | Some (UserDefined s) =>
          readerT.mk $ fun tu =>
          let this_type := tqualified m.(m_this_qual) $ classname_to_type m.(m_class) in
          const () <$> readerT.run (with_bindings {| _bindings := m.(m_params) |} $ check_stmt s) (tu, m.(m_return), Some this_type, [])
      | _ => mret ()
      end.

    Definition check_ctor (c : Ctor) : Merr unit :=
      match c.(c_body) with
      | Some (UserDefined (inits, body)) =>
          readerT.mk $ fun tu =>
          readerT.run (with_bindings {| _bindings := c.(c_params) |} $
                         let* _ := traverse (T:=eta list) (fun init => of_expr init.(init_init)) inits in
                         const () <$> check_stmt body) (tu, Tvoid, Some (classname_to_type c.(c_class)), [])
      | _ => mret ()
      end.

    Definition check_dtor (d : Dtor) : Merr unit :=
      match d.(d_body) with
      | Some (UserDefined body) =>
          readerT.mk $ fun tu =>
          readerT.run (const () <$> check_stmt body) (tu, Tvoid, Some (classname_to_type d.(d_class)), [])
      | _ => mret ()
      end.

    Definition check_obj_value (o : ObjValue) : Merr unit :=
      readerT.trace (breadcrumb o)
      match o with
      | Ovar _ oinit =>
          match oinit with
          | global_init.Init init =>
              readerT.mk $ fun tu =>
              const () <$> readerT.run (of_expr init) (tu, Tvoid, None, []) (* Tvoid isn't really correct here *)
          | _ => mret tt
          end
      | Ofunction f => check_func f
      | Omethod m => check_method m
      | Oconstructor c => check_ctor c
      | Odestructor d => check_dtor d
      end.

  End with_lang.

  End internal.

  Definition tu_to_ext (tu : translation_unit) : internal.ext_tu :=
    {| internal.ext_symbols nm := fmap (M:=fun t => option t) type_of_value $ tu.(symbols) !! nm
    ; internal.ext_types nm := types tu !! nm |}.

  Definition of_expr (tu : translation_unit) (e : Expr) : trace.M Error.t decltype :=
     readerT.run (internal.of_expr e) (tu_to_ext tu, Tvoid, None, []).

  Definition check_tu (tu : translation_unit) : trace.M Error.t unit :=
    let fn (nm_v : name * ObjValue) :=
      trace (breadcrumb nm_v.1) $ internal.check_obj_value nm_v.2
    in
    let* _ := readerT.run (traverse (T:=eta list) fn $ NM.elements tu.(symbols)) $ tu_to_ext tu in
    mret tt.
End decltype.

Module exprtype.
Section exprtype.
  Context (tu : translation_unit).

  Definition of_expr (e : Expr) : option (ValCat * exprtype) :=
    trace.runO $ decltype.to_exprtype <$> decltype.of_expr tu e.

  Definition of_expr_drop (e : Expr) : option exprtype :=
    trace.runO $ drop_reference <$> decltype.of_expr tu e.

  Definition of_expr_check (P : ValCat -> Prop) `{!∀ vc, Decision (P vc)}
      (e : Expr) : option exprtype :=
    of_expr e >>= fun p => guard (P p.1) ;; mret p.2.

End exprtype.
End exprtype.
