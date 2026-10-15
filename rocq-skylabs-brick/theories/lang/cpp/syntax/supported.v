(*
 * Copyright (c) 2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import stdpp.fin_maps.
Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.syntax.core.
Require Import skylabs.lang.cpp.syntax.types.
Require Import skylabs.lang.cpp.syntax.typing.
Require Import skylabs.lang.cpp.syntax.translation_unit.
Require Import skylabs.lang.cpp.syntax.templates.
Require Import skylabs.lang.cpp.semantics.cast_operator.
Require skylabs.lang.cpp.syntax.name_notation.parser.
Require skylabs.lang.cpp.syntax.name_notation.printer.

(** ** Supported Check

    This file implements a *light-weight* check on terms to determine if they
    use features BRiCk's semantics does not support. It is not a type checker:
    [typed.v](typed.v) checks that terms are well-typed, including that the
    shallow [type_of] this file relies on agrees with full typing.

    [walk] traverses a term once and records gaps in the semantics
    ([Gap Unsupported]: no semantics, proofs get stuck; [Gap Partial]: partial
    semantics, proofs may get stuck or prove less than the code does), and
    the names the term needs ([Ref], [Access]). [check] only keeps
    [Unsupported] gaps; [report] answers per C++ entity.

    Each [Gap Unsupported] mirrors a place where the semantics in [logic/] gets
    stuck: an [UNSUPPORTED] or [ERROR] case, a [False], or a missing [wp]
    rule. See [tests/supported_report.v].
 *)

Module walk.
  Variant gap : Set := Unsupported | Partial.

  Variant item : Set :=
  | Gap (g : gap) (msg : PrimString.string)
  | Ref (n : name)    (** needs the definition of [n] (type, function, variable) *)
  | Access (n : name) (** accesses a member of an object of class [n] *).

Section with_monad.

  Definition M := list item.
  Definition op : M -> M -> M := List.app.
  Definition OK : M := [].
  Definition FAIL (msg : PrimString.string) : M := [Gap Unsupported msg].
  Definition PARTIAL (msg : PrimString.string) : M := [Gap Partial msg].
  Definition REF (n : name) : M := [Ref n].

  (** Pointers and references do not need the definition of their target. *)
  Definition no_refs : M -> M := List.filter (fun i => if i is Ref _ then false else true).

  #[local] Infix "<+>" := op (at level 30).
  #[local] Notation opt f := (from_option f OK).
  #[local] Notation lst f xs := (List.concat (List.map f xs)).

  Definition check_float_width (ft : float_type.t) : M :=
    if float_type.supported ft then OK else FAIL "unsupported floating width".

  Definition as_float_type (t : type) : option float_type.t :=
    match drop_qualifiers t with
    | Tfloat_ ft => Some ft
    | _ => None
    end.

  Definition is_float_type (t : type) : bool :=
    if as_float_type t is Some _ then true else false.

  Definition check_float_type_if_present (t : type) : M :=
    match as_float_type t with
    | Some ft => check_float_width ft
    | None => OK
    end.

  Definition check_float_cast_target (t : type) : M :=
    match as_float_type t with
    | Some ft => check_float_width ft
    | None => FAIL "expected floating cast target"
    end.

  Definition check_float_cast_source (t : type) : M :=
    match as_float_type t with
    | Some ft => check_float_width ft
    | None => FAIL "expected floating cast source"
    end.

  Definition check_unop (op : UnOp) (argT resT : type) : M :=
    (match op with
     | Uunsupported msg => FAIL msg
     | _ => OK
     end) <+>
    if is_float_type argT || is_float_type resT then
      check_float_type_if_present argT <+> check_float_type_if_present resT <+>
      match op with
      | Uplus | Uminus | Unot => OK
      | Ubnot => FAIL "unsupported floating unary operator"
      | Uunsupported _ => OK
      end
    else OK.

  Definition check_float_binop (op : BinOp) : M :=
    match result_type op Tfloat with
    | Some _ => OK
    | None => FAIL "unsupported floating binary operator"
    end.

  Definition check_binop (op : BinOp) (lhsT rhsT resT : type) : M :=
    (match op with
     | Bunsupported msg => FAIL msg
     | _ => OK
     end) <+>
    if is_float_type lhsT || is_float_type rhsT || is_float_type resT then
      check_float_type_if_present lhsT <+>
      check_float_type_if_present rhsT <+>
      check_float_type_if_present resT <+>
      if is_pointer lhsT || is_pointer rhsT then
        FAIL "unsupported pointer/floating operator"
      else
        match op with
        | Bunsupported _ => OK
        | _ => check_float_binop op
        end
    else OK.

  Definition check_float_cast_expr (c : Cast) (srcT : type) : M :=
    match c with
    | Cfloat t =>
        check_float_cast_source srcT <+> check_float_cast_target t
    | Cint2float t =>
        check_float_cast_target t <+>
        if is_float_type srcT then FAIL "invalid floating cast source" else OK
    | Cfloat2int t =>
        check_float_cast_source srcT <+>
        if is_float_type t then FAIL "invalid floating cast target" else OK
    | Cfloat2bool => check_float_cast_source srcT
    | _ => OK
    end.

  (** Compare-exchange only has rules for integers and booleans
      (see [logic/atomics.v]). *)
  Definition check_atomic (op : AtomicOp) (es : list Expr) : M :=
    if bool_decide (op = "__atomic_compare_exchange_n"%pstring) ||
       bool_decide (op = "__atomic_compare_exchange"%pstring)
    then match es with
         | e :: _ =>
             match drop_qualifiers (type_of e) with
             | Tptr t =>
                 match drop_qualifiers t with
                 | Tnum _ _ | Tbool => OK
                 | _ => FAIL "atomic compare-exchange on non-integer values"
                 end
             | _ => OK
             end
         | [] => OK
         end
    else OK.

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
      | Atemplate_param _ => OK
      | Aunsupported msg => FAIL msg
      end.
  End temp_arg.

  Section temp_param.
    Context (name : name -> M) (type : type -> M) (expr : Expr -> M).
    Fixpoint temp_param  (a : temp_param) : M :=
      match a with
      | Ptype _ => OK
      | Pvalue _ t => type t
      | Ptemplate _ ps => lst temp_param ps
      | Punsupported msg => FAIL msg
      end.

    Definition temp_param_entry (a : core.temp_param * option core.temp_arg) : M :=
      temp_param a.1 <+> opt (temp_arg name type expr) a.2.
  End temp_param.

  (* The types in a name (parameters, template arguments) identify it; they
     are not needed. What a template instance needs comes from its own
     definition. *)
  Fixpoint name (n : name) : M :=
    no_refs match n with
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
    | Tptr t | Tref t | Trv_ref t => no_refs (type t)
    | Tarray t _ | Tincomplete_array t => type t
    | Tnum _ _ | Tchar_ _ | Tvoid | Tbool | Tnullptr => OK
    | Tfloat_ ft => check_float_width ft
    | Tvariable_array t e =>
        (* Templates also use [Tvariable_array] for dependent sizes. *)
        (if is_dependentE e then OK else FAIL "variable-length array") <+> type t <+> expr e
    (* Like a pointee, a function type needs its return and parameter types
       only well-scoped ([complete_pt_function]); a call needs them complete
       through the types of its arguments and result. *)
    | Tfunction (FunctionType t ts) => no_refs (type t <+> lst type ts)
    | Tmember_pointer t1 t2 => no_refs (type t1 <+> type t2)
    | Tqualified q t =>
        (if q_volatile q then PARTIAL "volatile: accesses are modelled as ordinary memory" else OK)
        <+> type t
    | Tarch _ _ => OK
    | Tdecltype e | Texprtype e => expr e
    | Tnamed n | Tenum n => REF n <+> name n
    end

  with expr (e : Expr) : M :=
    match e with
    | Evar _ t => type t
    | Eenum_const n _ => name n
    | Eglobal n t | Eglobal_member n t => REF n <+> name n <+> type t
    | Echar _ t | Estring _ t | Eunresolved_string_literal t | Eint _ t => type t
    | Efloat ft _ => check_float_width ft
    | Ebool _ => OK
    | Eunop op e t => expr e <+> type t <+> check_unop op (type_of e) t
    | Ebinop op e1 e2 t => expr e1 <+> expr e2 <+> type t <+> check_binop op (type_of e1) (type_of e2) t
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
    | Eassign e1 e2 t => expr e1 <+> expr e2 <+> type t
    | Eassign_op op e1 e2 t => expr e1 <+> expr e2 <+> type t <+> check_binop op (type_of e1) (type_of e2) t
    | Epreinc e t | Epostinc e t | Epredec e t | Epostdec e t =>
        expr e <+> type t <+>
        if is_float_type (type_of e) || is_float_type t then FAIL "unsupported floating increment/decrement" else OK
    | Eseqand e1 e2 | Eseqor e1 e2 | Ecomma e1 e2 => expr e1 <+> expr e2
    | Ecall e es => expr e <+> lst expr es
    | Eoperator_call _ impl es =>
        match impl with
        | operator_impl.Func n _ | operator_impl.MFunc n _ _ => REF n
        end <+> lst expr es
    | Epseudo_destructor _ t e => type t <+> expr e
    | Einitlist es oe t => lst expr es <+> opt expr oe <+> type t
    | Einitlist_union _ oe t => opt expr oe <+> type t
    | Einitlist_std e t => expr e <+> type t
    | Emember_call _ mr e es =>
        match mr with
        | inr e => expr e
        | inl (n, _, _) => REF n
        end <+> expr e <+> lst expr es
    | Enew (n, t) es _ t1 oe1 oe2 =>
        REF n <+> name n <+> type t <+> lst expr es <+> type t1 <+> opt expr oe1 <+> opt expr oe2
    | Edelete _ n e t => REF n <+> name n <+> expr e <+> type t
    | Eexplicit_cast _ t e => type t <+> expr e
    | Ecast c e => cast c <+> expr e <+> check_float_cast_expr c (type_of e)
    | Emember arrow e an _ t =>
        (* With [arrow], [e] is a pointer; either way, the class must be defined. *)
        let obj := drop_qualifiers (type_of e) in
        let obj := if arrow then (if obj is Tptr t then drop_qualifiers t else obj) else obj in
        (if obj is Tnamed cls then [Access cls; Ref cls] else OK)
        <+> expr e <+> atomic_name type an <+> type t
    | Estmt s t => stmt s <+> type t
    | Enull => OK
    | Eopaque_ref _ t => type t
    | Eva_arg e t => expr e <+> type t
    | Eatomic op es t => lst expr es <+> type t <+> check_atomic op es
    | Eandclean e => expr e
    | Ematerialize_temp e _ => expr e
    | Ethis t => type t
    | Eif e1 e2 e3 t => expr e1 <+> expr e2 <+> expr e3 <+> type t
    | Eif2 _ e1 e2 e3 e4 t => expr e1 <+> expr e2 <+> expr e3 <+> expr e4 <+> type t
    | Elambda nm es => name nm <+> lst expr es
    | Econstructor nm es t => REF nm <+> name nm <+> lst expr es <+> type t
    | Einherited_constructor nm _ t => REF nm <+> name nm <+> type t
    | Eimplicit e => expr e
    | Emember_ignore _ _ e => expr e
    | Eimplicit_init t => type t
    | Eparam _ => OK
    | Eunresolved_global n => name n
    | Eunresolved_sizeof_pack _ t => type t
    | Eunresolved_unop _ e => expr e
    | Eunresolved_binop _ e1 e2 => expr e1 <+> expr e2
    | Eunresolved_call n es => name n <+> lst expr es
    | Eunresolved_member_call _ _ _
    | Eunresolved_parenlist _ _
    | Eunresolved_initlist _ _
    | Eunresolved_member _ _ => OK
    | Earrayloop_init _ e _ _ e2 t => expr e <+> expr e2 <+> type t
    | Earrayloop_index _ t => type t
    | Eunsupported msg t => FAIL msg
    end

  with stmt (s : Stmt) : M :=
    match s with
    | Sseq ss => lst stmt ss
    | Sdecl ds => lst var_decl ds
    | Sif os ovd e s1 s2 => opt stmt os <+> opt var_decl ovd <+> expr e <+> stmt s1 <+> stmt s2
    | Sif_consteval _ _ => FAIL "if consteval"
    | Swhile ovd e s => opt var_decl ovd <+> expr e <+> stmt s
    | Sdo s e => stmt s <+> expr e
    | Sfor os oe1 oe2 s =>
        opt stmt os <+> opt expr oe1 <+> opt expr oe2 <+> stmt s
    | Sswitch os ovd e s => opt stmt os <+> opt var_decl ovd <+> expr e <+> stmt s
    | Scase _ => OK
    | Sdefault | Sbreak | Scontinue => OK
    | Sreturn oe => opt expr oe
    | Sexpr e => expr e
    | Sasm _ _ lpe1 lpe2 _ =>
        FAIL "inline assembly" <+> lst (expr ∘ snd) lpe1 <+> lst (expr ∘ snd) lpe2
    | Sattr _ s => stmt s
    | Slabeled _ s => stmt s
    | Sgoto _ => FAIL "goto"
    | Sunsupported msg => FAIL msg
    end

  with var_decl (v : VarDecl) : M :=
    match v with
    | Dvar _ t oe =>
        (if q_volatile (decompose_type t).1 then FAIL "volatile object" else OK)
        <+> type t <+> opt expr oe
    | Ddecompose e _ bds => expr e <+> lst binding_decl bds
    | Dinit _ n t oe => FAIL "static local variable" <+> name n <+> type t <+> opt expr oe
    end

  with binding_decl (b : BindingDecl) : M :=
    match b with
    | Bvar _ t e => type t <+> expr e
    | Bbind _ t e => type t <+> expr e
    end

  with cast (c : Cast) : M :=
    match c with
    | Cdependent t | Cbitcast t | Cnoop t | Cint2ptr t | Cptr2int t
    | Cintegral t
    | Cnull2ptr t | Cnull2memberptr t
    | Cbuiltin2fun t | Cctor t => type t
    | Clvaluebitcast t => FAIL "lvalue bitcast" <+> type t
    | Cdynamic t => FAIL "dynamic_cast" <+> type t
    | Cderived2base ts t | Cbase2derived ts t => lst type ts <+> type t
    | Cfloat t | Cint2float t => check_float_cast_target t
    | Cfloat2int t => type t <+> if is_float_type t then FAIL "invalid floating cast target" else OK
    | Cfloat2bool => OK
    | Cl2r_bitcast _ => FAIL "l2r_bitcast"
    | Cunsupported _ _ => FAIL "unsupported cast"
    | _ => OK
    end.

  Definition function_body (b : FunctionBody) : M :=
    match b with
    | Impl s => stmt s
    | Builtin _ => OK
    end.
  (** clang defines every defaulted member a translation unit uses, with or
      without cpp2v's elaboration, so a remaining [Defaulted] body belongs to
      an unused member and only matters when it is queried, see [report]. *)
  Definition or_default {T : Set} (f : T -> M) (o : OrDefault T) : M :=
    match o with
    | Defaulted => OK
    | CompilerProvided v => f v
    | UserDefined v => f v
    end.

  Definition classname (n : classname) : M := REF n <+> name n.

  Definition initializer (i : Initializer) : M :=
    (if i.(init_path) is InitIndirect _ _ then FAIL "indirect member initialization" else OK)
    <+> expr i.(init_init).

  Definition check_exc_spec {B} (exc : _) (body : option (OrDefault B)) : M :=
    if exc is exception_spec.Unknown
    then match body with
         | None | Some Defaulted => OK
         | _ => FAIL "unknown exception spec"
         end
    else OK.


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
        <+> check_exc_spec m.(m_exception) m.(m_body)

    | Oconstructor c =>
        let check_body '(li, s) := lst initializer li <+> stmt s in
        classname c.(c_class) <+> params c.(c_params)
        <+> opt (or_default check_body) c.(c_body)
        <+> check_exc_spec c.(c_exception) c.(c_body)

    | Odestructor d =>
        classname d.(d_class) <+> opt (or_default stmt) d.(d_body)
        <+> check_exc_spec d.(d_exception) d.(d_body)
    end.

  Definition member (m : Member) : M := type m.(mem_type) <+> opt expr m.(mem_init).

  Definition glob_decl (gd : GlobDecl) : M :=
    match gd with
    | Gunsupported msg => FAIL msg
    | Gtype => OK
    | Gunion u => lst member u.(u_fields)
    | Gstruct s => lst (classname ∘ fst) s.(s_bases) <+> lst member s.(s_fields)
    | Genum t _ => type t
    | Gconstant t oe => type t <+> opt expr oe
    | Gtypedef t => type t
    end.

  Definition translation_unit (tu : translation_unit) : M :=
    let symbol '(nm, obj) := obj_value obj in
    let gd '(nm, gd) := glob_decl gd in
    let msymbol '(nm, t_obj) :=
      lst (temp_param_entry name type expr) t_obj.(template_params)
      <+> obj_value t_obj.(template_value)
    in
    let mgd '(nm, t_gd) :=
      lst (temp_param_entry name type expr) t_gd.(template_params)
      <+> glob_decl t_gd.(template_value)
    in
    lst gd (namemap.NM.elements tu.(types)) <+>
    lst symbol (namemap.NM.elements tu.(symbols)) <+>
    lst mgd (namemap.NM.elements tu.(translation_unit.mtypes)) <+>
    lst msymbol (namemap.NM.elements tu.(translation_unit.msymbols)).

  Definition template_unit (mtu : Mtranslation_unit) : M :=
    let symbol '(nm, t_obj) :=
      lst (temp_param_entry name type expr) t_obj.(template_params)
      <+> obj_value t_obj.(template_value)
    in
    let gd '(nm, t_gd) :=
      lst (temp_param_entry name type expr) t_gd.(template_params)
      <+> glob_decl t_gd.(template_value)
    in
    lst gd (namemap.NM.elements mtu.(mtypes)) <+>
    lst symbol (namemap.NM.elements mtu.(msymbols)).

End with_monad.
End walk.

(** [Unsupported] gaps only. *)
Module check.
  Definition M := list PrimString.string.
  Definition OK : M := [].
  Definition FAIL (msg : PrimString.string) : M := [msg].
  Definition fails (m : walk.M) : M :=
    List.flat_map (fun i => if i is walk.Gap walk.Unsupported msg then [msg] else []) m.

  Definition type t : M := fails (walk.type t).
  Definition expr e : M := fails (walk.expr e).
  Definition obj_value o : M := fails (walk.obj_value o).
  Definition glob_decl gd : M := fails (walk.glob_decl gd).
  Definition translation_unit tu : M := fails (walk.translation_unit tu).
  Definition template_unit mtu : M := fails (walk.template_unit mtu).
End check.

(** ** Per-entity report

    [report.run tu roots] resolves each root in [tu] (with the [cpp.spec] name
    parser) and returns:
    - [unsupported]: the entity's own [Unsupported] gaps;
    - [partial]: [Partial] gaps in the entity or in the types it needs;
    - [blocked_by]: the types it needs (transitively, through fields and bases)
      with [Unsupported] gaps, and these gaps;
    - [unsupported_refs]: the functions and variables it refers to with
      [Unsupported] gaps. This is one level only: they do not block the
      entity, whose proof assumes their specs; query them as roots to go
      further.

    Types reached only through pointers or references are not needed. *)
Module report.
  Record entry : Set := mk_entry
    { input : PrimString.string
    ; resolved : PrimString.string (** [""] when [status = "missing"] *)
    ; status : PrimString.string   (** supported | partial | blocked | unsupported | missing *)
    ; unsupported : list PrimString.string
    ; partial : list PrimString.string
    ; blocked_by : list (PrimString.string * list PrimString.string)
    ; unsupported_refs : list (PrimString.string * list PrimString.string) }.

  Definition print (n : name) : PrimString.string :=
    default "<unprintable name>"%pstring (printer.print_name n).

  Definition partials (m : walk.M) : list PrimString.string :=
    List.flat_map (fun i => if i is walk.Gap walk.Partial msg then [msg] else []) m.

  (** [walk.no_refs] discards needs, never gaps. *)
  Lemma fails_no_refs m : check.fails (walk.no_refs m) = check.fails m.
  Proof. elim: m => [//|[[] ?|?|?] m IH] /=; by rewrite IH. Qed.

  Lemma partials_no_refs m : partials (walk.no_refs m) = partials m.
  Proof. elim: m => [//|[[] ?|?|?] m IH] /=; by rewrite IH. Qed.

  (** [n] with its [Unsupported] gaps, if any. *)
  Definition named (n : name) (m : walk.M) : list (PrimString.string * list PrimString.string) :=
    if check.fails m is [] then [] else [(print n, check.fails m)].

  Section with_tu.
    Context (tu : translation_unit).

    Definition refs (m : walk.M) : list name :=
      remove_dups (List.flat_map (fun i => if i is walk.Ref n then [n] else []) m).

    Definition type_refs (m : walk.M) : list name :=
      List.filter (fun n => bool_decide (is_Some (tu.(types) !! n))) (refs m).

    (** Unions only record their active member, but changing it is not
        supported (see [union_change] in [logic/layout.v]). *)
    Definition union_members (m : walk.M) : list PrimString.string :=
      List.flat_map (fun i =>
        if i is walk.Access n then
          if tu.(types) !! n is Some (Gunion _)
          then ["union member access: changing the active member is not supported"%pstring]
          else []
        else []) m.

    (** [wp_method] and [wp_ctor] are stuck on [Defaulted] bodies. *)
    Definition defaulted (o : ObjValue) : walk.M :=
      match o with
      | Omethod m => if m.(m_body) is Some Defaulted then walk.FAIL "defaulted method" else []
      | Oconstructor c => if c.(c_body) is Some Defaulted then walk.FAIL "defaulted constructor" else []
      | _ => []
      end.

    Definition walk_type (n : name) : walk.M :=
      from_option walk.glob_decl [] (tu.(types) !! n).

    (** The types that the definition of type [n] needs. *)
    Definition succs (n : name) : list name := type_refs (walk_type n).

    Definition is_new (seen : list name) (n : name) : bool :=
      bool_decide (n ∉ seen) && bool_decide (is_Some (tu.(types) !! n)).

    (** The types needed by [todo], transitively. Each round adds at least one
        type, so one more round than there are types suffices (see
        [closure_complete]). *)
    (* ponytail: [seen] is a list, so membership is linear in the closure's
       size; use a name set if closures get large. *)
    Fixpoint closure (fuel : nat) (todo : list name) (seen : list name) : list name :=
      match fuel with
      | O => seen
      | S fuel =>
          match remove_dups (List.filter (is_new seen) todo) with
          | [] => seen
          | new => closure fuel (List.flat_map succs new) (new ++ seen)
          end
      end.

    Definition closure_fuel : nat := S (length (map_to_list tu.(types))).

    (** What the entity [n] itself uses. *)
    Definition own (n : name) : option walk.M :=
      match tu.(symbols) !! n, tu.(types) !! n with
      | Some o, _ => Some (defaulted o ++ walk.obj_value o)
      | None, gd => walk.glob_decl <$> gd
      end.

    (** [fuel] is [closure_fuel], computed once by [run]. *)
    Definition entry_for (fuel : nat) (input : PrimString.string) : entry :=
      if (n ← parser.parse_name_with tu input; pair n <$> own n) is Some (n, own) then
        let needed := List.filter (fun t => bool_decide (t <> n)) (closure fuel (type_refs own) []) in
        let used := own ++ List.flat_map walk_type needed in
        let unsupported := check.fails own in
        let blocked_by := List.flat_map (fun t => named t (walk_type t)) needed in
        let partial := remove_dups (partials used ++ union_members used) in
        let unsupported_refs :=
          List.flat_map (fun r =>
            if bool_decide (r = n) then [] else from_option (fun o => named r (walk.obj_value o)) [] (tu.(symbols) !! r))
            (refs own) in
        let status :=
          match unsupported, blocked_by, partial with
          | _ :: _, _, _ => "unsupported"
          | [], _ :: _, _ => "blocked"
          | [], [], _ :: _ => "partial"
          | [], [], [] => "supported"
          end%pstring
        in
        mk_entry input (print n) status unsupported partial blocked_by unsupported_refs
      else mk_entry input "" "missing" [] [] [] [].

    (** ** [closure] computes the whole closure *)

    Lemma type_refs_types m n : n ∈ type_refs m -> is_Some (tu.(types) !! n).
    Proof.
      rewrite /type_refs list_elem_of_In filter_In bool_decide_eq_true. naive_solver.
    Qed.

    Lemma types_keys n : is_Some (tu.(types) !! n) -> In n (map fst (map_to_list tu.(types))).
    Proof.
      move=> [v Hv]. have [xs [ys ->]] := NM.map_to_list_elements n v _ Hv.
      apply/in_map_iff. exists (n, v). split; first done. apply/in_app_iff. by right; left.
    Qed.

    Lemma closure_spec fuel todo seen :
      NoDup seen ->
      (forall n, n ∈ seen -> is_Some (tu.(types) !! n)) ->
      (forall n, n ∈ seen -> forall m, m ∈ succs n -> m ∈ seen \/ m ∈ todo) ->
      length (map_to_list tu.(types)) - length seen < fuel ->
      let s := closure fuel todo seen in
      seen ⊆ s /\ NoDup s /\ (forall n, n ∈ s -> is_Some (tu.(types) !! n)) /\
      (forall n, n ∈ todo -> is_Some (tu.(types) !! n) -> n ∈ s) /\
      (forall n, n ∈ s -> forall m, m ∈ succs n -> m ∈ s).
    Proof.
      elim: fuel todo seen => [|fuel IH] todo seen Hnd Htys Hclosed Hfuel /=; first lia.
      have Hnew n : n ∈ remove_dups (List.filter (is_new seen) todo) <->
                    n ∈ todo /\ n ∉ seen /\ is_Some (tu.(types) !! n).
      { rewrite elem_of_remove_dups list_elem_of_In filter_In -list_elem_of_In /is_new.
        rewrite andb_true_iff !bool_decide_eq_true. naive_solver. }
      have Hin n : n ∈ todo -> is_Some (tu.(types) !! n) ->
                   n ∈ seen \/ n ∈ remove_dups (List.filter (is_new seen) todo).
      { move=> ??. destruct (decide (n ∈ seen)); [by left|right]. by apply Hnew. }
      destruct (remove_dups (List.filter (is_new seen) todo)) as [|n0 rest] eqn:Hdups.
      { split_and!; [done|done|done| |].
        - move=> n ??. by destruct (Hin n) as [|?%elem_of_nil].
        - move=> n Hn m Hm. destruct (Hclosed n Hn m Hm) as [|Htodo]; first done.
          by destruct (Hin m Htodo (type_refs_types _ _ Hm)) as [|?%elem_of_nil]. }
      set new := n0 :: rest.
      have Hnew' n : n ∈ new <-> n ∈ todo /\ n ∉ seen /\ is_Some (tu.(types) !! n).
      { by rewrite -Hnew. }
      have Hnd' : NoDup (new ++ seen).
      { apply NoDup_app. split_and!; last done.
        - rewrite /new -Hdups. apply NoDup_remove_dups.
        - move=> ? /Hnew'. naive_solver. }
      have Htys' n : n ∈ new ++ seen -> is_Some (tu.(types) !! n).
      { rewrite elem_of_app Hnew'. naive_solver. }
      have Hlen : length (new ++ seen) <= length (map_to_list tu.(types)).
      { rewrite -(List.length_map fst (map_to_list tu.(types))).
        apply NoDup_incl_length; first by apply NoDup_ListNoDup.
        move=> n /list_elem_of_In /Htys'. exact: types_keys. }
      have := IH (List.flat_map succs new) (new ++ seen) Hnd' Htys'.
      case.
      - move=> n. rewrite elem_of_app => -[Hn|Hn] m Hm.
        + right. rewrite list_elem_of_In in_flat_map. exists n.
          by rewrite -!list_elem_of_In.
        + left. rewrite elem_of_app.
          destruct (Hclosed n Hn m Hm) as [|Htodo]; first by right.
          destruct (Hin m Htodo (type_refs_types _ _ Hm)); [by right|by left].
      - rewrite length_app /= in Hlen *. lia.
      - move=> Hs [? [? [_ ?]]]. split_and!; [set_solver|done|done| |done].
        move=> n ??. apply Hs. rewrite elem_of_app. destruct (Hin n); [done|done|by right|by left].
    Qed.

    (** Starting from nothing, [closure_fuel] rounds yield exactly the types
        needed by [todo], transitively, without duplicates. *)
    Lemma closure_complete todo :
      let s := closure closure_fuel todo [] in
      NoDup s /\ (forall n, n ∈ s -> is_Some (tu.(types) !! n)) /\
      (forall n, n ∈ todo -> is_Some (tu.(types) !! n) -> n ∈ s) /\
      (forall n, n ∈ s -> forall m, m ∈ succs n -> m ∈ s).
    Proof.
      have := closure_spec closure_fuel todo [].
      case; [constructor|set_solver|set_solver|rewrite /closure_fuel /=; lia|naive_solver].
    Qed.
  End with_tu.

  Definition run (tu : translation_unit) (roots : list PrimString.string) : list entry :=
    List.map (entry_for tu (closure_fuel tu)) roots.
End report.
