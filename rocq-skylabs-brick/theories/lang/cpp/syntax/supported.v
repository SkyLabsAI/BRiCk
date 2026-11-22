(*
 * Copyright (c) 2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import stdpp.fin_maps.
Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.syntax.core.
Require Import skylabs.lang.cpp.syntax.stmt.
Require Import skylabs.lang.cpp.syntax.types.
Require Import skylabs.lang.cpp.syntax.typing.
Require Import skylabs.lang.cpp.syntax.translation_unit.
Require Import skylabs.lang.cpp.syntax.templates.
Require Import skylabs.lang.cpp.semantics.cast_operator.
Require skylabs.lang.cpp.syntax.name_notation.parser.
Require skylabs.lang.cpp.syntax.name_notation.printer.
Require skylabs.lang.cpp.syntax.pretty.

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

    [walk] takes an extension [ext], called on every expression, which adds
    gaps of a proof tool built on the semantics, e.g. a known automation gap
    (see [skylabs.auto.cpp.supported]). [check] and [report.run] use none.

    Without an extension, each [Gap Unsupported] mirrors a place where the
    semantics in [logic/] gets stuck: an [UNSUPPORTED] or [ERROR] case, a [False], or a missing [wp]
    rule. See [tests/supported_report.v].
 *)

Module walk.
  Variant gap : Set := Unsupported | Partial.

  Variant item : Set :=
  | Gap (g : gap) (msg : PrimString.string)
  | Ref (n : name)    (** needs the definition of [n] (type, function, variable) *)
  | Access (n : name) (** accesses a member of an object of class [n] *)
  | Bcall (n : name)  (** calls builtin [n] directly ([Cbuiltin2fun]) *).

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
     | Bdotp | Bdotip => FAIL "pointer-to-member access"
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

  (** The atomic operations with a rule (see [logic/atomics.v]). *)
  Definition atomic_with_rule (op : AtomicOp) : bool :=
    bool_decide (op ∈ [ "__atomic_load_n"; "__atomic_store_n"
      ; "__atomic_exchange_n"; "__atomic_exchange"
      ; "__atomic_compare_exchange_n"; "__atomic_compare_exchange"
      ; "__atomic_fetch_add"; "__atomic_fetch_sub"; "__atomic_fetch_and"
      ; "__atomic_fetch_xor"; "__atomic_fetch_or"; "__atomic_fetch_nand"
      ; "__atomic_add_fetch"; "__atomic_sub_fetch"; "__atomic_and_fetch"
      ; "__atomic_xor_fetch"; "__atomic_or_fetch"; "__atomic_nand_fetch"
      ]%pstring).

  Fixpoint strip_casts (e : Expr) : Expr :=
    match e with
    | Ecast _ e | Eexplicit_cast _ _ e | Eimplicit e => strip_casts e
    | _ => e
    end.

  (** Every rule needs [__ATOMIC_SEQ_CST] (5). A non-literal order (e.g. a
      parameter of <<std::atomic>>'s methods) is decided by the caller. *)
  Definition check_memorder (e : Expr) : M :=
    match strip_casts e with
    | Eint n _ =>
        if bool_decide (n = 5%Z) then OK
        else FAIL "atomic: only seq_cst memory order has rules"
    | _ => PARTIAL "atomic: memory order is not a literal; only seq_cst has rules"
    end.

  (** Compare-exchange only has rules for integers and booleans. *)
  Definition check_atomic (op : AtomicOp) (es : list Expr) : M :=
    if negb (atomic_with_rule op) then
      FAIL (PrimString.cat "atomic operation without semantics: " op)
    else
    (* The operands are, in this order: the pointer, the order, the value,
       the failure order (compare-exchange), ... *)
    opt check_memorder (nth_error es 1) <+>
    if bool_decide (op = "__atomic_compare_exchange_n"%pstring) ||
       bool_decide (op = "__atomic_compare_exchange"%pstring)
    then opt check_memorder (nth_error es 3) <+>
         match es with
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

  (** The builtins with a [wp_builtin] rule (see [logic/builtins.v]). *)
  Definition known_builtin (b : BuiltinFn) : bool :=
    bool_decide (b ∈ [ "__builtin_unreachable"; "__builtin_trap"; "__builtin_expect"
      ; "move"; "forward"; "__builtin_launder"
      ; "__builtin_ffs"; "__builtin_ffsl"; "__builtin_ffsll"
      ; "__builtin_ctz"; "__builtin_ctzl"; "__builtin_ctzll"
      ; "__builtin_clz"; "__builtin_clzl"; "__builtin_clzll"
      ; "__builtin_bswap16"; "__builtin_bswap32"; "__builtin_bswap64"; "__builtin_bswap128"
      ]%pstring).

  (** Direct calls to [b] (through [Cbuiltin2fun]): a builtin that is only
      declared is harmless; atomics, for instance, are called through
      [Eatomic]. *)
  Definition builtin (b : BuiltinFn) : M :=
    if known_builtin b then OK else FAIL (PrimString.cat "builtin without semantics: " b).

  (** Ordinary calls to a library function that clang treats as builtin [b]
      (e.g. <<memcpy>>, <<strlen>>): the caller assumes its spec, as for any
      callee without a definition. *)
  Definition library_builtin (b : BuiltinFn) : M :=
    if known_builtin b then OK
    else PARTIAL (PrimString.cat (PrimString.cat "library builtin " b)
      ": needs a spec (brick-libcpp or black-box)").

  (** Functions that return twice. A spec cannot describe the second return. *)
  Definition returns_twice (n : name) : bool :=
    match n with
    | Nglobal (Nid f) | Nglobal (Nfunction _ f _) =>
        bool_decide (f ∈ [ "setjmp"; "_setjmp"; "__setjmp"; "sigsetjmp"; "__sigsetjmp"
          ; "savectx"; "vfork"; "getcontext"; "__builtin_setjmp" ]%pstring)
    | _ => false
    end.

  (** A prvalue of class type needs its class (e.g. to allocate the result
      of a call). *)
  Definition prvalue_class (e : Expr) : M :=
    if valcat_of e is Prvalue then
      if drop_qualifiers (type_of e) is Tnamed n then REF n else OK
    else OK.

  (** The definition a type needs, without walking it. *)
  Fixpoint type_ref (t : type) : M :=
    match t with
    | Tnamed n | Tenum n => REF n
    | Tqualified _ t | Tarray t _ => type_ref t
    | _ => OK
    end.

  (** An object of class type is destroyed by its destructor. *)
  Definition dtor_of (t : type) : M :=
    match drop_qualifiers (decompose_type t).2 with
    | Tnamed n => REF (Nscoped n Ndtor)
    | Tarray t _ => if drop_qualifiers t is Tnamed n then REF (Nscoped n Ndtor) else OK
    | _ => OK
    end.

  (** [wp_switch] needs the [case]s and [default] of a block at its top level,
      not after a declaration (see [wp_switch_block] in [logic/stmt.v]). *)
  Fixpoint switch_cases (ls : list Stmt) : bool :=
    match ls with
    | (Scase _ | Sdefault) :: ls => switch_cases ls
    | Sdecl _ :: ls => no_case (Sseq ls)
    | s :: ls => no_case s && switch_cases ls
    | [] => true
    end.

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

  Context (ext : Expr -> M).

  (* The types in a name (parameters, template arguments) identify it; they
     are not needed. What a template instance needs comes from its own
     definition. *)
  (** BRiCk does not interpret any attribute yet ([attr.t] only has [Other]);
      cpp2v does not print the no-op ones. *)
  Definition attr (a : attr.t) : M :=
    match a with
    | attr.Other kind _ => FAIL (PrimString.cat "unsupported attribute: " kind)
    end.

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
    | Tattributed attrs t =>
        (* The program logic treats attributed types as opaque for now. *)
        lst attr attrs <+> type t <+> PARTIAL "attributed type (opaque to the program logic)"
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
    | Trealigned _ t =>
        PARTIAL "under-aligned object: only reads, assignments used as statements, initialization and destruction are modelled"
        <+> type t
    | Tdecltype e | Texprtype e => expr e
    | Tnamed n | Tenum n => REF n <+> name n
    end

  with expr (e : Expr) : M :=
    ext e <+>
    match e with
    | Evar _ t => type t
    | Eenum_const n _ => name n
    | Eglobal n t | Eglobal_member n t =>
        (if returns_twice n then FAIL "returns twice (setjmp family)" else OK)
        <+> REF n <+> name n <+> type t
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
        (* The operand is not evaluated: only its type matters. *)
        match et with
        | inr e => type_ref (type_of e)
        | inl t => type t
        end <+> type t
    | Eoffsetof t1 _ t2 => FAIL "offsetof" <+> type t1 <+> type t2
    | Eassign e1 e2 t | Ebf_assign e1 e2 t => expr e1 <+> expr e2 <+> type t
    | Eassign_op op e1 e2 t | Ebf_assign_op op e1 e2 t => expr e1 <+> expr e2 <+> type t <+> check_binop op (type_of e1) (type_of e2) t
    | Epreinc e t | Epostinc e t | Epredec e t | Epostdec e t
    | Ebf_preinc e t | Ebf_postinc e t | Ebf_predec e t | Ebf_postdec e t =>
        expr e <+> type t <+>
        if is_float_type (type_of e) || is_float_type t then FAIL "unsupported floating increment/decrement" else OK
    | Eseqand e1 e2 | Eseqor e1 e2 | Ecomma e1 e2 | Ebf_comma e1 e2 => expr e1 <+> expr e2
    | Ecall f es => prvalue_class e <+> expr f <+> lst expr es
    | Eoperator_call _ impl es =>
        prvalue_class e <+>
        match impl with
        | operator_impl.Func n _ | operator_impl.MFunc n _ _ => REF n
        end <+> lst expr es
    | Epseudo_destructor _ t e => type t <+> expr e
    | Einitlist es oe t => lst expr es <+> opt expr oe <+> type t
    | Einitlist_union _ oe t => opt expr oe <+> type t
    | Einitlist_std e t => expr e <+> type t
    | Emember_call _ mr obj es =>
        prvalue_class e <+>
        match mr with
        | inr f => FAIL "call through a pointer to member function" <+> expr f
        | inl (n, _, _) => REF n
        end <+> expr obj <+> lst expr es
    | Enew (n, t) es _ t1 oe1 oe2 =>
        REF n <+> name n <+> type t <+> lst expr es <+> type t1 <+> opt expr oe1 <+> opt expr oe2
    | Edelete _ n e t => REF n <+> name n <+> expr e <+> type t
    | Eexplicit_cast _ t e => type t <+> expr e
    | Ecast c e =>
        (if c is Cbuiltin2fun _ then if e is Eglobal n _ then [Bcall n] else OK else OK)
        <+> cast c <+> expr e <+> check_float_cast_expr c (type_of e)
    | Emember arrow e an _ t =>
        (* With [arrow], [e] is a pointer; either way, the class must be defined. *)
        let obj := drop_qualifiers (type_of e) in
        let obj := if arrow then (if obj is Tptr t then drop_qualifiers t else obj) else obj in
        (if obj is Tnamed cls then [Access cls; Ref cls] else OK)
        <+> expr e <+> atomic_name type an <+> type t
    | Ebitfield arrow e _ t =>
        (* Only the bit-fields that cpp2v lists in [o_bitfields] have a
           semantics; accesses to the others are stuck. The record is opaque,
           so this is not an [Access] (see [opaque_members]). *)
        let obj := drop_qualifiers (type_of e) in
        let obj := if arrow then (if obj is Tptr t then drop_qualifiers t else obj) else obj in
        (if obj is Tnamed cls then REF cls else OK)
        <+> PARTIAL "bit-field access: only integer bit-fields of classes are modelled"
        <+> expr e <+> type t
    | Estmt s t => FAIL "statement expression" <+> stmt s <+> type t
    | Enull => OK
    | Eopaque_ref _ t => type t
    | Eva_arg e t => FAIL "va_arg" <+> expr e <+> type t
    | Eatomic op es t => lst expr es <+> type t <+> check_atomic op es
    | Eandclean e => expr e
    | Ematerialize_temp e _ => dtor_of (type_of e) <+> expr e
    | Ethis t => type t
    | Eif e1 e2 e3 t | Ebf_if e1 e2 e3 t => expr e1 <+> expr e2 <+> expr e3 <+> type t
    | Eif2 _ e1 e2 e3 e4 t => expr e1 <+> expr e2 <+> expr e3 <+> expr e4 <+> type t
    | Elambda nm es => name nm <+> lst expr es
    | Econstructor nm es t => REF nm <+> name nm <+> lst expr es <+> type t
    | Einherited_constructor nm _ t => REF nm <+> name nm <+> type t
    | Eimplicit e | Ebf_glvalue e => expr e
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
    | Sfor os ovd oe1 oe2 s =>
        opt stmt os <+> opt var_decl ovd <+> opt expr oe1 <+> opt expr oe2 <+> stmt s
    | Sswitch os ovd e s =>
        (if s is Sseq b then
           if switch_cases b then OK
           else FAIL "switch: case or default nested in a statement or after a declaration"
         else OK) <+> opt stmt os <+> opt var_decl ovd <+> expr e <+> stmt s
    | Scase _ => OK
    | Sdefault | Sbreak | Scontinue => OK
    | Sreturn oe => opt expr oe
    | Sreturn_nrvo _ e => expr e
    | Sexpr e => expr e
    | Sasm _ _ lpe1 lpe2 _ =>
        FAIL "inline assembly" <+> lst (expr ∘ snd) lpe1 <+> lst (expr ∘ snd) lpe2
    | Sattr _ s => stmt s
    | Slabeled _ s => FAIL "label" <+> stmt s
    | Sgoto _ => FAIL "goto"
    | Sunsupported msg => FAIL msg
    end

  with var_decl (v : VarDecl) : M :=
    match v with
    | Dvar _ t oe =>
        (if q_volatile (decompose_type t).1 then FAIL "volatile object" else OK)
        <+> dtor_of t <+> type t <+> opt expr oe
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
    | Ofunction (Build_Func t args _ _ exc attrs ob) =>
        type t <+> params args <+> lst attr attrs <+> opt function_body ob
        <+> if exc is exception_spec.Unknown
            then match ob with
                 | None => OK
                 | _ => FAIL "unknown exception spec"
                 end
            else OK
    | Omethod m =>
        type m.(m_return) <+> classname m.(m_class)
        <+> params m.(m_params)
        <+> lst attr m.(m_attrs)
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

  (** A default member initializer is walked where it is used: in the
      constructors and aggregate initializations that use it. *)
  Definition member (m : Member) : M :=
    (if drop_qualifiers m.(mem_type) is Tincomplete_array _ then FAIL "flexible array member" else OK)
    <+> type m.(mem_type).

  Definition glob_decl (gd : GlobDecl) : M :=
    match gd with
    | Gunsupported msg => FAIL msg
    | Gtype => OK
    (* Policy: a translation unit with an opaque record is usable, so this
       is not an [Unsupported] gap and [check] accepts it. The record's body
       is not modeled; [o_reason] is the audit trail. *)
    | Gopaque o =>
        PARTIAL ("opaque record (" ++ o.(o_reason) ++ "): only its size, alignment, and destruction are modelled")
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

  (** No extension: the gaps of the semantics only. *)
  Definition no_ext : Expr -> M := fun _ => OK.
End walk.

(** [Unsupported] gaps only. *)
Module check.
  Definition M := list PrimString.string.
  Definition OK : M := [].
  Definition FAIL (msg : PrimString.string) : M := [msg].
  Definition fails (m : walk.M) : M :=
    List.flat_map (fun i => if i is walk.Gap walk.Unsupported msg then [msg] else []) m.

  Definition type t : M := fails (walk.type walk.no_ext t).
  Definition expr e : M := fails (walk.expr walk.no_ext e).
  Definition obj_value o : M := fails (walk.obj_value walk.no_ext o).
  Definition glob_decl gd : M := fails (walk.glob_decl walk.no_ext gd).
  Definition translation_unit tu : M := fails (walk.translation_unit walk.no_ext tu).
  Definition template_unit mtu : M := fails (walk.template_unit walk.no_ext mtu).
End check.

(** ** Per-entity report

    [report.run tu roots] resolves each root in [tu] (with the [cpp.spec] name
    parser); [report.all tu] takes every non-template entity of [tu]. Each
    entry gives:
    - [unsupported]: the entity's own [Unsupported] gaps, including those
      of the builtins it calls directly;
    - [partial]: [Partial] gaps in the entity or in the types it needs, and
      why there is no verdict (["... no verdict ..."]) for a member that
      cpp2v did not elaborate;
    - [blocked_by]: the types it needs (transitively, through fields and bases)
      with [Unsupported] gaps, and these gaps;
    - [unsupported_refs]: the functions and variables it refers to with
      [Unsupported] gaps, except builtins. This is one level only: they do
      not block the entity, whose proof assumes their specs; query them as
      roots to go further.

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

  (** A name the [cpp.spec] printer cannot print (e.g. one with an
      unsupported type) falls back to the human-readable printer, which marks
      unsupported parts with [?]. *)
  Definition print (n : name) : PrimString.string :=
    default (pretty.print_name n) (printer.print_name n).

  Definition partials (m : walk.M) : list PrimString.string :=
    List.flat_map (fun i => if i is walk.Gap walk.Partial msg then [msg] else []) m.

  (** [walk.no_refs] discards needs, never gaps. *)
  Lemma fails_no_refs m : check.fails (walk.no_refs m) = check.fails m.
  Proof. elim: m => [//|[[] ?|?|?|?] m IH] /=; by rewrite IH. Qed.

  Lemma partials_no_refs m : partials (walk.no_refs m) = partials m.
  Proof. elim: m => [//|[[] ?|?|?|?] m IH] /=; by rewrite IH. Qed.

  (** [n] with its [Unsupported] gaps, if any. *)
  Definition named (n : name) (m : walk.M) : list (PrimString.string * list PrimString.string) :=
    if check.fails m is [] then [] else [(print n, check.fails m)].

  (** ** Dropped symbols

      [cpp.prog] drops every symbol whose name may denote several entities
      ([has_unsupportedN]), and records its name in [dropped_symbols]. Each
      gets the verdict "unsupported", since no fact about it is available. *)
  Definition dropped_gap : PrimString.string :=
    "name may denote several entities (it contains an unsupported part): cpp.prog dropped it".

  Definition dropped_entry (input : PrimString.string) (n : name) : entry :=
    mk_entry input (print n) "unsupported" [dropped_gap] [] [] [].

  (** The name parser produces no unsupported part, so a root resolves to the
      dropped name [d] when it agrees with [d] outside [d]'s unsupported parts:
      [matchesN d n]. Other unsupported shapes match only equal names, and
      thus no parsed name. *)
  Fixpoint forallb2 {A B} (f : A -> B -> bool) (xs : list A) (ys : list B) : bool :=
    match xs, ys with
    | [], [] => true
    | x :: xs, y :: ys => f x y && forallb2 f xs ys
    | _, _ => false
    end.

  Definition matchesA (matchesT : type -> type -> bool) (d c : atomic_name) : bool :=
    match d, c with
    | Nunsupported_atomic _, _ => true
    | Nfunction q i ts, Nfunction q' i' ts' =>
        bool_decide (q = q') && bool_decide (i = i') && forallb2 matchesT ts ts'
    | Nctor ts, Nctor ts' => forallb2 matchesT ts ts'
    | Nop q o ts, Nop q' o' ts' =>
        bool_decide (q = q') && bool_decide (o = o') && forallb2 matchesT ts ts'
    | Nop_conv q t, Nop_conv q' t' => bool_decide (q = q') && matchesT t t'
    | Nop_lit i ts, Nop_lit i' ts' => bool_decide (i = i') && forallb2 matchesT ts ts'
    | _, _ => bool_decide (d = c)
    end.

  Fixpoint matchesN (d n : name) {struct d} : bool :=
    match d, n with
    | Nunsupported _, _ => true
    | Ninst d xs, Ninst n ys => matchesN d n && forallb2 matchesTA xs ys
    | Nglobal c, Nglobal c' => matchesA matchesT c c'
    | Nscoped d c, Nscoped n c' => matchesN d n && matchesA matchesT c c'
    | Ndependent d, Ndependent t => matchesT d t
    | _, _ => false
    end
  with matchesTA (d a : temp_arg) {struct d} : bool :=
    match d, a with
    | Aunsupported _, _ => true
    | Atype d, Atype t => matchesT d t
    | Apack ds, Apack xs => forallb2 matchesTA ds xs
    | Atemplate d, Atemplate n => matchesN d n
    | _, _ => bool_decide (d = a)
    end
  with matchesT (d t : type) {struct d} : bool :=
    match d, t with
    | Tunsupported _, _ => true
    | Tptr d, Tptr t
    | Tref d, Tref t
    | Trv_ref d, Trv_ref t
    | Tincomplete_array d, Tincomplete_array t => matchesT d t
    | Tarray d k, Tarray t k' => bool_decide (k = k') && matchesT d t
    | Tqualified q d, Tqualified q' t => bool_decide (q = q') && matchesT d t
    | Tnamed d, Tnamed n
    | Tenum d, Tenum n => matchesN d n
    | Tmember_pointer dc d, Tmember_pointer c t => matchesT dc c && matchesT d t
    | Tfunction (@FunctionType _ cc ar d ds), Tfunction (@FunctionType _ cc' ar' t ts) =>
        bool_decide (cc = cc') && bool_decide (ar = ar') &&
        matchesT d t && forallb2 matchesT ds ts
    | _, _ => bool_decide (d = t)
    end.

  Section with_tu.
    Context (ext : Expr -> walk.M) (tu : translation_unit).

    (** The dropped symbol that [input], parsed as [parsed], names: by its
        [print]ed name, which [all] lists, or by [matchesN]. *)
    Definition find_dropped (input : PrimString.string) (parsed : option name) : option name :=
      List.find (fun d => bool_decide (print d = input) ||
                         from_option (matchesN d) false parsed) tu.(dropped_symbols).

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

    (** The members of an opaque record are not modelled. *)
    Definition opaque_members (m : walk.M) : list PrimString.string :=
      List.flat_map (fun i =>
        if i is walk.Access n then
          if tu.(types) !! n is Some (Gopaque _)
          then ["member access into an opaque record"%pstring]
          else []
        else []) m.

    (** [wp_method] and [wp_ctor] are stuck on [Defaulted] bodies, except
        for a union's defaulted copy/move operations, which copy the object
        representation (see [wp_union_copy] in [logic/func.v]). A
        [Defaulted] body is one cpp2v did not elaborate: clang defines the
        members a translation unit uses (see [walk.or_default]), so its
        definition and verdict are those of a translation unit that uses it. *)
    Definition union_copy_or_move (cls : name) (params : list (ident * type)) : bool :=
      bool_decide (length params = 1) &&
      if tu.(types) !! cls is Some (Gunion _) then true else false.
    Definition not_elaborated : walk.M :=
      walk.PARTIAL "not elaborated: no verdict (cpp2v did not elaborate this defaulted member)".
    Definition defaulted (o : ObjValue) : walk.M :=
      match o with
      | Omethod m =>
        if m.(m_body) is Some Defaulted then
          if union_copy_or_move m.(m_class) m.(m_params) then [] else not_elaborated
        else []
      | Oconstructor c =>
        if c.(c_body) is Some Defaulted then
          if union_copy_or_move c.(c_class) c.(c_params) then [] else not_elaborated
        else []
      | _ => []
      end.

    Definition walk_type (n : name) : walk.M :=
      from_option (walk.glob_decl ext) [] (tu.(types) !! n).

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

    Definition builtin_of (n : name) : option BuiltinFn :=
      if tu.(symbols) !! n is Some (Ofunction f) then
        if f.(f_body) is Some (Builtin b) then Some b else None
      else None.

    Definition direct_builtins (m : walk.M) : list name :=
      List.flat_map (fun i => if i is walk.Bcall n then [n] else []) m.

    (** A builtin called directly has no spec to assume: its gaps are those
        of its callers. A library function that clang treats as a builtin
        is called like any other function. *)
    Definition with_builtins (m : walk.M) : walk.M :=
      let direct := direct_builtins m in
      m ++ List.flat_map (fun r =>
        from_option (if bool_decide (r ∈ direct) then walk.builtin else walk.library_builtin) []
          (builtin_of r)) (refs m).

    (** What the entity [n] itself uses. *)
    Definition own (n : name) : option walk.M :=
      match tu.(symbols) !! n, tu.(types) !! n with
      | Some o, _ => Some (with_builtins (defaulted o ++ walk.obj_value ext o))
      | None, gd => walk.glob_decl ext <$> gd
      end.

    (** The entry for entity [n], which uses [uses] (see [own]), asked for as
        [input]. [fuel] is [closure_fuel], computed once by the caller. *)
    Definition entry_of (fuel : nat) (input : PrimString.string) (n : name) (uses : walk.M) : entry :=
      let needed := List.filter (fun t => bool_decide (t <> n)) (closure fuel (type_refs uses) []) in
      let used := uses ++ List.flat_map walk_type needed in
      let unsupported := check.fails uses ++ remove_dups (opaque_members uses) in
      let blocked_by := List.flat_map (fun t => named t (walk_type t)) needed in
      let partial := remove_dups (partials used ++ union_members used) in
      let unsupported_refs :=
        List.flat_map (fun r =>
          if bool_decide (r = n) || bool_decide (is_Some (builtin_of r)) then [] else from_option (fun o => named r (walk.obj_value ext o)) [] (tu.(symbols) !! r))
          (refs uses) in
      let status :=
        match unsupported, blocked_by, partial with
        | _ :: _, _, _ => "unsupported"
        | [], _ :: _, _ => "blocked"
        | [], [], _ :: _ => "partial"
        | [], [], [] => "supported"
        end%pstring
      in
      mk_entry input (print n) status unsupported partial blocked_by unsupported_refs.

    Definition entry_for (fuel : nat) (input : PrimString.string) : entry :=
      let parsed := parser.parse_name_with tu input in
      if (n ← parsed; pair n <$> own n) is Some (n, uses) then
        entry_of fuel input n uses
      else if find_dropped input parsed is Some d then dropped_entry input d
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

  (** [ext] adds the gaps of a proof tool, see [walk]. *)
  Definition run_with (ext : Expr -> walk.M) (tu : translation_unit) (roots : list PrimString.string) : list entry :=
    List.map (entry_for ext tu (closure_fuel tu)) roots.

  Definition run : translation_unit -> list PrimString.string -> list entry :=
    run_with walk.no_ext.

  (** Every non-template function, variable and type of [tu], named by its
      [print]ed name. Unlike [run], it parses no names, which dominates [run]'s
      time on a large translation unit. Template patterns are left out: each
      instance has its own entry. The symbols that [cpp.prog] dropped are
      unsupported (see [dropped_entry]). *)
  Definition all_with (ext : Expr -> walk.M) (tu : translation_unit) : list entry :=
    let fuel := closure_fuel tu in
    let names := List.map fst (NM.elements tu.(symbols)) ++ List.map fst (NM.elements tu.(types)) in
    List.flat_map (fun n =>
      from_option (fun uses => [entry_of ext tu fuel (print n) n uses]) [] (own ext tu n)) names ++
    List.map (fun n => dropped_entry (print n) n) tu.(dropped_symbols).

  Definition all : translation_unit -> list entry := all_with walk.no_ext.
End report.
