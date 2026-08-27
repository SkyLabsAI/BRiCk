(*
 * Copyright (c) 2024-2025 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import skylabs.lang.cpp.syntax.prelude.
Require Export skylabs.lang.cpp.syntax.preliminary.
Require Export skylabs.lang.cpp.syntax.overloadable.
Require Import skylabs.lang.cpp.syntax.notations.
Require Export skylabs.lang.cpp.syntax.literal_string.
From Stdlib Require Import PrimInt63.

#[local] Set Primitive Projections.

#[local] Notation EqDecision1 T := (∀ (A : Set), EqDecision A -> EqDecision (T A)) (only parsing).
#[local] Notation EqDecision2 T := (∀ (A : Set), EqDecision A -> EqDecision1 (T A)) (only parsing).
#[local] Notation EqDecision3 T := (∀ (A : Set), EqDecision A -> EqDecision2 (T A)) (only parsing).
#[local] Tactic Notation "solve_decision" := intros; solve_decision.

(** ** Naming conventions

    Practically speaking, the entire abstract syntax tree of C++ is mutually recursive
    including names, types, expressions, and statements.

    In some instances, e.g. <<function_type_>> below, we generalize certain type
    constructors in order to expose [Functor] or traversable structure on them.
    When we do this, we name these types with an <_> suffix, e.g. <<function_type_>>.
    The "standard instantiations" of these, e.g. <<function_type_ type>>, are given
    the name without the suffix, e.g. <<Abbreviation function_type := (function_type_ type).>>

    **Historical note**
    Previously, there were also, e.g. <<Expr' : lang.t -> Set>>, which used types to
    distinguish between templated terms (sometimes referred to as "meta terms", see
    [mcore.v]) and normal terms. The use of <lang.t> has been removed, and therefore
    <<'>>d definitions and notations should be removed.
 *)


(** ** Function types *)
(**
TODO: Prefer [function_type] over [functype]. This is complicated by
the several function-like things in the language, with quirky rules
(e.g., member functions may be adorned with qualifiers governing how
<<this>> works and constructors/destructors aren't member functions).
*)
Record function_type_ {decltype : Set} : Set := FunctionType {
  ft_cc : calling_conv;
  ft_arity : function_arity;
  ft_return : decltype;
  ft_params : list decltype;
}.
Add Printing Constructor function_type_.
#[global] Arguments function_type_ : clear implicits.
#[global] Arguments FunctionType {_ _ _} _ _ : assert.
#[global] Instance function_type__inhabited {A : Set} {_ : Inhabited A} : Inhabited (function_type_ A).
Proof. solve_inhabited. Qed.
#[global] Instance function_type__eq_dec {A : Set} {_ : EqDecision A} : EqDecision (function_type_ A).
Proof. solve_decision. Defined.

Module function_type.
  Import UPoly.
  Definition existsb {decltype : Set} (f : decltype -> bool)
      (ft : function_type_ decltype) : bool :=
    f ft.(ft_return) || existsb f ft.(ft_params).

  Definition fmap {decltype decltype' : Set} (f : decltype -> decltype')
    (ft : function_type_ decltype) : function_type_ decltype' :=
    @FunctionType _ ft.(ft_cc) ft.(ft_arity) (f ft.(ft_return)) (f <$> ft.(ft_params)).
  #[global] Arguments fmap _ _ _ & _ : assert.
  #[global] Hint Opaque fmap : typeclass_instances.

  #[universes(polymorphic)]
  Definition traverse@{u | } {F : Set -> Type@{u}} `{!FMap F, !MRet F, AP : !Ap F}
  {decltype decltype' : Set} (f : decltype -> F decltype')
  (ft : function_type_ decltype) : F (function_type_ decltype') :=
    @FunctionType _ ft.(ft_cc) ft.(ft_arity)
                                    <$> f ft.(ft_return) <*> traverse (T:=eta list) f ft.(ft_params).
  #[global] Arguments traverse _ _ _ _ _ _ & _ _ : assert.
  #[global] Hint Opaque traverse : typeclass_instances.
End function_type.

Module function_qualifiers.
  (* This is a compressed tuple.
     - <<l>> means <<&>>
     - <<r>> means <<&&>>
     - <<c>> means <<const>>
     - <<v>> means <<volatile>>
   *)
  Variant t : Set :=
  | N   | Nl   | Nr
  | Nc  | Ncl  | Ncr
  | Nv  | Nvl  | Nvr
  | Ncv | Ncvl | Ncvr.

  Definition is_const (a : t) :=
    match a with
    | Nc | Ncl | Ncr | Ncv | Ncvl | Ncvr => true
    | _ => false
    end.
  Definition is_volatile (a : t) :=
    match a with
    | Nv | Nvl | Nvr | Ncv | Ncvl | Ncvr => true
    | _ => false
    end.

  (* we use [Prvalue] to represent no annotation *)
  Definition vc_of (a : t) : ValCat :=
    match a with
    | N | Nc | Nv | Ncv => Prvalue
    | Nl | Ncl | Nvl | Ncvl => Lvalue
    | Nr | Ncr | Nvr | Ncvr => Xvalue
    end.

  Definition mk (const volatile : bool) (vc : ValCat) : t :=
    match const , volatile , vc with
    | false , false , Prvalue => N
    | false , false , Lvalue => Nl
    | false , false , Xvalue => Nr
    | false , true  , Prvalue => Nv
    | false , true  , Lvalue => Nvl
    | false , true  , Xvalue => Nvr
    | true  , false , Prvalue => Nc
    | true  , false , Lvalue => Ncl
    | true  , false , Xvalue => Ncr
    | true  , true  , Prvalue => Ncv
    | true  , true  , Lvalue => Ncvl
    | true  , true  , Xvalue => Ncvr
    end.

  Definition join (a b : t) : t :=
    mk (is_const a || is_const b) (is_volatile a || is_volatile b)
      match vc_of a , vc_of b with
      | Prvalue , b => b
      | a , Prvalue => a
      | a , _ => a
      end.

  #[global] Instance t_inhabited : Inhabited t.
  Proof. solve_inhabited. Qed.

  #[prefix="", only(tag)] derive t.

  #[local] Definition tag_prim (x : t) : PrimInt63.int :=
    match x with
    | N => 1
    | Nl => 2
    | Nr => 3
    | Nc => 4
    | Ncl => 5
    | Ncr => 6
    | Nv => 7
    | Nvl => 8
    | Nvr => 9
    | Ncv => 10
    | Ncvl => 11
    | Ncvr => 12
    end%uint63.

  Definition compare (a b : t) : comparison :=
    PrimInt63.compare (tag_prim a) (tag_prim b).

  Definition to_type_qualifiers (f : t) : type_qualifiers :=
    match f with
    | N | Nl | Nr => QM
    | Nc | Ncl | Ncr => QC
    | Nv | Nvl | Nvr => QV
    | Ncv | Ncvl | Ncvr => QCV
    end.
End function_qualifiers.

Module cast_style.
  Variant t : Set :=
  | functional
  | c
  | static | dynamic | reinterpret | const.

  #[global] Instance t_eq_dec : EqDecision t.
  Proof. solve_decision. Defined.
  #[global] Instance t_inhabited : Inhabited t.
  Proof. repeat constructor. Qed.

  #[prefix="", only(tag)] derive t.
  Definition compare (a b : t) : comparison :=
    Pos.compare (tag a) (tag b).
End cast_style.

(** ** Structured names *)
Definition loc_info : Set := PrimInt63.int.

(** Atomic names are effectively path components. *)
Inductive atomic_name : Set :=
(** Named things *)
| Nid (_ : ident)	(** namespace, struct, union, typedef, variable, member,
                      and <<extern "C">> symbols... *)
(**
TODO (Discuss): Do we need to distinguish templated functions by their
return types?
*)
| Nfunction (_ : function_qualifiers.t) (_ : ident) (_ : list type)
| Nctor (_ : list type)
| Ndtor
| Nop (_ : function_qualifiers.t) (_ : OverloadableOperator) (_ : list type)
| Nop_conv (_ : function_qualifiers.t) (_ : type)
| Nop_lit (_ : ident) (_ : list type)

(** Unnamed things *)
| Nanon (_ : N)
  (* an anonymous namespace. Specialized b/c they are re-declarable so
     their position is not relevant *)
| Nanonymous
  (* When entities are not named, we use a heuristic that picks the
     first named declaration of the type or the first named field.
     It is important that we distinguish these from [Nid n] because
     [n] is a *type name* while the identifiers in these declarations
     are object names. Effectively in [Nfirst_decl "x"], the name
     of the type is <<decltype(x)>>.
   *)
| Nfirst_decl (_ : ident)
| Nfirst_child (_ : ident)

(** Errors *)
| Nunsupported_atomic (_ : PrimString.string)
| ANLocInfo (_ : loc_info) (_ : atomic_name)

with name : Set :=
| Ninst (c : name) (_ : list temp_arg)
| Nglobal (c : atomic_name)	(* <<::c>> *)
| Ndependent (t : type) (* <<typename t>> *)
| Nscoped (n : name) (c : atomic_name)	(* <<n::c>> *)
| Nunsupported (_ : PrimString.string)
| NLocInfo (_ : loc_info) (_ : name)

(** Template arguments
    - <<int>> would be represented as [Atype Tint]
    - <<1>> would be represented as [Avalue (Eint 1 Tint)]
    - <<int, char>> as the instantiation of a template parameter pack
      would be represented as [Apack [Atype Tint; Atype Tchar]].
      C++ requires these to be uniform, i.e. you can not mix [Avalue] and [Atype].
      We can enforce this if we want in the future.
    - <<T>> for <<T>> of template type would be represented as [Atemplate T]
    - <<T>> for <<T>> of template-template parameter would be represented
      as [Atemplate_param "T"]

    TODO: [Atemplate_param] could be removed if we had a [name] constructor
          that could represent a parameter. It's possible that we could capture
          this with [Ndependent (Tparam "T")].
          "T" is not a type, but it is a type-level name.
 *)
with temp_arg : Set :=
| Atype (_ : type)
| Avalue (_ : Expr)
| Apack (_ : list temp_arg) (* See <https://en.cppreference.com/w/cpp/language/pack> *)
| Atemplate (_ : name)
| Atemplate_param (_ : ident)
| Aunsupported (_ : PrimString.string)
| ALocInfo (_ : loc_info) (_ : temp_arg)

(** ** Types *)
(**
NOTE: We could eliminate [Tresult_unop], [Tresult_binop] using
[Tresult_call] because the evaluation order distinction between
operators and operator calls does not matter for typing purposes. We
do things this way for consistency, and to keep the components of
substitutions small.
*)

with type : Set :=
| Tparam (_ : ident)
| Tresult_param (_ : ident)
| Tresult_global (on : name)
| Tresult_unop (_ : RUnOp) (_ : type)
| Tresult_binop (_ : RBinOp) (_ _ : type)
| Tresult_call (on : name) (_ : list type)
| Tresult_member_call (on : name) (_ : type) (_ : list type)
| Tresult_parenlist (_ :type) (_ : list type)
| Tresult_member (_ : type) (_ : name)
| Tauto (* this is a place-holder type *)

| Tptr (t : type)
| Tref (t : type)
| Trv_ref (t : type)
| Tnum (sz : int_rank.t) (sgn : signed)
| Tchar_ (_ : char_type.t)
| Tvoid
| Tarray (t : type) (n : N)
| Tincomplete_array (t : type)
| Tvariable_array (t : type) (e : Expr)
| Tnamed (gn : name)
| Tenum (gn : name)
| Tfunction (t : function_type_ type)
| Tbool
| Tmember_pointer (gn : (* classname *)type) (t : type)
| Tfloat_ (_ : float_type.t)
| Tqualified (q : type_qualifiers) (t : type)
| Tnullptr
| Tarch (osz : option bitsize) (name : PrimString.string)
| Tdecltype (_ : Expr)
  (* ^^ this is <<decltype(e)>> when <<e>> is an expression, including a parenthesized expression.
     (2) in <https://en.cppreference.com/w/cpp/language/decltype>
   *)
| Texprtype (_ : Expr)
  (* ^^ this is <<decltype(e)>> when <<e>> is a variable reference
     (1) in <https://en.cppreference.com/w/cpp/language/decltype>
   *)
| Tunsupported (_ : PrimString.string)
| TLocInfo (_ : loc_info) (_ : type)

(** ** Expressions *)
(**
NOTE: We need both unresolved operators and unresolved calls because
operators like <<a = b>> use a different evaluation order than calls
like <<operator=(a, b)>>.

We use the [Eunresolved_] prefix for constructors whose C++ meaning is
deferred to template substitution.
*)
with Expr : Set :=
| Eparam (_ : ident)
| Eunresolved_global (_ : name)
| Eunresolved_sizeof_pack (_ : ident) (t : type)
| Eunresolved_unop (_ : RUnOp) (e : Expr)
| Eunresolved_binop (_ : RBinOp) (l r : Expr)
| Eunresolved_call (on : name) (_ : list Expr)
| Eunresolved_member_call (on : name) (_ : Expr) (_ : list Expr)
(**
<<Eunresolved_parenlist (Some T) [arg1;…;argN]>> is the initializer
for an uninstantiated direct initializer list declaration <<T
var(arg1,…,argN)>> with dependent type <<T>>. Making the type optional
simplifies cpp2v---we set it from context in ../mparser.v.
*)
| Eunresolved_parenlist (_ : option type) (_ : list Expr)
| Eunresolved_initlist (_ : option type) (_ : list Expr)
| Eunresolved_member (_ : Expr) (_ : name)
| Eunresolved_string_literal (character_type : type)

(**
NOTE: We might need to support template parameters as object names in
a few constructors (by carrying <<Expr ≈ Eparam + Eglobal>> instead of
<<name>>).
*)

| Evar (_ : localname) (_ : type)
| Eenum_const (gn : name) (_ : ident)
| Eglobal (on : name) (_ : type)
(**
[Eglobal_member gn t] represents <<&gn>> where <<gn>>
is a non-static member of a class, e.g. a field or method.
We distinguish this from [Eaddrof (Eglobal gn)] because,
when [gn] refers to a member, <<&gn>> is not a well-formed
program because, in part, C++ has no type for references to members.
*)
| Eglobal_member (gn : name) (ty : type)

| Echar (c : N) (t : type)
| Estring (s : literal_string.t) (t : type)
| Eint (n : Z) (t : type)
| Ebool (b : bool)
| Efloat (ft : float_type.t) (_ : float_type.car ft)
| Eunop (op : UnOp) (e : Expr) (t : type)
| Ebinop (op : BinOp) (e1 e2 : Expr) (t : type)
| Ederef (e : Expr) (t : type)
| Eaddrof (e : Expr)
| Eassign (e1 e2 : Expr) (t : type)
| Eassign_op (op : BinOp) (e1 e2 : Expr) (t : type)
| Epreinc (e : Expr) (t : type)
| Epostinc (e : Expr) (t : type)
| Epredec (e : Expr) (t : type)
| Epostdec (e : Expr) (t : type)
| Eseqand (e1 e2 : Expr)
| Eseqor (e1 e2 : Expr)
| Ecomma (e1 e2 : Expr)
| Ecall (f : Expr) (es : list Expr)
| Eexplicit_cast (c : cast_style.t) (_ : type) (e : Expr)
| Ecast (c : Cast) (e : Expr)
| Emember (arrow : bool) (obj : Expr) (f : atomic_name) (mut : bool) (t : type)
| Emember_ignore (arrow : bool) (obj : Expr) (res : Expr)
| Emember_call (arrow : bool) (method : MethodRef_ name type Expr) (obj : Expr) (args : list Expr)
| Eoperator_call (_ : OverloadableOperator) (_ : operator_impl.t name type) (_ : list Expr)
| Esubscript (e1 : Expr) (e2 : Expr) (t : type)
| Esizeof (_ : type + Expr) (t : type)
| Ealignof (_ : type + Expr) (t : type)
(**
NOTE: [Eoffsetof] carries a type instead of a name to support
dependent types.
Should be [gn : classname]
*)
| Eoffsetof (gn : type) (_ : ident) (t : type)
| Econstructor (on : name) (args : list Expr) (t : type)
| Einherited_constructor (on : name) (args : list ident) (t : type)
  (* ^^ this is a direct dispatch constructor and can not be represented within C++ itself.
     Morally, this looks like the following:
     <<
     struct DATA {};
     struct C {
       DATA d;
     };
     struct D : C {
        using C::C;
        // sketch implementation of the inherited constructor
        D(DATA x):C(x) {} // << no separate constructor for C is called here, the arguments are used
                          //    directly from the function. In BRiCk's interpretation, the arguments
                          //    are pre-materialized
     };
     >>
   *)
| Elambda (_ : name) (captures : list Expr)
| Eimplicit (e : Expr)
| Eimplicit_init (t : type)
| Eif (e1 e2 e3 : Expr) (t : type)
| Eif2  (n : N) (common cond thn els : Expr) (_ : type)
| Ethis (t : type)
| Enull
| Einitlist (args : list Expr) (default : option Expr) (t : type)
| Einitlist_union (_ : atomic_name) (_ : option Expr) (t : type)

| Enew (new_fn : name * type) (new_args : list Expr) (pass_align : new_form)
  (alloc_ty : type) (array_size : option Expr) (init : option Expr)
| Edelete (is_array : bool) (del_fn : name) (arg : Expr) (deleted_type : type)
| Eandclean (e : Expr)
| Ematerialize_temp (e : Expr) (vc : ValCat)
  (* ^^ [Ematerialize_temp] is can be an lvalue in the following program:
     <<
     int x[10];
     static_cast<int*const&>(x);
     >>
     (this is true at least in c++11)
   *)
| Eatomic (op : AtomicOp) (args : list Expr) (t : type)
| Estmt (_ : Stmt) (_ : type)
| Eva_arg (e : Expr) (t : type)
  (**
  TODO: We may have to adjust cpp2v: Either [Eva_arg] should carry a
  decltype, or [valcat_of] in cpp2v-core and [decltype.of_expr] here
  are unnecessarily complicated.

  TODO: [Eva_arg _ Tdependent]

  Docs for <<__builtin_va_arg>>.
  https://clang.llvm.org/docs/LanguageExtensions.html#builtin-functions
  *)
| Epseudo_destructor (is_arrow : bool) (t : type) (e : Expr)
| Earrayloop_init (oname : N) (src : Expr) (level : N) (length : N) (init : Expr) (t : type)
| Earrayloop_index (level : N) (t : type)
| Eopaque_ref (name : N) (t : type)
| Eunsupported (s : PrimString.string) (t : type)
| ELocInfo (_ : loc_info) (_ : Expr)

with Stmt : Set :=
| Sseq    (_ : list Stmt)
| Sdecl   (_ : list VarDecl)

| Sif     (init : option Stmt) (decl : option VarDecl) (test : Expr) (thn els : Stmt)
  (* ^^ if (init; decl) { ... } else { ... }
     the test is the expressions
   *)
| Sif_consteval (_ _ : Stmt)

| Swhile  (_ : option VarDecl) (_ : Expr) (_ : Stmt)
| Sfor    (_ : option Stmt) (_ : option Expr) (_ : option Expr) (_ : Stmt)
| Sdo     (_ : Stmt) (_ : Expr)

| Sswitch (_ : option Stmt) (_ : option VarDecl) (_ : Expr) (_ : Stmt)
| Scase   (_ : SwitchBranch)
| Sdefault

| Sbreak
| Scontinue

| Sreturn (_ : option Expr)

| Sexpr   (_ : Expr)

| Sattr (_ : list ident) (_ : Stmt)

| Sasm (_ : PrimString.string) (volatile : bool)
       (inputs : list (ident * Expr))
       (outputs : list (ident * Expr))
       (clobbers : list ident)

| Slabeled (_ : ident) (_ : Stmt)
| Sgoto (_ : ident)
| Sunsupported (_ : PrimString.string)
| SLocInfo (_ : loc_info) (_ : Stmt)

with VarDecl : Set :=
| Dvar (name : localname) (_ : type) (init : option Expr)
| Ddecompose (_ : Expr) (anon_var : ident) (_ : list BindingDecl)
  (* initialization of a function-local [static]. See https://eel.is/c++draft/stmt.dcl#3 *)
| Dinit (thread_safe : bool) (name : name) (_ : type) (init : option Expr)
| DLocInfo (_ : loc_info) (_ : VarDecl)

with BindingDecl : Set :=
| Bvar (name : localname) (_ : type) (init : Expr)
| Bbind (name : localname) (_ : type) (init : Expr)
| BLocInfo (_ : loc_info) (_ : BindingDecl)

(** ** Casts *)
with Cast : Set :=
| Cdependent (_ : type)
| Cbitcast (_ : type)
| Clvaluebitcast	(_ : type) (** TODO (FM-3431): Drop this constructor? *)
| Cl2r
| Cl2r_bitcast (_ : type)
| Cnoop (_ : type)
| Carray2ptr
| Cfun2ptr
| Cint2ptr (_ : type)
| Cptr2int (_ : type)
| Cptr2bool
| Cintegral (_ : type)
| Cint2bool
| Cfloat2bool
| Cfloat2int (_ : type)
| Cint2float (_ : type)
| Cfloat (_ : type) (* conversion between floating point types *)
| Cnull2ptr (_ : type)
| Cnull2memberptr (_ : type)
| Cbuiltin2fun (_ : type) (* OPTIMIZABLE? *)
| C2void

  (* These are just annotations on the underlying expression *)
| Cctor (_ : type)
| Cuser (* this is an annotation, the actual member call is the child node *)
| Cdynamic     (to : type)
| Cderived2base (path : list type) (END : type)
| Cbase2derived (path : list type) (END : type)
(* If the sub-expression has type <START> then the arguments of
   [Cderived2base] and [Cbase2derived] contain the path between
   <START> and <END> from derived class to base class.
   For example, with
     ```c++
     class A {};
     class B : public A {};
     class C : public B {};
     class D : public C {};
     ```
     A cast from <<D>> to <<A>> will be [Cderived2base ["C";"B"] "A"].
     - <<C>> comes from the type of the sub-expression.
     A cast from <<A>> to <<D>> will be [Cbase2derived ["C";"B"] "D"].
     - <<A>> comes from the type of the sub-expression.
 *)
| Cunsupported (_ : bs) (_ : type)
.

(** Template parameters
    - <<typename T>> would be represented as [Ptype "T"]
    - <<int X>> would be represented as [Pvalue "X" Tint]
    - <<template <typename T> class C>> would be represented as
      [Ptemplate "C" [Ptype "T"]]

    <<typename T...>> and <<int X...>> are not currently supported.
 *)
Inductive temp_param : Set :=
| Ptype (_ : ident)
| Pvalue (_ : ident) (_ : type)
| Ptemplate (_ : ident) (_ : list temp_param)
| Punsupported (_ : PrimString.string).

#[global] Arguments atomic_name : clear implicits.
#[global] Arguments Cast : clear implicits.
#[global] Arguments name : clear implicits.
#[global] Arguments temp_arg : clear implicits.
#[global] Arguments temp_param : clear implicits.
#[global] Arguments type : clear implicits.
#[global] Arguments Expr : clear implicits.
#[global] Arguments VarDecl : clear implicits.
#[global] Arguments BindingDecl : clear implicits.
#[global] Arguments Stmt : clear implicits.

(** Remove only leading location-information wrappers.  Unlike the recursive
    [erase_*] functions below, these functions do not traverse the whole AST.
    [drop_loc_info] looks through leading qualifiers so that locations and
    qualifiers can be normalized independently. *)
Fixpoint drop_atomic_name_loc_info (an : atomic_name) : atomic_name :=
  match an with
  | ANLocInfo _ an => drop_atomic_name_loc_info an
  | _ => an
  end.

Fixpoint drop_name_loc_info (n : name) : name :=
  match n with
  | NLocInfo _ n => drop_name_loc_info n
  | _ => n
  end.

Fixpoint drop_temp_arg_loc_info (arg : temp_arg) : temp_arg :=
  match arg with
  | ALocInfo _ arg => drop_temp_arg_loc_info arg
  | _ => arg
  end.

Fixpoint drop_loc_info (t : type) : type :=
  match t with
  | TLocInfo _ t => drop_loc_info t
  | Tqualified cv t => Tqualified cv (drop_loc_info t)
  | _ => t
  end.

Fixpoint drop_expr_loc_info (e : Expr) : Expr :=
  match e with
  | ELocInfo _ e => drop_expr_loc_info e
  | _ => e
  end.

Fixpoint drop_stmt_loc_info (s : Stmt) : Stmt :=
  match s with
  | SLocInfo _ s => drop_stmt_loc_info s
  | _ => s
  end.

Fixpoint drop_var_decl_loc_info (d : VarDecl) : VarDecl :=
  match d with
  | DLocInfo _ d => drop_var_decl_loc_info d
  | _ => d
  end.

Fixpoint drop_binding_decl_loc_info (d : BindingDecl) : BindingDecl :=
  match d with
  | BLocInfo _ d => drop_binding_decl_loc_info d
  | _ => d
  end.

Lemma drop_loc_info_idemp t : drop_loc_info (drop_loc_info t) = drop_loc_info t.
Proof. by induction t; cbn; auto; rewrite IHt. Qed.

#[global] Arguments drop_atomic_name_loc_info !_ / : simpl nomatch, assert.
#[global] Arguments drop_name_loc_info !_ / : simpl nomatch, assert.
#[global] Arguments drop_temp_arg_loc_info !_ / : simpl nomatch, assert.
#[global] Arguments drop_loc_info !_ / : simpl nomatch, assert.
#[global] Arguments drop_expr_loc_info !_ / : simpl nomatch, assert.
#[global] Arguments drop_stmt_loc_info !_ / : simpl nomatch, assert.
#[global] Arguments drop_var_decl_loc_info !_ / : simpl nomatch, assert.
#[global] Arguments drop_binding_decl_loc_info !_ / : simpl nomatch, assert.

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
  | TLocInfo _ t => erase_type t
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

#[global] Bind Scope cpp_name_scope with name.

Module atomic_name.
  Definition existsb (f : type -> bool) (c : atomic_name) : bool :=
    match drop_atomic_name_loc_info c with
    | Nid _ => false
    | Nfunction _ _ ts => List.existsb f ts
    | Nctor ts => List.existsb f ts
    | Ndtor => false
    | Nop _ _ ts => List.existsb f ts
    | Nop_conv _ t => f t
    | Nop_lit _ ts => List.existsb f ts
    | Nanon _
    | Nanonymous
    | Nfirst_decl _
    | Nfirst_child _
    | Nunsupported_atomic _
    | ANLocInfo _ _ => false
    end.

  Import UPoly.

  Fixpoint fmap (f : type -> type) (c : atomic_name) : atomic_name :=
    match c with
    | Nid id => Nid id
    | Nfunction qs n ts => Nfunction qs n (f <$> ts)
    | Nctor ts => Nctor (f <$> ts)
    | Ndtor => Ndtor
    | Nop q oo ts => Nop q oo (f <$> ts)
    | Nop_conv n t => Nop_conv n $ f t
    | Nop_lit n ts => Nop_lit n $ f <$> ts
    | Nanon n => Nanon n
    | Nanonymous => Nanonymous
    | Nfirst_decl n => Nfirst_decl n
    | Nfirst_child n => Nfirst_child n
    | Nunsupported_atomic msg => Nunsupported_atomic msg
    | ANLocInfo li c => ANLocInfo li (fmap f c)
    end.
  #[global] Arguments fmap _ & _ : assert.

  Section traverse.
    #[local] Set Universe Polymorphism.
    #[local] Unset Auto Template Polymorphism.
    #[local] Unset Universe Minimization ToSet.
    Universe u.
    Context {F : Set -> Type@{u}} `{!FMap F, !MRet F, AP : !Ap F}.
    Context (f : type -> F type).

    #[local] Notation list_traverse := (UPoly.traverse (T:=eta list)).
    Fixpoint traverse (c : atomic_name) : F atomic_name :=
      match c with
      | Nid id => mret $ Nid id
      | Nfunction qs n ts => Nfunction qs n <$> list_traverse f ts
      | Nctor ts => Nctor <$> list_traverse f ts
      | Ndtor => mret Ndtor
      | Nop q oo ts => Nop q oo <$> list_traverse f ts
      | Nop_conv n t => Nop_conv n <$> f t
      | Nop_lit n ts => Nop_lit n <$> list_traverse f ts
      | Nanon n => mret $ Nanon n
      | Nanonymous => mret Nanonymous
      | Nfirst_decl n => mret $ Nfirst_decl n
      | Nfirst_child n => mret $ Nfirst_child n

      | Nunsupported_atomic msg => mret $ Nunsupported_atomic msg
      | ANLocInfo li c => ANLocInfo li <$> traverse c
      end.
    #[global] Hint Opaque traverse : typeclass_instances.
  End traverse.

End atomic_name.

Module temp_param.
  Import UPoly.
  Fixpoint existsb (f : type -> bool) (p : temp_param) : bool :=
    match p with
    | Ptype _ => false
    | Pvalue _ t => f t
    | Ptemplate _ ps => List.existsb (existsb f) ps
    | Punsupported _ => false
    end.

  Fixpoint fmap (f : type -> type) (p : temp_param) : temp_param :=
    match p with
    | Ptype id => Ptype id
    | Pvalue id t => Pvalue id (f t)
    | Ptemplate id ps => Ptemplate id (List.map (fmap f) ps)
    | Punsupported msg => Punsupported msg
    end.
  #[global] Arguments fmap _ & _ : assert.
  #[global] Hint Opaque fmap : typeclass_instances.

  Section traverse.
    #[local] Set Universe Polymorphism.
    #[local] Unset Auto Template Polymorphism.
    #[local] Unset Universe Minimization ToSet.
    Universe u.
    Context {F : Set -> Type@{u}} `{!FMap F, !MRet F, AP : !Ap F}.
    Context (f : type -> F type).

    Fixpoint traverse (p : temp_param) : F temp_param :=
      match p with
      | Ptype id => mret $ Ptype id
      | Pvalue id t => Pvalue id <$> f t
      | Ptemplate id ps =>
          Ptemplate id <$> UPoly.traverse (T:=eta list) (F:=F) traverse ps
      | Punsupported msg => mret $ Punsupported msg
      end.
    #[global] Hint Opaque traverse : typeclass_instances.
  End traverse.

End temp_param.

(** The representation of applied template type parameters,
    e.g.
    <<
    template<template<typename T> U> f() { U<int> ... };
    >>
    This notation effectively has type
    [[
    Tparam_inst : ident -> list temp_arg -> type
    ]]

    TODO: It might be desireable to promote this to a new constructor
 *)
Abbreviation Tparam_inst n args :=
  (Tnamed (Ninst (Ndependent (Tparam n)) args)).


#[global] Instance type_inhabited : Inhabited type.
Proof. solve_inhabited. Qed.
#[global] Instance atomic_name_inhabited : Inhabited atomic_name.
Proof. solve_inhabited. Qed.
#[global] Instance temp_param_inhabited : Inhabited temp_param.
Proof. solve_inhabited. Qed.
#[global] Instance Expr_inhabited : Inhabited Expr.
Proof. solve_inhabited. Qed.
#[global] Instance name_inhabited : Inhabited name.
Proof. apply populate, Nglobal, inhabitant. Qed.
#[global] Instance temp_arg_inhabited : Inhabited temp_arg.
Proof. apply populate, Atype, inhabitant. Qed.
#[global] Instance VarDecl_inhabited : Inhabited VarDecl.
Proof. solve_inhabited. Qed.
#[global] Instance BindingDecl_inhabited : Inhabited BindingDecl.
Proof. solve_inhabited. Qed.
#[global] Instance Stmt_inhabited : Inhabited Stmt.
Proof. apply populate, Sseq, nil. Qed.
#[global] Instance Cast_inhabited : Inhabited Cast.
Proof. apply populate, C2void. Qed.

#[global] Reserved Notation "x .:: y" (left associativity, at level 61).
(* Maybe not this one *)
(* #[global] Notation "x .:: y" := (Nscoped x%cpp_type (Nid y%pstring)) : cpp_type_scope. *)

#[global] Notation "x .:: y" := (Nscoped x%cpp_name y) : cpp_name_scope.
#[global] Notation "x .:: y" := (Nscoped x%cpp y) : cpp_scope.
#[global] Notation "x .:: y" := (Nscoped x%cpp_field y) : cpp_field_scope.

(* Notation to insert parameters inside names *)
#[global] Reserved Notation "p .<< a0 , .. , an >>"
  (at level 61, left associativity, format "p  .<<  a0 ,  .. ,  an  >>").

#[global] Notation "p .<< a0 , .. , an >>" := (Ninst p (@cons temp_arg a0 ( .. (@cons temp_arg an nil) .. )) ) : cpp_field_scope.
#[global] Notation "p .<< a0 , .. , an >>" := (Ninst p (@cons temp_arg a0 ( .. (@cons temp_arg an nil) .. )) ) : cpp_scope.
#[global] Notation "p .<< a0 , .. , an >>" := (Ninst p (@cons temp_arg a0 ( .. (@cons temp_arg an nil) .. )) ) : cpp_name_scope.
(* Maybe not this one *)
(* #[global] Notation "p .<< a0 , .. , an >>" := (Ninst p (@cons temp_arg a0 ( .. (@cons temp_arg an nil) .. )) ) : cpp_type_scope. *)


Module Cast.
  Definition existsb
    (T : type -> bool)
    (c : Cast) : bool :=
    match c with
    | Cdependent t
    | Cbitcast t
    | Clvaluebitcast t => T t
    | Cl2r => false
    | Cl2r_bitcast t => T t
    | Cnoop t => T t
    | Carray2ptr
    | Cfun2ptr => false
    | Cint2ptr t
    | Cptr2int t => T t
    | Cptr2bool => false
    | Cderived2base path t
    | Cbase2derived path t => List.existsb T path || T t
    | Cintegral t => T t
    | Cint2bool => false
    | Cfloat2bool => false
    | Cfloat2int t
    | Cint2float t
    | Cfloat t
    | Cnull2ptr t
    | Cnull2memberptr t
    | Cbuiltin2fun t
    | Cctor t => T t
    | C2void => false
    | Cuser => false
    | Cdynamic t => T t
    | Cunsupported _ t => T t
    end.

End Cast.

Definition is_implicit (e : Expr) : bool :=
  if e is Eimplicit _ then true else false.

Definition globname := name.	(** Type names *)
#[global] Bind Scope cpp_name_scope with globname.
Definition obj_name := name.	(** Function, data names *)
#[global] Bind Scope cpp_name_scope with obj_name.

Definition exprtype := type.	(** An expression's non-reference type *)
#[global] Bind Scope cpp_type_scope with exprtype.
Definition decltype := type.	(** Types as used in declarations (≈ ValCat × exprtype) *)
#[global] Bind Scope cpp_type_scope with decltype.
Definition functype := type.	(** Must be [Tfunction] *)
#[global] Bind Scope cpp_type_scope with functype.


Definition integral_type_to_type (v : integral_type.t) : type :=
  Tnum v.(integral_type.size) v.(integral_type.signedness).
Coercion integral_type_to_type : integral_type.t >-> type.

Notation Nenum_const gn id := (Nscoped gn (Nid id)) (only parsing).

Notation function_type := (function_type_ decltype).

(**
In certain places, C++ requires a class name,
for example, for base classes.
In templates, these names do not have to be resolved, e.g. in CRTP.
<<
template<typename T>
struct Foo : T { };
>>
*)
Notation classname := name (only parsing).

(** ** C++ with structured names *)
Notation operator_impl := (operator_impl.t obj_name type).
Notation MethodRef := (MethodRef_ obj_name functype Expr).

Module field_name.
  Definition t := atomic_name.
  Definition Id : ident -> t := Nid.
  Definition Anon : _ -> t := Nanon.
  Definition CaptureVar : ident -> t := Nid.
  Definition CaptureThis : t := Nid ".this".
End field_name.
Notation field_name := field_name.t.

(*
#[global] Instance field_name_inh : Inhabited field_name.t.
Proof. rewrite /field_name.t. refine _. Defined.
#[global] Instance field_name_eq_dec : EqDecision field_name.t.
Proof. rewrite /field_name.t. refine _. Defined.
#[global] Hint Opaque field_name.t : typeclass_instances.
*)

Notation field := name (only parsing).
Notation Field := Nscoped (only parsing).
Definition f_type (t : field) : globname :=
  match t with
  | Nscoped n _ => n
  | _ => Nunsupported "not a field"
  end.
Definition f_name (t : field) : atomic_name :=
  match t with
  | Nscoped _ n => n
  | _ => Nunsupported_atomic "not a field"
  end.

Definition Ndependent' (t : type) : classname :=
  match t with
  | Tnamed nm => nm
  | Tenum nm => nm
  | _ => Ndependent t
  end.
Lemma Ndependent'_Tnamed x :
  Ndependent' (Tnamed x) = x.
Proof. done. Qed.

Definition Tnamed' (n : name) : type :=
  match n with
  | Ndependent t => t
  | _ => Tnamed n
  end.
Lemma Tnamed'_Ndependent x :
  Tnamed' (Ndependent x) = x.
Proof. done. Qed.


(* Lemma Tnamed_Ndependent' x : *)
(*   Tnamed (Ndependent' x) = x. *)
(* Proof. case: x => //=. try done. Qed. *)

Definition Field'' (t : type) (c : field_name.t) : field :=
  Nscoped (Ndependent' t) c.


(** ** Derived forms *)
Notation Tconst_volatile := (Tqualified QCV).
Notation Tconst := (Tqualified QC).
Notation Tvolatile := (Tqualified QV).
Notation Tmut := (Tqualified QM).
Notation Tmut_volatile := Tvolatile (only parsing).

Notation Tchar := (Tchar_ char_type.Cchar).
Notation Twchar := (Tchar_ char_type.Cwchar).
Notation Tchar8 := (Tchar_ char_type.C8).
Notation Tchar16 := (Tchar_ char_type.C16).
Notation Tchar32 := (Tchar_ char_type.C32).

#[deprecated(since="20240624", note="use [Tschar].")]
Notation Ti8 := (Tnum int_rank.Ichar Signed) (only parsing).
#[deprecated(since="20240624", note="use [Tuchar].")]
Notation Tu8 := (Tnum int_rank.Ichar Unsigned) (only parsing).
#[deprecated(since="20240624", note="use [Tshort].")]
Notation Ti16 := (Tnum int_rank.Ishort Signed) (only parsing).
#[deprecated(since="20240624", note="use [Tushort].")]
Notation Tu16 := (Tnum int_rank.Ishort Unsigned) (only parsing).
#[deprecated(since="20240624", note="use [Tint].")]
Notation Ti32 := (Tnum int_rank.Iint Signed) (only parsing).
#[deprecated(since="20240624", note="use [Tuint].")]
Notation Tu32 := (Tnum int_rank.Iint Unsigned) (only parsing).
#[deprecated(since="20240624", note="use [Tlong] or [Tlonglong].")]
Notation Ti64 := (Tnum int_rank.Ilonglong Signed) (only parsing).
#[deprecated(since="20240624", note="use [Tulong] or [Tulonglong].")]
Notation Tu64 := (Tnum int_rank.Ilonglong Unsigned) (only parsing).
#[deprecated(since="20240624", note="use [Tint128_t].")]
Notation Ti128 := (Tnum int_rank.I128 Signed) (only parsing).
#[deprecated(since="20240624", note="use [Tuint128_t].")]
Notation Tu128 := (Tnum int_rank.I128 Unsigned) (only parsing).

Notation Tschar := (Tnum int_rank.Ichar Signed).
Notation Tuchar := (Tnum int_rank.Ichar Unsigned).

Notation Tushort := (Tnum int_rank.Ishort Unsigned).
Notation Tshort := (Tnum int_rank.Ishort Signed).

Notation Tint := (Tnum int_rank.Iint Signed).
Notation Tuint := (Tnum int_rank.Iint Unsigned).

Notation Tulong := (Tnum int_rank.Ilong Unsigned) (only parsing).
Notation Tlong := (Tnum int_rank.Ilong Signed) (only parsing).

Notation Tulonglong := (Tnum int_rank.Ilonglong Unsigned).
Notation Tlonglong := (Tnum int_rank.Ilonglong Signed).

Notation Tuint128_t := (Tnum int_rank.I128 Unsigned).
Notation Tint128_t := (Tnum int_rank.I128 Signed).

Notation Tfloat16 := (Tfloat_ float_type.Ffloat16).
Notation Tfloat := (Tfloat_ float_type.Ffloat).
Notation Tdouble := (Tfloat_ float_type.Fdouble).
Notation Tlongdouble := (Tfloat_ float_type.Flongdouble).
Notation Tfloat128 := (Tfloat_ float_type.Ffloat128).

Notation Twchar_t := (Tchar_ char_type.Cwchar).
Notation Tchar8_t := (Tchar_ char_type.C8).
Notation Tchar16_t := (Tchar_ char_type.C16).
Notation Tchar32_t := (Tchar_ char_type.C32).

(* TODO: This is determined by the compiler. *)
Notation Tsize_t := Tulong (only parsing).
(* NOTE Use [Tbyte] when talking about the offsets for "raw bytes" *)
Notation Tbyte := (Tnum int_rank.Ichar Unsigned) (only parsing).


(** ** Dependent names, types, and terms *)
Fixpoint is_dependentN (n : name) : bool :=
  match n with
  | Ninst n xs => is_dependentN n || existsb is_dependentTA xs
  | Nglobal c => atomic_name.existsb is_dependentT c
  | Ndependent t => is_dependentT t
  | Nscoped n c => is_dependentN n || atomic_name.existsb is_dependentT c
  | Nunsupported _ => false
  | NLocInfo _ n => is_dependentN n
  end

with is_dependentTA (t : temp_arg) : bool :=
  match t with
  | Atype t => is_dependentT t
  | Avalue e => is_dependentE e
  | Apack tas => List.existsb is_dependentTA tas
  | Atemplate nm => is_dependentN nm
  | Atemplate_param _ => false
  | Aunsupported _ => false
  | ALocInfo _ t => is_dependentTA t
  end

with is_dependentT (t : type) : bool :=
  match t with
  | Tparam _
  | Tresult_param _
  | Tresult_global _
  | Tresult_unop _ _
  | Tresult_binop _ _ _
  | Tresult_call _ _
  | Tresult_member_call _ _ _
  | Tresult_parenlist _ _ => true
  | Tresult_member _ _ => true
  | Tauto => true
  | Tptr t
  | Tref t
  | Trv_ref t => is_dependentT t
  | Tnum _ _
  | Tchar_ _
  | Tvoid => false
  | Tarray t _
  | Tincomplete_array t => is_dependentT t
  | Tvariable_array t e => is_dependentT t || is_dependentE e
  | Tnamed n
  | Tenum n => is_dependentN n
  | Tfunction ft => function_type.existsb is_dependentT ft
  | Tbool => false
  | Tmember_pointer gn t => is_dependentT gn || is_dependentT t
  | Tfloat_ _ => false
  | Tqualified _ t => is_dependentT t
  | Tnullptr
  | Tarch _ _ => false
  | Tdecltype e => is_dependentE e
  | Texprtype e => is_dependentE e
  | Tunsupported _ => false
  | TLocInfo _ t => is_dependentT t
  end

with is_dependentE (e : Expr) : bool :=
  match e with
  | Eparam _
  | Eunresolved_global _
  | Eunresolved_sizeof_pack _ _
  | Eunresolved_unop _ _
  | Eunresolved_binop _ _ _
  | Eunresolved_call _ _
  | Eunresolved_member_call _ _ _
  | Eunresolved_parenlist _ _
  | Eunresolved_initlist _ _
  | Eunresolved_member _ _ => true
  | Evar _ t => is_dependentT t
  | Eenum_const n _ => is_dependentN n
  | Eglobal n t => is_dependentN n || is_dependentT t
  | Eglobal_member n t => is_dependentN n || is_dependentT t
  | Echar _ t
  | Estring _ t
  | Eunresolved_string_literal t
  | Eint _ t => is_dependentT t
  | Ebool _
  | Efloat _ _ => false
  | Eunop _ e t => is_dependentE e || is_dependentT t
  | Ebinop _ e1 e2 t => is_dependentE e1 || is_dependentE e2 || is_dependentT t
  | Ederef e t => is_dependentE e || is_dependentT t
  | Eaddrof e => is_dependentE e
  | Eassign e1 e2 t => is_dependentE e1 || is_dependentE e2 || is_dependentT t
  | Eassign_op _ e1 e2 t => is_dependentE e1 || is_dependentE e2 || is_dependentT t
  | Epreinc e t => is_dependentE e || is_dependentT t
  | Epostinc e t => is_dependentE e || is_dependentT t
  | Epredec e t => is_dependentE e || is_dependentT t
  | Epostdec e t => is_dependentE e || is_dependentT t
  | Eseqand e1 e2 => is_dependentE e1 || is_dependentE e2
  | Eseqor e1 e2 => is_dependentE e1 || is_dependentE e2
  | Ecomma e1 e2 => is_dependentE e1 || is_dependentE e2
  | Ecall e es => is_dependentE e || existsb is_dependentE es
  | Eexplicit_cast _ t e => is_dependentE e || is_dependentT t
  | Ecast c e => Cast.existsb is_dependentT c || is_dependentE e
  | Emember _ e f _ t => is_dependentE e || atomic_name.existsb is_dependentT f || is_dependentT t
  | Emember_ignore _ e e' => is_dependentE e || is_dependentE e'
  | Emember_call _ m e es => MethodRef.existsb is_dependentN is_dependentT is_dependentE m || is_dependentE e || existsb is_dependentE es
  | Eoperator_call _ i es => operator_impl.existsb is_dependentN is_dependentT i || existsb is_dependentE es
  | Esubscript e1 e2 t => is_dependentE e1 || is_dependentE e2 || is_dependentT t
  | Esizeof te t
  | Ealignof te t => sum.existsb is_dependentT is_dependentE te || is_dependentT t
  | Eoffsetof gn _ t => is_dependentT gn || is_dependentT t
  | Econstructor n es t => is_dependentN n || existsb is_dependentE es || is_dependentT t
  | Einherited_constructor n _ t => is_dependentN n || is_dependentT t
  | Elambda n es => is_dependentN n || existsb is_dependentE es
  | Eimplicit e => is_dependentE e
  | Eimplicit_init t => is_dependentT t
  | Eif e1 e2 e3 t => is_dependentE e1 || is_dependentE e2 || is_dependentE e3 || is_dependentT t
  | Eif2 _ e1 e2 e3 e4 t => is_dependentE e1 || is_dependentE e2 || is_dependentE e3 || is_dependentE e4 || is_dependentT t
  | Ethis t => is_dependentT t
  | Enull => false
  | Einitlist es eo t => existsb is_dependentE es || option.existsb is_dependentE eo || is_dependentT t
  | Einitlist_union f oe t => option.existsb is_dependentE oe || is_dependentT t

  | Enew p es _ t e1 e2 => is_dependentN p.1 || is_dependentT p.2 || existsb is_dependentE es || is_dependentT t || option.existsb is_dependentE e1 || option.existsb is_dependentE e2
  | Edelete _ p e t => is_dependentN p || is_dependentE e || is_dependentT t
  | Eandclean e => is_dependentE e
  | Ematerialize_temp e _ => is_dependentE e
  | Eatomic _ es t => existsb is_dependentE es || is_dependentT t
  | Estmt s t => is_dependentS s || is_dependentT t
  | Eva_arg e t => is_dependentE e || is_dependentT t
  | Epseudo_destructor _ t e => is_dependentT t || is_dependentE e
  | Earrayloop_init _ e1 _ _ e2 t => is_dependentE e1 || is_dependentE e2 || is_dependentT t
  | Earrayloop_index _ t => is_dependentT t
  | Eopaque_ref _ t => is_dependentT t
  | Eunsupported _ t => is_dependentT t
  | ELocInfo _ e => is_dependentE e
  end

with is_dependentVD (vd : VarDecl) : bool :=
  match vd with
  | Dvar _ t oe => is_dependentT t || option.existsb is_dependentE oe
  | Ddecompose e _ lvd => is_dependentE e || List.existsb is_dependentBD lvd
  | Dinit _ n t oe => is_dependentN n || is_dependentT t || option.existsb is_dependentE oe
  | DLocInfo _ vd => is_dependentVD vd
  end

with is_dependentBD (bd : BindingDecl) : bool :=
  match bd with
  | Bvar _ t e
  | Bbind _ t e => is_dependentT t || is_dependentE e
  | BLocInfo _ bd => is_dependentBD bd
  end

with is_dependentS (s : Stmt) : bool :=
  match s with
  | Sseq ss => List.existsb is_dependentS ss
  | Sdecl ds => List.existsb is_dependentVD ds
  | Sif os ovd e thn els =>
      option.existsb is_dependentS os ||
      option.existsb is_dependentVD ovd || is_dependentE e || is_dependentS thn || is_dependentS els
  | Sif_consteval thn els =>
      is_dependentS thn || is_dependentS els
  | Swhile ovd e b =>
      option.existsb is_dependentVD ovd || is_dependentE e || is_dependentS b
  | Sfor os oe1 oe2 s =>
      option.existsb is_dependentS os || option.existsb is_dependentE oe1 || option.existsb is_dependentE oe2 || is_dependentS s
  | Sdo b t => is_dependentS b || is_dependentE t
  | Sswitch os ovd e s =>
      option.existsb is_dependentS os ||
      option.existsb is_dependentVD ovd || is_dependentE e || is_dependentS s
  | Scase _
  | Sdefault
  | Sbreak
  | Scontinue => false
  | Sreturn oe => option.existsb is_dependentE oe
  | Sexpr e => is_dependentE e
  | Sattr _ s => is_dependentS s
  | Sasm _ _ ins outs _ =>
      List.existsb (is_dependentE ∘ snd) ins || List.existsb (is_dependentE ∘ snd) outs
  | Slabeled _ s => is_dependentS s
  | Sgoto _ => false
  | Sunsupported _ => false
  | SLocInfo _ s => is_dependentS s
  end.
