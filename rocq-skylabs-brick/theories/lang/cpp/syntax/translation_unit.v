(*
 * Copyright (c) 2020-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import stdpp.fin_maps.
Require Import bluerock.prelude.base.
Require Import bluerock.prelude.avl.
Require Import bluerock.prelude.lens.
Require Import bluerock.prelude.elpi.derive.lens.
Require Import bluerock.prelude.pstring.
Require Import bluerock.lang.cpp.syntax.core.
Require Import bluerock.lang.cpp.syntax.types.
Require Import bluerock.lang.cpp.syntax.decl.
Require Import bluerock.lang.cpp.syntax.namemap.
Export decl.

#[local] Set Primitive Projections.

#[local] Tactic Notation "solve_decision" := intros; solve_decision.

(** ** Type Declarations *)
Variant GlobDecl' : Set :=
  | Gtype     (* this is a type declaration, but not a definition *)
  | Gunion    (_ : Union) (* union body *)
  | Gstruct   (_ : Struct) (* struct body *)
  | Genum     (_ : type) (_ : list ident) (* *)
  | Gconstant (_ : type) (init : option Expr) (* used for enumerator constants*)
  | Gtypedef  (_ : type)
  | Gunsupported (_ : PrimString.string).
Notation GlobDecl := GlobDecl'.
#[global] Instance: EqDecision GlobDecl.
Proof. solve_decision. Defined.

(** *** The Type Table *)
Definition type_table : Type := NM.t GlobDecl.

(** ** Value Declarations *)

Module global_init.
  Variant t : Set :=
  | Init (_ : Expr)
  | ImplicitInit
    (* ^^ This arises because template instantiations are only carried out
          as much as they are needed. For example,
       <<
       template<typename T, T v>
       struct integral_constant {
         static constexpr T value = v;
       };
       void test() {
         // this line forces the declaration, but not the initialization.
         auto x = sizeof(integral_constant<bool, true>::value);
         // this line forces the initialization of the value.
         auto y = integral_constant<bool, true>::value;
       }
       >>
     *)
  | NoInit
  | Delayed (* for <<static>> variables declared in functions.
               These are initialized during the first call to the function *)
  | Extern.
  #[global] Instance t_eq : EqDecision t.
  Proof. solve_decision. Defined.

  Import UPoly.
  #[universes(polymorphic)]
  Definition fmap `{FMap M} (f : Expr -> Expr)
    (gi : global_init.t) : global_init.t :=
    match gi with
    | global_init.Init e => global_init.Init $ f e
    | global_init.ImplicitInit => global_init.ImplicitInit
    | global_init.NoInit => global_init.NoInit
    | global_init.Delayed => global_init.Delayed
    | global_init.Extern => global_init.Extern
    end.

  #[universes(polymorphic)]
  Definition traverse `{MRet M, Ap M} (f : Expr -> M Expr)
    (gi : global_init.t) : M (global_init.t) :=
    match gi with
    | global_init.Init e => global_init.Init <$> f e
    | global_init.ImplicitInit => mret global_init.ImplicitInit
    | global_init.NoInit => mret global_init.NoInit
    | global_init.Delayed => mret global_init.Delayed
    | global_init.Extern => mret global_init.Extern
    end.
End global_init.

(* Values in Object files. These can be externed. *)
Variant ObjValue' : Set :=
| Ovar         (_ : type) (_ : global_init.t)
| Ofunction    (_ : Func)
| Omethod      (_ : Method)
| Oconstructor (_ : Ctor)
| Odestructor  (_ : Dtor).
Notation ObjValue := ObjValue'.
#[global] Instance: EqDecision ObjValue.
Proof. solve_decision. Defined.

Definition can_throw (ov : ObjValue') : exception_spec.t :=
  match ov with
  | Ovar _ _ => exception_spec.Unknown
  | Ofunction fn => fn.(f_exception)
  | Omethod meth => meth.(m_exception)
  | Oconstructor ct => ct.(c_exception)
  | Odestructor dt => dt.(d_exception)
  end.

(**
TODO: [Tmember_func], [type_of_value] seem misplaced
*)

Definition type_of_classname : classname -> type := Tnamed.

(** [type_of_value o] returns the type of the given [ObjValue] *)
Definition type_of_value (o : ObjValue) : type :=
  normalize_type
  match o with
  | Ovar t _ => t
  | Ofunction f => Tfunction {| ft_cc := f.(f_cc) ; ft_arity := f.(f_arity) ; ft_return := f.(f_return) ; ft_params := snd <$> f.(f_params) |}
  | Omethod m =>
    Tmember_func (Tqualified m.(m_this_qual) (type_of_classname m.(m_class)))
                 $ Tfunction {| ft_cc := m.(m_cc) ; ft_arity := m.(m_arity) ; ft_return := m.(m_return) ; ft_params := snd <$> m.(m_params) |}

  | Oconstructor c =>
    Tmember_func (type_of_classname c.(c_class)) $ Tfunction {| ft_cc := c.(c_cc) ; ft_arity := c.(c_arity) ; ft_return := Tvoid ; ft_params := snd <$> c.(c_params) |}
  | Odestructor d =>
    Tmember_func (type_of_classname d.(d_class)) $ Tfunction {| ft_cc := d.(d_cc) ; ft_arity := Ar_Definite ; ft_return := Tvoid ; ft_params := nil |}
  end.

(** *** The Value Declaration Table *)

Definition symbol_table : Type := NM.t ObjValue.

(** ** Initializers *)
Variant GlobalInit' : Set :=
  (* initialization by an expression *)
| ExprInit (_ : Expr)
  (* zero initialization *)
| ZeroInit
  (* declaration will be initialized from within a function.
     The C++ standard states that these need to be initialized
     in a concurrency-safe way; however, in practice it is common
     to disable this functionality in embedded code using
     [-fno-threadsafe-statics]. The boolean attached to this
     determines whether *the compiler* guarantees there is at most
     a single call to this constructor.

     See https://eel.is/c++draft/stmt.dcl#3
   *)
| FunctionInit (at_most_once : bool).
Notation GlobalInit := GlobalInit'.
#[global] Instance: EqDecision GlobalInit.
Proof. solve_decision. Defined.

(** [GlobalInitializer] represents an initializer for a
    global variable.
 *)
Record GlobalInitializer' : Set := Build_GlobalInitializer
  { g_name : obj_name
  ; g_type : type
  ; g_init : GlobalInit
  }.
Notation GlobalInitializer := GlobalInitializer'.
#[global] Instance: EqDecision GlobalInitializer.
Proof. solve_decision. Defined.

(** An initialization block is a sequence of variable initializers
    that will be run when the compilation unit is loaded.

    Note that C++ guarantees the order of some initialization, but
    the order of template initialized global types is not specified by the
    standard.

    This means that, to be completely precise, this type needs to be
    something a bit more exotic that permits concurrent initialization.
 *)
Definition InitializerBlock : Set :=
  list GlobalInitializer.
#[global] Instance InitializerBlock_empty : Empty InitializerBlock :=
  nil.

(** ** Aliases *)

(** These support

    <<
    namespace X {
      inline namespace Y {
        void test();
        using namespace Bar;
      }
      inline namespace Z { }
    }
    >>

    In this snippet, <<X::Y::test()>> is also exposed as <<X::test()>>.

    <<inline>> is an attribute of a <<namespace>>, **not** a <<namespace>>
    declaration, so either the entire <<namespace>> is inlined, or none of
    it is.

    This data structure stores namespace inclusions, e.g.
    <<
    X := [X::Y; X::Z]
    X::Y := [Bar]
    >>
    as above. If <<NM>> maps to <<NM'>>, then a lookup on <<NM::xxx>> can
    be satisfied by a lookup on <<NM'::xxx>>.

    We do not include transitive dependencies, e.g. <<Bar>> is not included
    in <<X>>.
 *)
Module alias_table.
  Definition t : Type := listset name * NM.t (listset name).
  #[global] Instance t_empty : Empty t := (∅, ∅).

  Section expand_aliases.
    (** Get all possible expansions of the name *)
    Fixpoint all_expansions_ (aliases : NM.t (listset name)) (n : name) (fuel : nat) : list name :=
      [n] ++
        match aliases !! n with
        | Some (Listset ls) =>
            match fuel with
            | O => ls
            | S fuel =>
                letM* l := ls in
                all_expansions_ (NM.remove n aliases) l fuel
            end
        | None => []
        end.

    Definition all_expansions (aliases : NM.t (listset name)) (n : name) : list name :=
      all_expansions_ aliases n (NM.cardinal aliases).

    (** Expand all the aliases based on the information in the namespace table. *)
    Fixpoint expand_aliases (tu : alias_table.t) (nm : name) : list name :=
      match nm with
      | Nglobal an =>
          (* Because the global namespace can have inclusions, we need to consider <<inclusion::an>> *)
          let '(Listset gl, al) := tu in
          ((fun n => Nscoped n an) <$> gl) ++ all_expansions al nm
      | Ninst ns inst =>
          (fun ns => Ninst ns inst) <$> expand_aliases tu ns
      | Nscoped ns an =>
          letM* ns := expand_aliases tu ns in
          (fun ns => Nscoped ns an) <$> all_expansions tu.2 ns
      | _ => [nm]
      end.
  End expand_aliases.
End alias_table.

(** ** Translation units *)
(**
A [translation_unit] represents all the statically known
information about a C++ translation unit, that is, a source file.

TOOD: add support for symbols with _internal_ linkage.

TODO: does linking induce a (non-commutative) monoid on object files?
Is then a translation unit a "singleton" value in this monoid?
*)

Record translation_unit : Type := makeTranslationUnit {
  symbols           : symbol_table;
  types             : type_table;
  namespace_aliases : alias_table.t;
  initializer       : InitializerBlock;
  byte_order        : endian; (* NOTE: this is "runtime" information *)
}.
#[only(lens)] derive translation_unit.

Definition empty_tu (e : endian) : translation_unit :=
  makeTranslationUnit ∅ ∅ ∅ [] e.
#[global] Instance : Empty translation_unit :=
  empty_tu Little.

#[local]
Definition canonicalize {T} (find : name -> option T) (tu : translation_unit) (nm : name) : option T :=
  let aliases := alias_table.expand_aliases tu.(namespace_aliases) nm in
  let process n :=
    match find n with
    | None => []
    | Some v => [v]
    end
  in
  match List.flat_map process aliases with
  | t :: _ => Some t
  | _ => None
  end.

(** Resolves all of the aliases in a type name. *)
Definition resolve_type (tu : translation_unit) (nm : name) : option decltype :=
  let find n :=
    match tu.(types) !! n with
    | Some (Gtypedef ty) => Some ty
    | Some (Genum _ _) => Some $ Tenum n
    | Some _ => Some $ Tnamed n
    | None => None
    end
  in
  canonicalize find tu nm.

(** Resolves all of the aliases in a value name.
    TODO: This needs to be extended to search for <<enum>> constants.
    There is some complexity to this because <<enum>> constants in names will be
    replaced by their values.
 *)
Definition resolve_value (tu : translation_unit) (nm : name) : option name :=
  let find n :=
    match tu.(symbols) !! n with
    | Some _ => Some n
    | None => None
    end
  in
  canonicalize find tu nm.


(** [is_trivially_destructible tu ty] returns [true] if [ty] is trivially destructible.

    This classifies references as trivially destructible.
 *)
Fixpoint is_trivially_destructible (tu : translation_unit) (ty : type) {struct ty} : bool :=
  qual_norm (fun _ t =>
               match t with
               | Tref _ | Trv_ref _
               | Tnum _ _ | Tchar_ _
               | Tvoid | Tbool | Tptr _
               | Tenum _
               | Tmember_pointer _ _
               | Tfloat_ _
               | Tnullptr => true
               | Tnamed nm =>
                   match tu.(types) !! nm with
                   | Some (Gunion u) => u.(u_trivially_destructible)
                   | Some (Gstruct s) => s.(s_trivially_destructible)
                   | _ => false
                   end
               | Tarray ety _ => is_trivially_destructible tu ety
               | _ => false
               end) ty.

(**
TODO: The following work on complete types seems misplaced.
*)
Fixpoint ref_to_type (t : type) : option type :=
  match t with
  | Tref t
  | Trv_ref t => Some t
  | Tqualified _ t => ref_to_type t
  | _ => None
  end.

(* Not a reference type *)
Notation not_ref_type t := (ref_to_type t = None).

Section with_type_table.
  Variable te : type_table.
  (*
  To traverse a type definition and compute, say, its list of subobjects,
  we require that the type is _complete_, as in the usual sense.

  This definition is adapted from Krebbers'15, Definition 3.3.5, with needed
  adjustments for C++.

  Unlike Krebbers:
  - our [type_table] are not ordered
  - [complete_named] takes a proof of [complete_decl] to simplify its use for consumers,
    so we'd naively recheck a struct wherever needed; but an actual checker can
    be smarter (it could use a state monad carrying a map of known-complete types).

  The C++ standard defines and constrains "(in)complete type"s at
  https://eel.is/c++draft/basic.types.general#def:object_type,incompletely-defined,
  and constraints it at https://eel.is/c++draft/basic.scope.pdecl#6,
  https://eel.is/c++draft/class.mem#def:data_member,
  https://eel.is/c++draft/basic.def.odr#12,
  https://eel.is/c++draft/basic.def#5.
  *)

  (* Check that [g : GlobDecl] is complete in environment [te]. *)
  Inductive complete_decl : GlobDecl -> Prop :=
  (* We intentionally omit Krebbers' clauses checking the aggregate is not
  empty: empty aggregates are legal in full C/C++ (see
  [cpp2v-tests/test_translation_unit_validity.cpp]). *)
  | complete_Struct {st : Struct}
              (_ : forall (b : name) li, In (b, li) st.(s_bases) -> complete_type (Tnamed b))
              (_ : forall m, In m st.(s_fields) -> complete_type m.(mem_type))
    : complete_decl (Gstruct st)
  | complete_Union {u}
              (_ : forall m, In m u.(u_fields) -> complete_type m.(mem_type))
    : complete_decl (Gunion u)
  | complete_enum {t consts} (_ : complete_type t)
    : complete_decl (Genum t consts)
  (* No need for typedefs since those are forbidden in `Tnamed`, `Gtype` isn't
  legal, `Gconstant` is illegal and wouldn't make sense. *)

  (* Basic types. This excludes references (as checked by [complete_basic_type_not_ref]). *)
  with complete_basic_type : type -> Prop :=
  | complete_float sz : complete_basic_type (Tfloat_ sz)
  | complete_int sgn sz : complete_basic_type (Tnum sgn sz)
  | complete_bool : complete_basic_type Tbool
  | complete_nullptr : complete_basic_type Tnullptr
  | complete_char c : complete_basic_type (Tchar_ c)

  (* t can in turn be a pointer type *)
  | complete_ptr {t} : complete_pointee_type t -> complete_basic_type (Tptr t)

  (* [complete_pointee_type t] says that a pointer/reference to [t] is complete.
     This excludes references (as checked by [complete_pointee_type_not_ref])
     since they cannot be nested. *)
  with complete_pointee_type : type -> Prop :=
  | complete_pt_qualified {q t} (_ : complete_pointee_type t)
    : complete_pointee_type (Tqualified q t)
  (*
    Pointers to array are only legal if the array is complete, at least
    in C, since they cannot actually be indexed or created.
    This rejects the invalid C:

    [struct T; int foo(struct T x[][10]);]

    However, C++ compilers appear to accept this code, which we cover
    in [wellscoped_array].
    *)
  | complete_pt_array t n
    (_ : (n <> 0)%N) (* From Krebbers. Probably needed to reject [T[][]]. *)
    (_ : complete_type t) :
    complete_pointee_type (Tarray t n)
  | complete_pt_named {n decl} :
    (* This check could not appear in a Krebbers-style definition.
       And it is not needed to enable computation on complete types.
     *)
    te !! n = Some decl ->
    complete_pointee_type (Tnamed n)
  | complete_pt_enum {n ty branches} :
    (* This check could not appear in a Krebbers-style definition.
       And it is not needed to enable computation on complete types.
     *)
    te !! n = Some (Genum ty branches) ->
    complete_basic_type ty ->
    complete_pointee_type (Tenum n)

  (* Beware:
  [Tfunction] represents a function type; somewhat counterintuitively,
  a pointer to a function type is complete even if the argument/return types
  are not complete but only well-scoped, you're just forbidden from
  actually invoking the pointer; this follows Krebbers'15 3.3.5. *)
  | complete_pt_function {cc ret args}
      (_ : wellscoped_type ret)
      (_ : wellscoped_types args)
    : complete_pointee_type (Tfunction $ FunctionType (ft_cc:=cc) ret args)
  | complete_pt_basic t :
    complete_basic_type t ->
    complete_pointee_type t
  | complete_pointee_void : complete_pointee_type Tvoid
  (* [complete_type t] says that type [t] is well-formed, that is, complete. *)
  with complete_type : type -> Prop :=
  | complete_qualified {q t} (_ : complete_type t)
    : complete_type (Tqualified q t)
  (* Reference types. This setup forbids references to references. *)
  | complete_ref {t} : complete_pointee_type t -> complete_type (Tref t)
  | complete_rv_ref {t} : complete_pointee_type t -> complete_type (Trv_ref t)
  (*
  A reference to a struct/union named [n] is well-formed if its definition is.
  TODO: instead of checking that [n] points to a well-formed definition
  _at each occurrence_, check it once, when adding it to our
  analogue of a type environment, that is [type_table].
  However, that might require replacing [type_table] by a _sequence_ of
  declarations, instead of an unordered dictionary.
  *)
  | complete_named {n decl} (_ : te !! n = Some decl)
                    (_ : complete_decl decl) :
    complete_type (Tnamed n)
  | complete_array {t n}
    (_ : (n <> 0)%N) (* Needed? from Krebbers*)
    (_ : complete_type t) :
    complete_type (Tarray t n)
  | complete_member_pointer {n t} (_ : not_ref_type t)
      (_ : complete_pointee_type (Tnamed n))
      (_ : complete_pointee_type t)
    : complete_type (Tmember_pointer (Tnamed n) t)
  | complete_function {cc ar ret args} :
    (*
    We could probably omit this constructor, and consider function types as not
    complete; "complete function types" do not exist in the standard, and
    [complete_symbol_table] does not use the concept.
     *)
    complete_pointee_type (Tfunction $ FunctionType (ft_cc:=cc) (ft_arity:=ar) ret args) ->
    complete_type (Tfunction $ FunctionType (ft_cc:=cc) (ft_arity:=ar) ret args)
  | complete_basic t :
    complete_basic_type t ->
    complete_type t
  (** Well-scoped arguments cannot mention undeclared types. Krebbers identifies
  them with valid pointee, but that breaks down in C++ due to references. *)
  with wellscoped_type : type -> Prop :=
  | wellscoped_qualified {q t} (_ : wellscoped_type t)
    : wellscoped_type (Tqualified q t)
  | wellscoped_array t n
    (_ : (n <> 0)%N) : (* From Krebbers. Probably needed to reject [T[][]]. *)
    wellscoped_type t ->
    wellscoped_type (Tarray t n)
  | wellscoped_pointee t :
    complete_pointee_type t ->
    wellscoped_type t
  (* covers references. *)
  | wellscoped_complete {t} :
    complete_type t ->
    wellscoped_type t
  with wellscoped_types : list type -> Prop :=
  | wellscoped_nil : wellscoped_types []
  | wellscoped_cons t ts :
    wellscoped_type t ->
    wellscoped_types ts ->
    wellscoped_types (t :: ts).

  Inductive valid_decl : GlobDecl -> Prop :=
  | valid_typedef t :
    (*
    All typedefs in use have been inlined at their use-site, so we don't enforce
    their validity.

    In addition, we can't enforce their validity because `clang` produces
    builtin typedefs with ill-scoped bodies, such as
    [(Dtypedef "__NSConstantString" (Tnamed "_Z22__NSConstantString_tag")) :: ... ::
    (Dtypedef "__builtin_va_list" (Tarray (Tnamed "_Z13__va_list_tag") 1)) ::]. *)
    (* wellscoped_type t -> *)
    valid_decl (Gtypedef t)
  | valid_type : valid_decl Gtype
  | valid_const t oe :
    (* Potentially redundant. *)
    wellscoped_type t ->
    valid_decl (Gconstant t oe)
  | valid_complete_decl g :
    complete_decl g -> valid_decl g.
End with_type_table.

Scheme complete_decl_mut_ind := Minimality for complete_decl Sort Prop
with complete_basic_type_mut_ind := Minimality for complete_basic_type Sort Prop
with complete_pointee_type_mut_ind := Minimality for complete_pointee_type Sort Prop
with complete_type_mut_ind := Minimality for complete_type Sort Prop
with wellscoped_type_mut_ind := Minimality for wellscoped_type Sort Prop
with wellscoped_types_mut_ind := Minimality for wellscoped_types Sort Prop.

Combined Scheme complete_mut_ind from complete_decl_mut_ind, complete_basic_type_mut_ind,
  complete_pointee_type_mut_ind, complete_type_mut_ind,
  wellscoped_type_mut_ind, wellscoped_types_mut_ind.

Lemma complete_basic_type_not_ref te t : complete_basic_type te t → not_ref_type t.
Proof. by inversion 1. Qed.
Lemma complete_pointee_type_not_ref te t : complete_pointee_type te t → not_ref_type t.
Proof. induction 1; by [eapply complete_basic_type_not_ref | ]. Qed.

Lemma complete_type_not_ref_ref te t1 t2 : complete_type te t1 → ref_to_type t1 = Some t2 → not_ref_type t2.
Proof.
  induction 1 => Hsome; simplify_eq/=; generalize dependent te => te;
    try by [exact: complete_pointee_type_not_ref| tauto].
  move => /complete_basic_type_not_ref; naive_solver.
Qed.

(**
Adapted from Krebbers'15, Definition 3.3.6:
- all member types must be complete
- all function types must be pointer-complete as defined above.
*)
Definition complete_type_table (te : type_table) :=
  map_Forall (fun _key d => valid_decl te d) te.

Definition complete_symbol_table (te : type_table) (syms : symbol_table) :=
  map_Forall (fun _key d => complete_pointee_type te (type_of_value d)) syms.

Definition complete_translation_unit (te : type_table) (syms : symbol_table) :=
  complete_type_table te /\ complete_symbol_table te syms.

(*
#[global] Instance complete_type_table_dec te : Decision (complete_type_table te).
Proof.
apply: map_Forall_dec.
(* unshelve eapply map_Forall_dec; try apply _. *)
*)

(*
TODOs for FM-216:
1. prove [complete_type_table_dec] above with an efficient checker.
2. add [bool_decide (complete_type_table types = true]) to translation_unit;
   that's automatically proof-irrelevant, and proofs are just cheap [eq_refl].
3. add any helper lemmas, say for proving equality of [translation_unit] from
   equality of the relevant componets.

Twist: the "decision procedure" likely requires fuel; find how to adapt the
above plan. We'll likely end up with a boolean checker proven correct.

Question: do we need [complete_symbol_table]? This is not expected.

Goal: enable recursion on proofs of [complete_type_table], e.g. for defining
[anyR] (FM-215).
*)
