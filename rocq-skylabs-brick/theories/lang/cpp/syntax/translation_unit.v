(*
 * Copyright (c) 2020-2026 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import stdpp.fin_maps.
Require Import stdpp.sorting.
Require Stdlib.Sorting.SetoidList.
Require Import skylabs.prelude.base.
Require Import skylabs.prelude.avl.
Require Import skylabs.prelude.lens.
Require Import skylabs.prelude.elpi.derive.lens.
Require Import skylabs.prelude.pstring.
Require Import skylabs.lang.cpp.syntax.core.
Require Import skylabs.lang.cpp.syntax.types.
Require Import skylabs.lang.cpp.syntax.decl.
Require Import skylabs.lang.cpp.syntax.namemap.
Require skylabs.lang.cpp.syntax.compare.
Require Import skylabs.lang.cpp.syntax.mcore.
Require Import skylabs.lang.cpp.syntax.abi.
Require skylabs.lang.cpp.syntax.pretty.
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

(** ** Static assertions *)

Record StaticAssert : Set := Build_StaticAssert
  { sa_message : PrimString.string
  ; sa_condition : Expr
  }.
#[global] Instance StaticAssert_eq : EqDecision StaticAssert.
Proof. solve_decision. Defined.

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

(** The template AST *)
Notation MObjValue := ObjValue (only parsing).
Notation MGlobDecl := GlobDecl (only parsing).
Notation MGlobalInit := GlobalInit (only parsing).
Notation MGlobalInitializer := GlobalInitializer (only parsing).
Notation MInitializerBlock := InitializerBlock (only parsing).

(** ** Template Information

Template TUs house all templated code in a translation unit and relate
non-templated code induced by template application to the applied
template and its arguments.
 *)
Definition Msymbol_table : Type := TM.t (template MObjValue).
Definition Mtype_table : Type := TM.t (template MGlobDecl).
Definition Malias_table : Type := TM.t (template Mtype).
Definition Minstance_table : Type := NM.t Mtpreinst.

(** ** Distinct field names *)
(**
BRiCk identifies a field by its name (see [offset_of]), so every [Struct] and
[Union] in a [translation_unit] must have members with distinct names.
[fields_nodup] checks this by computation, and [translation_unit] carries a
proof that it holds.
*)

(** [field_names_nodup] is quadratic on short lists and sorts longer ones:
    measured under [vm_compute], comparison sorting only pays off above about
    16 names, while nearly all records in generated translation units have at
    most 8 fields.

    Both branches test names with [compare] directly rather than with
    [EqDecision], so the definition of [fields_nodup] (and hence the type of
    [translation_unit]) does not mention the laws of name comparison; only
    the soundness lemmas below use them. *)
#[local] Instance field_name_comparison : Comparison (@compare field_name.t _) :=
  compare.atomic_name_comparison.

Fixpoint field_names_nodup_quad (l : list field_name.t) : bool :=
  match l with
  | [] => true
  | x :: l =>
      negb (existsb (fun y => if compare x y is Eq then true else false) l) &&
      field_names_nodup_quad l
  end.

Lemma field_names_nodup_quad_sound l : field_names_nodup_quad l = true -> NoDup l.
Proof.
  elim: l => [|x l IH] /=; first by constructor.
  move=> /andb_prop [/negb_true_iff Hx /IH Hl]. constructor; last done.
  move=> Hin. move: Hx => /not_true_iff_false; apply.
  apply/existsb_exists. exists x. split; first exact/list_elem_of_In.
  by rewrite comparison_refl.
Qed.

#[local] Definition field_name_le (a b : field_name.t) : Prop := compare a b <> Gt.
#[local] Instance field_name_le_dec : RelDecision field_name_le :=
  fun a b => decide (compare a b <> Gt).

(** [strictly_increasing x l] checks that [x :: l] is strictly increasing. *)
Fixpoint strictly_increasing (x : field_name.t) (l : list field_name.t) : bool :=
  match l with
  | [] => true
  | y :: l => if compare x y is Lt then strictly_increasing y l else false
  end.

Definition field_names_nodup_sort (l : list field_name.t) : bool :=
  match merge_sort field_name_le l with
  | [] => true
  | x :: l => strictly_increasing x l
  end.

Lemma strictly_increasing_sound x l :
  strictly_increasing x l = true -> NoDup (x :: l) /\ forall y, y ∈ l -> compare x y = Lt.
Proof.
  elim: l x => [|y l IH] x /=.
  { split; first by apply NoDup_singleton. by move=> ? /elem_of_nil. }
  case Hxy: (compare x y) => // /IH [Hnd Hlt].
  have Hall : forall z, z ∈ y :: l -> compare x z = Lt.
  { move=> z /elem_of_cons [->|/Hlt Hyz]; first done.
    exact: (compare_trans _ _ _ _ Hxy Hyz). }
  split; last done. constructor; last done.
  move=> /Hall. by rewrite comparison_refl.
Qed.

Lemma field_names_nodup_sort_sound l : field_names_nodup_sort l = true -> NoDup l.
Proof.
  rewrite /field_names_nodup_sort => H.
  rewrite -(merge_sort_Permutation field_name_le l).
  move: H. case: (merge_sort _ _) => [|x l'] H; first constructor.
  by case: (strictly_increasing_sound _ _ H).
Qed.

Definition field_names_nodup (l : list field_name.t) : bool :=
  if (length l <=? 16)%nat then field_names_nodup_quad l else field_names_nodup_sort l.

Lemma field_names_nodup_sound l : field_names_nodup l = true -> NoDup l.
Proof.
  rewrite /field_names_nodup. case: (_ <=? _)%nat.
  - exact: field_names_nodup_quad_sound.
  - exact: field_names_nodup_sort_sound.
Qed.

Definition decl_fields_nodup (d : GlobDecl) : bool :=
  match d with
  | Gstruct st => field_names_nodup (mem_name <$> st.(s_fields))
  | Gunion u => field_names_nodup (mem_name <$> u.(u_fields))
  | _ => true
  end.

Definition fields_nodup (te : type_table) : bool :=
  map_fold (fun _ d b => decl_fields_nodup d && b) true te.

Lemma fields_nodup_alt te :
  fields_nodup te = forallb (fun kv => decl_fields_nodup kv.2) (NM.elements te).
Proof.
  rewrite /fields_nodup /map_fold /NM.map_mapfold NM.fold_1.
  have Hgen b l :
    fold_left (fun a (p : name * GlobDecl) => decl_fields_nodup p.2 && a) l b =
      b && forallb (fun kv => decl_fields_nodup kv.2) l.
  { elim: l b => [|p l IH] b /=; first by rewrite andb_true_r.
    by rewrite IH andb_assoc (andb_comm b). }
  by rewrite Hgen.
Qed.

Lemma fields_nodup_lookup te n d :
  fields_nodup te = true -> te !! n = Some d -> decl_fields_nodup d = true.
Proof.
  rewrite fields_nodup_alt => /forallb_forall Hall Hlook.
  have /SetoidList.InA_alt [[k v] [[_ /= Hv] Hin]] := NM.elements_1 (NM.find_2 Hlook).
  subst v. exact: (Hall (k, d)).
Qed.

Lemma fields_nodup_intro te :
  (forall n d, te !! n = Some d -> decl_fields_nodup d = true) -> fields_nodup te = true.
Proof.
  rewrite fields_nodup_alt => Hall. apply/forallb_forall => [[k v] Hin] /=.
  apply: (Hall k). apply: NM.find_1. apply: NM.elements_2.
  apply/SetoidList.InA_alt. exists (k, v). split; last done.
  split; first apply NM.Key.eq_refl. done.
Qed.

Lemma fields_nodup_struct te n st :
  fields_nodup te = true -> te !! n = Some (Gstruct st) ->
  NoDup (mem_name <$> st.(s_fields)).
Proof. move=> H /(fields_nodup_lookup _ _ _ H). exact: field_names_nodup_sound. Qed.

Lemma fields_nodup_union te n u :
  fields_nodup te = true -> te !! n = Some (Gunion u) ->
  NoDup (mem_name <$> u.(u_fields)).
Proof. move=> H /(fields_nodup_lookup _ _ _ H). exact: field_names_nodup_sound. Qed.

(** [sanitize_types te] replaces every record whose field names are not
    distinct by [Gunsupported]; it is the identity on tables that pass
    [fields_nodup]. *)
Definition sanitize_decl (n : name) (d : GlobDecl) : GlobDecl :=
  if decl_fields_nodup d then d
  else Gunsupported ("Duplicate field names in " ++ pretty.print_name n)%pstring.

(** Like [NM.mapi sanitize_decl te], but the [bst] proof is opaque and
    mentions only [te]. [NM.mapi]'s proof mentions [sanitize_decl] itself, and
    [vm_compute] reads such a proof back by normalizing [sanitize_decl]'s body
    under its binders, unfolding the checker and the pretty-printer on symbolic
    arguments; that does not terminate in practice, even for a one-entry table. *)
Lemma sanitize_types_bst (te : type_table) :
  NM.Raw.bst (NM.Raw.mapi sanitize_decl (NM.this te)).
Proof. apply: NM.Raw.Proofs.mapi_bst. exact: NM.is_bst. Qed.

Definition sanitize_types (te : type_table) : type_table :=
  {| NM.this := NM.Raw.mapi sanitize_decl (NM.this te); NM.is_bst := sanitize_types_bst te |}.

Lemma sanitize_types_find te n :
  NM.find n (sanitize_types te) = NM.find n (NM.mapi sanitize_decl te).
Proof. done. Qed.

Lemma sanitize_types_ok te : fields_nodup (sanitize_types te) = true.
Proof.
  apply: fields_nodup_intro => n d Hlook.
  have [d0 Hd0] : NM.In n te.
  { apply: (NM.mapi_2 (f := sanitize_decl)). exists d. exact: NM.find_2. }
  have [n0 [_ Hmaps]] := NM.mapi_1 sanitize_decl Hd0.
  have H := NM.find_1 Hmaps. rewrite -sanitize_types_find in H.
  have Hlook' : NM.find n (sanitize_types te) = Some d := Hlook.
  have <- : sanitize_decl n0 d0 = d by congruence.
  rewrite /sanitize_decl. by case E: (decl_fields_nodup d0); rewrite ?E.
Qed.

#[global] Arguments sanitize_types : simpl never.

Lemma sanitize_types_lookup te n :
  sanitize_types te !! n = sanitize_decl n <$> te !! n.
Proof.
  rewrite /lookup /NM.map_lookup sanitize_types_find.
  case Hn: (NM.find n te) => [d|] /=.
  - have [n0 [/NM.eqL -> Hmaps]] := NM.mapi_1 sanitize_decl (NM.find_2 Hn).
    exact: NM.find_1.
  - case Hm: (NM.find n (NM.mapi sanitize_decl te)) => [d|] //.
    have [d0 Hd0] : NM.In n te.
    { apply: (NM.mapi_2 (f := sanitize_decl)). exists d. exact: NM.find_2. }
    move: (NM.find_1 Hd0). congruence.
Qed.

Lemma sanitize_types_id te :
  fields_nodup te = true -> forall n, sanitize_types te !! n = te !! n.
Proof.
  move=> H n. rewrite sanitize_types_lookup.
  case Hn: (te !! n) => [d|] //=. rewrite /sanitize_decl.
  by rewrite (fields_nodup_lookup _ _ _ H Hn).
Qed.

(** [with_checked_types te k] passes [te] to [k] when it passes
    [fields_nodup], and [sanitize_types te] otherwise. *)
Definition with_checked_types {A} (te : type_table)
    (k : forall te', fields_nodup te' = true -> A) : A :=
  match fields_nodup te as b return fields_nodup te = b -> A with
  | true => fun H => k te H
  | false => fun _ => k (sanitize_types te) (sanitize_types_ok te)
  end eq_refl.

Lemma with_checked_types_ok {A} te k (H : fields_nodup te = true) :
  @with_checked_types A te k = k te H.
Proof.
  rewrite /with_checked_types. move: (eq_refl (fields_nodup te)).
  rewrite {2 3}H => H'. by rewrite (proof_irrel H' H).
Qed.

(** ** Translation units *)
(**
A [translation_unit] represents all the statically known
information about a C++ translation unit, that is, a source file.

For us, a [translation_unit] also contains implementation-defined information,
both in layout information for types and in [abi].

TOOD: add support for symbols with _internal_ linkage.

TODO: does linking induce a (non-commutative) monoid on object files?
Is then a translation unit a "singleton" value in this monoid?
*)

Record translation_unit : Type := makeTranslationUnit {
  symbols           : symbol_table;
  types             : type_table;
  namespace_aliases : alias_table.t;
  initializer       : InitializerBlock;
  asserts           : list StaticAssert;
  abi               : abi.t;

  msymbols : Msymbol_table;
  mtypes : Mtype_table;
  maliases : Malias_table;	(* we eschew <<Gtypedef>> for now *)
  minstances : Minstance_table;

  types_fields_nodup : fields_nodup types = true
}.
(** Lenses. [derive lens] does not support the dependent field
    [types_fields_nodup]. [_types] stores [sanitize_types] of the new table,
    which replaces records with duplicate field names by [Gunsupported] and
    does not otherwise change lookups (see [sanitize_types_lookup]); unlike
    [with_checked_types], it reduces on tables with symbolic entries. *)
#[local] Definition tu_lens {A} (view : translation_unit -> A)
    (set : A -> translation_unit -> translation_unit)
  : Lens translation_unit translation_unit A A :=
  {| Lens.view := view; Lens.over f tu := set (f (view tu)) tu |}.

Definition _symbols : Lens translation_unit translation_unit symbol_table symbol_table :=
  tu_lens symbols (fun x tu =>
    makeTranslationUnit x tu.(types) tu.(namespace_aliases) tu.(initializer)
      tu.(asserts) tu.(abi) tu.(msymbols) tu.(mtypes) tu.(maliases)
      tu.(minstances) tu.(types_fields_nodup)).

Definition _types : Lens translation_unit translation_unit type_table type_table :=
  tu_lens types (fun x tu =>
    makeTranslationUnit tu.(symbols) (sanitize_types x) tu.(namespace_aliases)
      tu.(initializer) tu.(asserts) tu.(abi) tu.(msymbols) tu.(mtypes)
      tu.(maliases) tu.(minstances) (sanitize_types_ok x)).

Definition _namespace_aliases : Lens translation_unit translation_unit alias_table.t alias_table.t :=
  tu_lens namespace_aliases (fun x tu =>
    makeTranslationUnit tu.(symbols) tu.(types) x tu.(initializer)
      tu.(asserts) tu.(abi) tu.(msymbols) tu.(mtypes) tu.(maliases)
      tu.(minstances) tu.(types_fields_nodup)).

Definition _initializer : Lens translation_unit translation_unit InitializerBlock InitializerBlock :=
  tu_lens initializer (fun x tu =>
    makeTranslationUnit tu.(symbols) tu.(types) tu.(namespace_aliases) x
      tu.(asserts) tu.(abi) tu.(msymbols) tu.(mtypes) tu.(maliases)
      tu.(minstances) tu.(types_fields_nodup)).

Definition _asserts : Lens translation_unit translation_unit (list StaticAssert) (list StaticAssert) :=
  tu_lens asserts (fun x tu =>
    makeTranslationUnit tu.(symbols) tu.(types) tu.(namespace_aliases)
      tu.(initializer) x tu.(abi) tu.(msymbols) tu.(mtypes) tu.(maliases)
      tu.(minstances) tu.(types_fields_nodup)).

Definition _abi : Lens translation_unit translation_unit abi.t abi.t :=
  tu_lens abi (fun x tu =>
    makeTranslationUnit tu.(symbols) tu.(types) tu.(namespace_aliases)
      tu.(initializer) tu.(asserts) x tu.(msymbols) tu.(mtypes) tu.(maliases)
      tu.(minstances) tu.(types_fields_nodup)).

Definition _msymbols : Lens translation_unit translation_unit Msymbol_table Msymbol_table :=
  tu_lens msymbols (fun x tu =>
    makeTranslationUnit tu.(symbols) tu.(types) tu.(namespace_aliases)
      tu.(initializer) tu.(asserts) tu.(abi) x tu.(mtypes) tu.(maliases)
      tu.(minstances) tu.(types_fields_nodup)).

Definition _mtypes : Lens translation_unit translation_unit Mtype_table Mtype_table :=
  tu_lens mtypes (fun x tu =>
    makeTranslationUnit tu.(symbols) tu.(types) tu.(namespace_aliases)
      tu.(initializer) tu.(asserts) tu.(abi) tu.(msymbols) x tu.(maliases)
      tu.(minstances) tu.(types_fields_nodup)).

Definition _maliases : Lens translation_unit translation_unit Malias_table Malias_table :=
  tu_lens maliases (fun x tu =>
    makeTranslationUnit tu.(symbols) tu.(types) tu.(namespace_aliases)
      tu.(initializer) tu.(asserts) tu.(abi) tu.(msymbols) tu.(mtypes) x
      tu.(minstances) tu.(types_fields_nodup)).

Definition _minstances : Lens translation_unit translation_unit Minstance_table Minstance_table :=
  tu_lens minstances (fun x tu =>
    makeTranslationUnit tu.(symbols) tu.(types) tu.(namespace_aliases)
      tu.(initializer) tu.(asserts) tu.(abi) tu.(msymbols) tu.(mtypes)
      tu.(maliases) x tu.(types_fields_nodup)).

(** [types_fields_nodup] is a proof of an equation between booleans, so it is
    irrelevant: translation units with equal data are equal. *)
Lemma translation_unit_eq (tu1 tu2 : translation_unit) :
  tu1.(symbols) = tu2.(symbols) ->
  tu1.(types) = tu2.(types) ->
  tu1.(namespace_aliases) = tu2.(namespace_aliases) ->
  tu1.(initializer) = tu2.(initializer) ->
  tu1.(asserts) = tu2.(asserts) ->
  tu1.(abi) = tu2.(abi) ->
  tu1.(msymbols) = tu2.(msymbols) ->
  tu1.(mtypes) = tu2.(mtypes) ->
  tu1.(maliases) = tu2.(maliases) ->
  tu1.(minstances) = tu2.(minstances) ->
  tu1 = tu2.
Proof.
  case: tu1 => ?????????? H1; case: tu2 => ?????????? H2 /=.
  intros; subst. f_equal. exact: proof_irrel.
Qed.

Definition byte_order (tu : translation_unit) : endian :=
  tu.(abi).(abi.byte_order).

Definition language_version (tu : translation_unit) : lang_version.t :=
  tu.(abi).(abi.lang_version).

(** Just for testing *)
Definition empty_tu (info : abi.t) : translation_unit :=
  makeTranslationUnit ∅ ∅ ∅ [] [] info ∅ ∅ ∅ ∅ eq_refl.
#[global] Instance : Empty translation_unit :=
  empty_tu abi.abi_default.

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

(** TODO: this logic replicates part of the substitution infrastructure inside of <auto>
    The implementation should use the <traverse> functionality.
 *)
Module template_alias.
  Definition env : Set := list (ident * temp_arg).

  Fixpoint lookup (xs : env) (id : ident) : option temp_arg :=
    match xs with
    | [] => None
    | (id', arg) :: xs =>
        if bool_decide (id = id') then Some arg else lookup xs id
    end.

  Definition lookup_type (xs : env) (id : ident) : option type :=
    match lookup xs id with
    | Some (Atype t) => Some t
    | _ => None
    end.

  Definition lookup_value (xs : env) (id : ident) : option Expr :=
    match lookup xs id with
    | Some (Avalue e) => Some e
    | _ => None
    end.

  Definition lookup_template (xs : env) (id : ident) : option temp_arg :=
    match lookup xs id with
    | Some (Atemplate _) as arg => arg
    | Some (Atemplate_param _) as arg => arg
    | _ => None
    end.

  Definition subst_expr (xs : env) (e : Expr) : Expr :=
    match e with
    | Eparam id =>
        match lookup_value xs id with
        | Some e => e
        | None => e
        end
    | _ => e
    end.

  Fixpoint subst_name (xs : env) (n : name) : name :=
    match n with
    | Ninst n args =>
      let n := subst_name xs n in
      let args := subst_temp_arg xs <$> args in
      Ninst n args
    | Nglobal _ => n
    | Ndependent t => Ndependent' (subst_type xs t)
    | Nscoped n c => Nscoped (subst_name xs n) c
    | Nunsupported _ => n
    end

  with subst_temp_arg (xs : env) (a : temp_arg) : temp_arg :=
    match a with
    | Atype t => Atype (subst_type xs t)
    | Avalue e => Avalue (subst_expr xs e)
    | Apack args => Apack (subst_temp_arg xs <$> args)
    | Atemplate n => Atemplate (subst_name xs n)
    | Atemplate_param id =>
        match lookup_template xs id with
        | Some arg => arg
        | None => a
        end
    | Aunsupported _ => a
    end

  with subst_type (xs : env) (t : type) : type :=
    match t with
    | Tparam_inst n args =>
      let args := subst_temp_arg xs <$> args in
      match lookup_template xs n with
      | Some (Atemplate n) => Tnamed $ Ninst n args
      | Some (Atemplate_param n) => Tparam_inst n args
      | _ => Tparam_inst n args
      end
    | Tparam id =>
        match lookup_type xs id with
        | Some t => t
        | None => t
        end
    | Tresult_param _ | Tauto | Tnum _ _ | Tchar_ _ | Tvoid
    | Tbool | Tfloat_ _ | Tnullptr | Tarch _ _ | Tunsupported _ => t
    | Tresult_global n => Tresult_global (subst_name xs n)
    | Tresult_unop o t => Tresult_unop o (subst_type xs t)
    | Tresult_binop o l r =>
        Tresult_binop o (subst_type xs l) (subst_type xs r)
    | Tresult_call n ts => Tresult_call (subst_name xs n) (subst_type xs <$> ts)
    | Tresult_member_call n o ts =>
        Tresult_member_call (subst_name xs n) (subst_type xs o) (subst_type xs <$> ts)
    | Tresult_parenlist t ts =>
        Tresult_parenlist (subst_type xs t) (subst_type xs <$> ts)
    | Tresult_member o f => Tresult_member (subst_type xs o) (subst_name xs f)
    | Tnamed n => Tnamed (subst_name xs n)
    | Tref t => tref QM (subst_type xs t)
    | Trv_ref t => trv_ref QM (subst_type xs t)
    | Tqualified q t => tqualified q (subst_type xs t)
    | Tptr t => Tptr (subst_type xs t)
    | Tarray t n => Tarray (subst_type xs t) n (* BUG: qualifier normalization on arrays? *)
    | Tincomplete_array t => Tincomplete_array (subst_type xs t)
    | Tvariable_array t e =>
        let t := subst_type xs t in
        let e := subst_expr xs e in
        match e with
        | Eint z _ =>
            if bool_decide (0 <= z)%Z then Tarray t (Z.to_N z)
            else Tvariable_array t e
        | _ => Tvariable_array t e
        end
    | Tenum n => Tenum (subst_name xs n)
    | Tfunction ft => Tfunction (function_type.fmap (subst_type xs) ft) (* BUG: qualifier normalization on function types *)
    | Tmember_pointer n t => Tmember_pointer (subst_type xs n) (subst_type xs t)
    | Tdecltype e => Tdecltype (subst_expr xs e)
    | Texprtype e => Texprtype (subst_expr xs e)
    end.

  Definition same_template_base (actual candidate : name) : option (list temp_arg) :=
    match actual, candidate with
    | Ninst actual_base args, Ninst candidate_base _ =>
        if bool_decide (actual_base = candidate_base) then Some args else None
    | _, _ => None
    end.

  #[local] Open Scope monad_scope.
  Fixpoint bind (e : env) (ps : list (temp_param * option temp_arg)) (args : list temp_arg) {struct ps} : option env :=
    match ps with
    | [] => if args is [] then Some [] else None
    | (p, default) :: ps =>
        let* arg :=
          match args return option temp_arg with
          | [] => subst_temp_arg e <$> default
          | arg :: _ => Some arg
          end
        in
        let* next_arg :=
          match p , arg with
          | Ptype id , Atype _ => Some (id, arg)
          | Pvalue id _ , Avalue _ => Some (id, arg)
          | Ptemplate id _ , (Atemplate _ | Atemplate_param _) => Some (id, arg)
          | _ , _ => None
          end
        in
        cons next_arg <$> bind (next_arg :: e) ps (tail args)
    end.

  Definition instantiate (actual : name) (candidate : name * template type)
      : option type :=
    let '(candidate_name, templ) := candidate in
    match same_template_base actual candidate_name with
    | Some args =>
        match bind [] templ.(template_params) args with
        | Some xs => Some (subst_type xs templ.(template_value))
        | None => None
        end
    | None => None
    end.

  Fixpoint find (actual : name) (candidates : list (name * template type))
      : option type :=
    match candidates with
    | [] => None
    | candidate :: candidates =>
        match instantiate actual candidate with
        | Some t => Some t
        | None => find actual candidates
        end
    end.
End template_alias.

(** Resolves all of the aliases in a type name. *)
Definition resolve_type (tu : translation_unit) (nm : name) : option decltype :=
  let maliases := TM.elements tu.(maliases) in
  let fix find (fuel : nat) (n : name) :=
    match tu.(types) !! n with
    | Some (Gtypedef ty) => Some ty
    | Some (Genum _ _) => Some $ Tenum n
    | Some _ => Some $ Tnamed n
    | None =>
        match template_alias.find n maliases with
        | Some (Tnamed n') =>
            match fuel with
            | O => Some (Tnamed n')
            | S fuel =>
                match canonicalize (find fuel) tu n' with
                | Some t => Some t
                | None => Some (Tnamed n')
                end
            end
        | other => other
        end
    end
  in
  canonicalize (find (List.length maliases)) tu nm.

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
  | complete_type_enum {n ty branches} :
    (* This check could not appear in a Krebbers-style definition.
       And it is not needed to enable computation on complete types.
     *)
    te !! n = Some (Genum ty branches) ->
    complete_basic_type ty ->
    complete_type (Tenum n)
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
   [types_fields_nodup] already follows this pattern for distinct field names.
3. add any helper lemmas, say for proving equality of [translation_unit] from
   equality of the relevant componets ([translation_unit_eq] covers this).

Twist: the "decision procedure" likely requires fuel; find how to adapt the
above plan. We'll likely end up with a boolean checker proven correct.

Question: do we need [complete_symbol_table]? This is not expected.

Goal: enable recursion on proofs of [complete_type_table], e.g. for defining
[anyR] (FM-215).
*)
