(*
 * Copyright (c) 2026 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import Stdlib.FSets.FMapFacts.
Require Import stdpp.listset.
Require Import skylabs.lang.cpp.syntax.core.
Require Import skylabs.lang.cpp.syntax.loc_info.
Require Import skylabs.lang.cpp.syntax.mcore.
Require Import skylabs.lang.cpp.syntax.namemap.
Require Import skylabs.lang.cpp.syntax.translation_unit.

Module LocInfoTU.
  Definition erase_FunctionBody (body : FunctionBody) : FunctionBody :=
    match body with
    | Impl s => Impl (LocInfo.erase_Stmt s)
    | Builtin name => Builtin name
    end.

  Definition erase_Func (f : Func) : Func :=
    Build_Func
      (LocInfo.erase_type f.(f_return))
      (List.map (fun '(name, t) => (name, LocInfo.erase_type t)) f.(f_params))
      f.(f_cc) f.(f_arity) f.(f_exception)
      (option_map erase_FunctionBody f.(f_body)).

  Definition erase_or_default {A : Set} (erase : A -> A)
      (value : OrDefault A) : OrDefault A :=
    match value with
    | Defaulted => Defaulted
    | CompilerProvided value => CompilerProvided (erase value)
    | UserDefined value => UserDefined (erase value)
    end.

  Definition erase_Method (m : Method) : Method :=
    Build_Method
      (LocInfo.erase_type m.(m_return))
      (LocInfo.erase_name m.(m_class))
      m.(m_this_qual)
      (List.map (fun '(name, t) => (name, LocInfo.erase_type t)) m.(m_params))
      m.(m_cc) m.(m_arity) m.(m_exception)
      (option_map (erase_or_default LocInfo.erase_Stmt) m.(m_body)).

  Definition erase_InitPath (path : InitPath) : InitPath :=
    match path with
    | InitBase base => InitBase (LocInfo.erase_name base)
    | InitField field => InitField (LocInfo.erase_atomic_name field)
    | InitIndirect path field =>
        InitIndirect
          (List.map
             (fun '(field, base) =>
                (LocInfo.erase_atomic_name field, LocInfo.erase_name base))
             path)
          (LocInfo.erase_atomic_name field)
    | InitThis => InitThis
    end.

  Definition erase_Initializer (init : Initializer) : Initializer :=
    Build_Initializer
      (erase_InitPath init.(init_path))
      (LocInfo.erase_Expr init.(init_init)).

  Definition erase_Ctor (ctor : Ctor) : Ctor :=
    Build_Ctor
      (LocInfo.erase_name ctor.(c_class))
      (List.map (fun '(name, t) => (name, LocInfo.erase_type t)) ctor.(c_params))
      ctor.(c_cc) ctor.(c_arity) ctor.(c_exception)
      (option_map
         (erase_or_default
            (fun '(initializers, body) =>
               (List.map erase_Initializer initializers,
                LocInfo.erase_Stmt body)))
         ctor.(c_body)).

  Definition erase_Dtor (dtor : Dtor) : Dtor :=
    Build_Dtor
      (LocInfo.erase_name dtor.(d_class))
      dtor.(d_cc) dtor.(d_exception)
      (option_map (erase_or_default LocInfo.erase_Stmt) dtor.(d_body)).

  Definition erase_ObjValue (value : ObjValue) : ObjValue :=
    match value with
    | Ovar t init =>
        Ovar (LocInfo.erase_type t)
          (match init with
           | global_init.Init e => global_init.Init (LocInfo.erase_Expr e)
           | global_init.ImplicitInit => global_init.ImplicitInit
           | global_init.NoInit => global_init.NoInit
           | global_init.Delayed => global_init.Delayed
           | global_init.Extern => global_init.Extern
           end)
    | Ofunction func => Ofunction (erase_Func func)
    | Omethod method => Omethod (erase_Method method)
    | Oconstructor ctor => Oconstructor (erase_Ctor ctor)
    | Odestructor dtor => Odestructor (erase_Dtor dtor)
    end.

  Definition erase_Member (member : Member) : Member :=
    mkMember
      (LocInfo.erase_atomic_name member.(mem_name))
      (LocInfo.erase_type member.(mem_type))
      member.(mem_mutable)
      (option_map LocInfo.erase_Expr member.(mem_init))
      member.(mem_layout).

  Definition erase_Union (union : Union) : Union :=
    Build_Union
      (List.map erase_Member union.(u_fields))
      (LocInfo.erase_name union.(u_dtor))
      union.(u_trivially_destructible)
      (option_map LocInfo.erase_name union.(u_delete))
      union.(u_size) union.(u_alignment).

  Definition erase_Struct (struct : Struct) : Struct :=
    Build_Struct
      (List.map
         (fun '(base, offset) => (LocInfo.erase_name base, offset))
         struct.(s_bases))
      (List.map erase_Member struct.(s_fields))
      (List.map
         (fun '(method, final) =>
            (LocInfo.erase_name method, option_map LocInfo.erase_name final))
         struct.(s_virtuals))
      (List.map
         (fun '(method, override) =>
            (LocInfo.erase_name method, LocInfo.erase_name override))
         struct.(s_overrides))
      (LocInfo.erase_name struct.(s_dtor))
      struct.(s_trivially_destructible)
      (option_map LocInfo.erase_name struct.(s_delete))
      struct.(s_layout) struct.(s_size) struct.(s_alignment).

  Definition erase_GlobDecl (decl : GlobDecl) : GlobDecl :=
    match decl with
    | Gtype => Gtype
    | Gunion union => Gunion (erase_Union union)
    | Gstruct struct => Gstruct (erase_Struct struct)
    | Genum t ids => Genum (LocInfo.erase_type t) ids
    | Gconstant t init =>
        Gconstant (LocInfo.erase_type t) (option_map LocInfo.erase_Expr init)
    | Gtypedef t => Gtypedef (LocInfo.erase_type t)
    | Gunsupported msg => Gunsupported msg
    end.

  Definition erase_NM {A : Type} (erase_value : A -> A)
      (table : NM.t A) : NM.t A :=
    NM.fold
      (fun name value result =>
         NM.add (LocInfo.erase_name name) (erase_value value) result)
      table (NM.empty A).

  (** Look up one canonical key without constructing the entire canonical map.
      The fold order and last-match-wins behavior intentionally agree with
      [erase_NM], including in the presence of canonical-key collisions. *)
  Definition lookup_NM {A : Type} (erase_value : A -> A)
      (table : NM.t A) (key : name) : option A :=
    NM.fold
      (fun stored_key value result =>
         if bool_decide (LocInfo.erase_name stored_key = key)
         then Some (erase_value value)
         else result)
      table None.

  Module NMFacts := FMapFacts.WFacts_fun NM.E NM.

  Lemma lookup_NM_spec {A : Type} (erase_value : A -> A)
      (table : NM.t A) (key : name) :
    erase_NM erase_value table !! key =
    lookup_NM erase_value table key.
  Proof.
    change (NM.find key (erase_NM erase_value table) =
      lookup_NM erase_value table key).
    unfold erase_NM, lookup_NM.
    rewrite !NM.fold_1.
    assert (Hfold : forall (entries : list (name * A)) (out : NM.t A) found,
        NM.find key out = found ->
        NM.find key
          (fold_left
             (fun result entry =>
                NM.add (LocInfo.erase_name entry.1)
                  (erase_value entry.2) result)
             entries out) =
        fold_left
          (fun result entry =>
             if bool_decide (LocInfo.erase_name entry.1 = key)
             then Some (erase_value entry.2)
             else result)
          entries found).
    { intros entries.
      induction entries as [|[stored_key value] entries IH];
        intros out found Hfind; simpl.
      - exact Hfind.
      - apply IH.
        destruct (bool_decide (LocInfo.erase_name stored_key = key))
          eqn:E.
        + apply bool_decide_eq_true_1 in E. subst key.
          apply NMFacts.add_eq_o. apply NM.E.eq_refl.
        + apply bool_decide_eq_false_1 in E.
          rewrite NMFacts.add_neq_o; first exact Hfind.
          intros Heq. apply E. apply NM.eqL in Heq. exact Heq. }
    apply Hfold. apply NMFacts.empty_o.
  Qed.

  Lemma lookup_NM_origin {A : Type} (erase_value : A -> A)
      (table : NM.t A) (key : name) selected :
    lookup_NM erase_value table key = Some selected ->
    exists stored_key stored_value,
      NM.MapsTo stored_key stored_value table /\
      LocInfo.erase_name stored_key = key.
  Proof.
    unfold lookup_NM. rewrite NM.fold_1. intros Hlookup.
    assert (Hfold : forall (entries : list (name * A)) found,
        fold_left
          (fun result entry =>
             if bool_decide (LocInfo.erase_name entry.1 = key)
             then Some (erase_value entry.2)
             else result)
          entries found = Some selected ->
        (exists stored_key stored_value,
           List.In (stored_key, stored_value) entries /\
           LocInfo.erase_name stored_key = key) \/
        found = Some selected).
    { intros entries. induction entries as [|[stored_key value] entries IH];
        intros found Hresult; simpl in Hresult.
      - right. exact Hresult.
      - specialize (IH _ Hresult).
        destruct IH as [[stored_key' [value' [Hin Heq]]]|Hfound].
        + left. exists stored_key', value'. split; first by right.
          exact Heq.
        + destruct (bool_decide (LocInfo.erase_name stored_key = key))
            eqn:E.
          * left. exists stored_key, value. split; first by left.
            by apply bool_decide_eq_true_1 in E.
          * right. exact Hfound. }
    destruct (Hfold (NM.elements table) None Hlookup)
      as [[stored_key [stored_value [Hin Heq]]]|Hnone];
      last discriminate Hnone.
    exists stored_key, stored_value. split; last exact Heq.
    apply NM.elements_2.
    induction (NM.elements table) as [|entry entries IH] in Hin |- *;
      first contradiction.
    destruct Hin as [->|Hin].
    - constructor. split; first apply NM.E.eq_refl. reflexivity.
    - constructor 2. exact (IH Hin).
  Qed.

  Definition erase_TM {A : Type} (erase_value : A -> A)
      (table : TM.t A) : TM.t A :=
    TM.fold
      (fun name value result =>
         TM.add (LocInfo.erase_name name) (erase_value value) result)
      table (TM.empty A).

  Definition erase_name_listset (names : listset name) : listset name :=
    match names with
    | Listset names => Listset (List.map LocInfo.erase_name names)
    end.

  Definition erase_alias_table (aliases : alias_table.t) : alias_table.t :=
    (erase_name_listset aliases.1, erase_NM erase_name_listset aliases.2).

  Definition erase_GlobalInit (init : GlobalInit) : GlobalInit :=
    match init with
    | ExprInit e => ExprInit (LocInfo.erase_Expr e)
    | ZeroInit => ZeroInit
    | FunctionInit at_most_once => FunctionInit at_most_once
    end.

  Definition erase_GlobalInitializer
      (init : GlobalInitializer) : GlobalInitializer :=
    Build_GlobalInitializer
      (LocInfo.erase_name init.(g_name))
      (LocInfo.erase_type init.(g_type))
      (erase_GlobalInit init.(g_init)).

  Definition erase_StaticAssert (assertion : StaticAssert) : StaticAssert :=
    Build_StaticAssert assertion.(sa_message)
      (LocInfo.erase_Expr assertion.(sa_condition)).

  Fixpoint erase_temp_param (param : temp_param) : temp_param :=
    match param with
    | Ptype id => Ptype id
    | Pvalue id t => Pvalue id (LocInfo.erase_type t)
    | Ptemplate id params =>
        Ptemplate id (List.map erase_temp_param params)
    | Punsupported msg => Punsupported msg
    end.

  Definition erase_template {A : Type} (erase_value : A -> A)
      (t : template A) : template A :=
    Template
      (List.map
         (fun '(param, default) =>
            (erase_temp_param param,
             option_map LocInfo.erase_temp_arg default))
         t.(template_params))
      (erase_value t.(template_value)).

  Definition erase_tpreinst (preinst : Mtpreinst) : Mtpreinst :=
    TPreInst
      (LocInfo.erase_name preinst.(tpreinst_name))
      (List.map LocInfo.erase_temp_arg preinst.(tpreinst_args)).

  Definition erase_translation_unit (tu : translation_unit) : translation_unit :=
    makeTranslationUnit
      (erase_NM erase_ObjValue tu.(symbols))
      (erase_NM erase_GlobDecl tu.(types))
      (erase_alias_table tu.(namespace_aliases))
      (List.map erase_GlobalInitializer tu.(initializer))
      (List.map erase_StaticAssert tu.(asserts))
      tu.(abi)
      (erase_TM (erase_template erase_ObjValue) tu.(msymbols))
      (erase_TM (erase_template erase_GlobDecl) tu.(mtypes))
      (erase_TM (erase_template LocInfo.erase_type) tu.(maliases))
      (erase_NM erase_tpreinst tu.(minstances)).
End LocInfoTU.

(** A canonical, location-free view of a translation unit.

    Semantic lookup APIs consume [SemanticTU.t], while operational predicates
    continue to carry the original [translation_unit].  Keeping the types
    distinct prevents semantic consumers from accidentally erasing an already
    canonical view a second time. *)
Module SemanticTU.
  (** Source views retain the original translation unit so single-entry
      lookups can canonicalize only the traversed keys and selected value.
      Canonical views wrap linked environments that are already location-free. *)
  Inductive t : Type :=
  | from_tu (_ : translation_unit)
  | from_canonical (_ : translation_unit).

  Definition of_tu (tu : translation_unit) : t := from_tu tu.

  (** Wrap a translation unit that is already known to be canonical.  This is
      reserved for semantic environments produced by linking. *)
  Definition of_canonical (tu : translation_unit) : t := from_canonical tu.

  Definition repr (tu : t) : translation_unit :=
    match tu with
    | from_tu tu => LocInfoTU.erase_translation_unit tu
    | from_canonical tu => tu
    end.

  Definition lookup_symbol (tu : t) (key : name) : option ObjValue :=
    match tu with
    | from_tu tu =>
        LocInfoTU.lookup_NM LocInfoTU.erase_ObjValue tu.(symbols) key
    | from_canonical tu => tu.(symbols) !! key
    end.

  Definition lookup_type (tu : t) (key : name) : option GlobDecl :=
    match tu with
    | from_tu tu =>
        LocInfoTU.lookup_NM LocInfoTU.erase_GlobDecl tu.(types) key
    | from_canonical tu => tu.(types) !! key
    end.

  Definition symbols (tu : t) : symbol_table := (repr tu).(symbols).
  Definition types (tu : t) : type_table := (repr tu).(types).

  Lemma lookup_symbol_spec tu key :
    symbols tu !! key = lookup_symbol tu key.
  Proof.
    destruct tu; simpl.
    - apply LocInfoTU.lookup_NM_spec.
    - reflexivity.
  Qed.

  Lemma lookup_type_spec tu key :
    types tu !! key = lookup_type tu key.
  Proof.
    destruct tu; simpl.
    - apply LocInfoTU.lookup_NM_spec.
    - reflexivity.
  Qed.

  Definition namespace_aliases (tu : t) : alias_table.t :=
    (repr tu).(namespace_aliases).
  Definition initializer (tu : t) : list GlobalInitializer :=
    (repr tu).(initializer).
  Definition asserts (tu : t) : list StaticAssert := (repr tu).(asserts).
  Definition abi (tu : t) := (repr tu).(abi).
End SemanticTU.

(** Location-insensitive translation-unit operations.  This is the neutral
    public boundary: callers keep the original translation unit while keyed
    queries erase only the selected declaration. *)
Module TU.
  Definition lookup_symbol (tu : translation_unit) (key : name) : option ObjValue :=
    SemanticTU.lookup_symbol (SemanticTU.of_tu tu) key.

  Definition lookup_type (tu : translation_unit) (key : name) : option GlobDecl :=
    SemanticTU.lookup_type (SemanticTU.of_tu tu) key.

  Definition canonical (tu : translation_unit) : translation_unit :=
    SemanticTU.repr (SemanticTU.of_tu tu).

  Definition canonical_aliases (tu : translation_unit) : alias_table.t :=
    LocInfoTU.erase_alias_table tu.(namespace_aliases).

  Definition resolve_candidates {A : Type} (find : name -> option A)
      (aliases : alias_table.t) (nm : name) : option A :=
    let process n :=
      match find n with
      | Some value => [value]
      | None => []
      end in
    match List.flat_map process
            (alias_table.expand_aliases aliases (LocInfo.erase_name nm)) with
    | value :: _ => Some value
    | [] => None
    end.

  (** Resolve an ordinary value name without materializing a canonical TU. *)
  Definition resolve_value (tu : translation_unit) (nm : name) : option name :=
    resolve_candidates
      (fun n =>
         match lookup_symbol tu n with
         | Some _ => Some n
         | None => None
         end)
      (canonical_aliases tu) nm.

  (** Resolve a type name.  This canonicalizes the template-alias table once,
      while ordinary keyed queries use [lookup_type] and erase only the
      selected declaration. *)
  Definition resolve_type (tu : translation_unit) (nm : name) : option decltype :=
    let aliases := canonical_aliases tu in
    let maliases :=
      LocInfoTU.erase_TM
        (LocInfoTU.erase_template LocInfo.erase_type) tu.(maliases) in
    let fix find (fuel : nat) (n : name) :=
      match lookup_type tu n with
      | Some (Gtypedef ty) => Some ty
      | Some (Genum _ _) => Some (Tenum n)
      | Some _ => Some (Tnamed n)
      | None =>
          match template_alias.find n (TM.elements maliases) with
          | Some (Tnamed n') =>
              match fuel with
              | O => Some (Tnamed n')
              | S fuel =>
                  match resolve_candidates (find fuel) aliases n' with
                  | Some ty => Some ty
                  | None => Some (Tnamed n')
                  end
              end
          | other => other
          end
      end in
    resolve_candidates (find (List.length (TM.elements maliases))) aliases nm.

  Lemma lookup_symbol_spec tu key :
    (canonical tu).(symbols) !! key = lookup_symbol tu key.
  Proof. exact (SemanticTU.lookup_symbol_spec (SemanticTU.of_tu tu) key). Qed.

  Lemma lookup_type_spec tu key :
    (canonical tu).(types) !! key = lookup_type tu key.
  Proof. exact (SemanticTU.lookup_type_spec (SemanticTU.of_tu tu) key). Qed.
End TU.
