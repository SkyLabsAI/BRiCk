(*
 * Copyright (c) 2026 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

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
