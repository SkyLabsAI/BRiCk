(*
 * Copyright (C) 2021-2022 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

Require Ltac2.Pstring.
Require Import skylabs.ltac2.extra.internal.plugin.
Require Import skylabs.ltac2.extra.internal.init.
Require Import skylabs.ltac2.extra.internal.misc.
Require Import skylabs.ltac2.extra.internal.printf.
Require Ltac2.FSet.

(* NOTE: When using [Constr.Unsafe], [Constr.Unsafe.check] will enforce sane
   universe constraints on _output_ constructors, as will code like
   <<
     let c := ... unsafe ... in
     let safe_c := '$c in
     ...
   >> *)

(** Minor extensions to [Ltac2.Constr] *)
Module Constr.
  Import Ltac2 Init Printf.
  Export Ltac2.Constr.

  (** [entirely_closed c] indicates whether [c] is free of: undefined evars,
      unbound rels, named evars without a bode, named variables whose body is
      not [entirely_closed]. Note that opaque and transparent constants are
      considered [entirely_closed]. *)
  Ltac2 @ external entirely_closed : constr -> bool :=
    "ltac2_extensions" "entirely_closed".

  (** [retype c] runs [Retyping.get_type_of ~lax:false c]. *)
  Ltac2 @ external retype : constr -> constr :=
    "ltac2_extensions" "constr_retype".

  (** [pretype_at otc oty p] pretypes preterm [p] at type [ty] if [oty] is
      [Some ty], or without any constraints if [ty] is [None]. Typeclass
      resolution is controlled with [otc]. If it is [None], typeclass search
      is disabled. If it is [Some b], then typeclass search is enabled, and
      the boolean [b] indicates whether all goals must be solved. *)
  Ltac2 @ external pretype_at :
    bool option -> constr option -> preterm -> constr :=
    "ltac2_extensions" "constr_pretype_at".

  (** See Coq's Vars.mli *)
  Module Vars.
    Ltac2 @ external closedn : int -> constr -> bool :=
      "ltac2_extensions" "vars_closedn".

    Ltac2 @ external noccur_between : int -> int -> constr -> bool :=
      "ltac2_extensions" "vars_noccur_between".

    Ltac2 @ external rels : constr -> int list :=
      "ltac2_extensions" "vars_rels".

    Ltac2 @ external vars : constr -> ident FSet.t :=
      "ltac2_extensions" "vars_vars".

    Ltac2 @ external vars_really_needed : constr -> ident FSet.t :=
      "ltac2_extensions" "vars_really_needed".

    Ltac2 @ external vars_really_needed_unsafe : constr -> ident FSet.t :=
      "ltac2_extensions" "vars_really_needed_unsafe".
  End Vars.

  Module Binder.
    Export Ltac2.Constr.Binder.

    Ltac2 deconstruct (b : binder) : name * relevance * type :=
      (name b, relevance b, type b).

    (** Mapping over a binder *)

    Ltac2 map_name : (name -> name) -> binder -> binder := fun f b =>
      let (name, r, ty) := deconstruct b in unsafe_make (f name) r ty.

    Ltac2 map_type : (type -> type) -> binder -> binder := fun f b =>
      let (name, r, ty) := deconstruct b in unsafe_make name r (f ty).
  End Binder.

  Module Evar.
    (** [make ty] creates a new evar of type [ty]. *)
    Ltac2 make (ty : constr) : constr := Misc.gen_evar false ty.

    (** [make_tc ty] creates a new evar of type [ty] that should be considered
        a candidate for typeclass resolution. *)
    Ltac2 make_tc (ty : constr) : constr := Misc.gen_evar true ty.

    (** [of_constr c] deconstructs [c] assuming it is an evar node. If that is
        not the case, an uncatchable [Invalid_argument _] is raised. *)
    Ltac2 of_constr (c : constr) : evar * constr array :=
      match Constr.Unsafe.kind c with
      | Constr.Unsafe.Evar evar args => (evar, args)
      | _ => Control.throw_invalid_argument "Evar.get"
      end.

    (** [name evar] gives the name of [evar]. It returns [None] if the evar is
        not in the evar map. *)
    Ltac2 @external name : evar -> ident option :=
      "ltac2_extensions" "evar_name".

    (** [rename evar id] renames the evar [evar] using name [id]. The tactic
        does not fail if [evar] is already named [id]. *)
    Ltac2 @ external rename : evar -> ident -> unit :=
      "ltac2_extensions" "rename_evar".

    (** [is_undefined evar] indicates wheter [evar] is undefined. *)
    Ltac2 @ external is_undefined : evar -> bool :=
      "ltac2_extensions" "evar_is_undefined".

    (** [restrict] uses [Evarutils.restrict_evar] to restrict the valid
        hypothesis of an evar.
        NOTE: Unlike [Evarutils.restrict_evar] and [Evd.restrict], [restrict]
        expects a filter whose length is equal to __FILTERED__ evar context,
        i.e. it only filters out hypotheses that were not filtered out before.
        In other words, the existing filter of the evar is composed with the
        [bool list] argument provided to [restrict]
     *)
    Ltac2 @ external restrict : bool list -> evar -> evar :=
      "ltac2_extensions" "restrict_evar".

    (** See [Evd.evar_context].
        NOTE: The context is returned from outermost to innermost binder, i.e.
        the same order as in [Control.hyps]. *)
    Ltac2 @ external context : evar -> (ident * constr option * constr) list :=
      "sl.Constr" "evar_context".
  End Evar.

  (** [subst_evars c] returns [Some c'], where [c'] is a copy of [c] where all
      evars have been replaced with their solutions. It returns [None] if there
      are evars without solutions. *)
  Ltac2 @ external subst_evars : constr -> constr option :=
    "ltac2_extensions" "subst_evars".

  Module Unsafe.
    Export Ltac2.Constr.Unsafe.

    (** ** Make wrappers *)

    Ltac2 make_rel (i : int) : constr :=
      make (Rel i).

    Ltac2 make_var (id : ident) : constr :=
      make (Var id).

    Ltac2 make_meta (m : meta) : constr :=
      make (Meta m).

    Ltac2 make_evar (evar : evar) (args : constr array) : constr :=
      make (Evar evar args).

    Ltac2 make_sort (s : sort) : constr :=
      make (Sort s).

    (** [Cast tm c ty] is [tm : ty] *)
    Ltac2 make_cast (tm : constr) (c : cast) (ty : constr) : constr :=
      make (Cast tm c ty).

    Ltac2 make_prod (b : binder) (c : constr) : constr :=
      make (Prod b c).

    Ltac2 make_prod' (b : binder) (f : constr -> constr) : constr :=
      let v := Fresh.in_goal (Option.default @x (Constr.Binder.name b)) in
      let t := Constr.Binder.type b in
      let fn := Constr.in_context v t (fun _ =>
              let v := Control.hyp v in
              Control.refine (fun _ => f v)) in
      match Constr.Unsafe.kind fn with
      | Lambda _ body' => make (Prod b body')
      | _ => Control.assert_true false ; t
      end.

    Ltac2 make_arrow (t0 : constr) (t1 : constr) : constr :=
      Constr.Unsafe.make (Prod (Constr.Binder.make None t0) t1).

    Ltac2 make_lambda (b : binder) (c : constr) : constr :=
      make (Lambda b c).

    Ltac2 make_lambda' (b : binder) (f : constr -> constr) : constr :=
      let v := Fresh.in_goal (Option.default @x (Constr.Binder.name b)) in
      let t := Constr.Binder.type b in
      Constr.in_context v t (fun _ =>
        let v := Control.hyp v in
        Control.refine (fun _ => f v)).

    (** [let b := c1 in c2] *)
    Ltac2 make_let_in (b : binder) (c1 : constr) (c2 : constr) : constr :=
      make (LetIn b c1 c2).

    Ltac2 make_app (c : constr) (args : constr array) : constr :=
      make (App c args).
    Ltac2 make_app_list (c : constr) (args : constr list) : constr :=
      make_app c (Array.of_list args).
    Ltac2 make_app1 (c : constr) (arg : constr) : constr :=
      let args := Array.make 1 arg in
      make_app c args.
    Ltac2 make_app2 (c : constr) (arg0 : constr) (arg1 : constr) : constr :=
      let args := Array.make 2 arg0 in
      Array.set args 1 arg1;
      make_app c args.
    Ltac2 make_app3 (c : constr) (arg0 : constr) (arg1 : constr)
        (arg2 : constr) : constr :=
      let args := Array.make 3 arg0 in
      Array.set args 1 arg1;
      Array.set args 2 arg2;
      make_app c args.
    Ltac2 make_app4 (c : constr) (arg0 : constr) (arg1 : constr)
        (arg2 : constr) (arg3 : constr) : constr :=
      let args := Array.make 4 arg0 in
      Array.set args 1 arg1;
      Array.set args 2 arg2;
      Array.set args 3 arg3;
      make_app c args.
    Ltac2 make_app5 (c : constr) (arg0 : constr) (arg1 : constr)
        (arg2 : constr) (arg3 : constr) (arg4 : constr) : constr :=
      let args := Array.make 5 arg0 in
      Array.set args 1 arg1;
      Array.set args 2 arg2;
      Array.set args 3 arg3;
      Array.set args 4 arg4;
      make_app c args.
    Ltac2 make_app6 (c : constr) (arg0 : constr) (arg1 : constr)
        (arg2 : constr) (arg3 : constr) (arg4 : constr)
        (arg5 : constr) : constr :=
      let args := Array.make 6 arg0 in
      Array.set args 1 arg1;
      Array.set args 2 arg2;
      Array.set args 3 arg3;
      Array.set args 4 arg4;
      Array.set args 5 arg5;
      make_app c args.
    Ltac2 make_app7 (c : constr) (arg0 : constr) (arg1 : constr)
        (arg2 : constr) (arg3 : constr) (arg4 : constr)
        (arg5 : constr) (arg6 : constr) : constr :=
      let args := Array.make 7 arg0 in
      Array.set args 1 arg1;
      Array.set args 2 arg2;
      Array.set args 3 arg3;
      Array.set args 4 arg4;
      Array.set args 5 arg5;
      Array.set args 6 arg6;
      make_app c args.
    Ltac2 make_app8 (c : constr) (arg0 : constr) (arg1 : constr)
        (arg2 : constr) (arg3 : constr) (arg4 : constr)
        (arg5 : constr) (arg6 : constr) (arg7 : constr) : constr :=
      let args := Array.make 8 arg0 in
      Array.set args 1 arg1;
      Array.set args 2 arg2;
      Array.set args 3 arg3;
      Array.set args 4 arg4;
      Array.set args 5 arg5;
      Array.set args 6 arg6;
      Array.set args 7 arg7;
      make_app c args.
    Ltac2 make_app9 (c : constr) (arg0 : constr) (arg1 : constr)
        (arg2 : constr) (arg3 : constr) (arg4 : constr)
        (arg5 : constr) (arg6 : constr) (arg7 : constr)
        (arg8 : constr) : constr :=
      let args := Array.make 9 arg0 in
      Array.set args 1 arg1;
      Array.set args 2 arg2;
      Array.set args 3 arg3;
      Array.set args 4 arg4;
      Array.set args 5 arg5;
      Array.set args 6 arg6;
      Array.set args 7 arg7;
      Array.set args 8 arg8;
      make_app c args.

    (**
    Instances of universe polymorphic constants, inductives, and
    constructors.
    *)
    Ltac2 make_constant (c : constant) (u : instance) : constr :=
      make (Constant c u).
    Ltac2 make_ind (i : inductive) (u : instance) : constr :=
      make (Ind i u).
    Ltac2 make_constructor (c : constructor) (u : instance) : constr :=
      make (Constructor c u).

    (**
    [Case ci p iv c br] represents a match expression in compact form
    (see Coq's kernel/inductive.mli):

    - [ci : case]: information about the match

    - [p]: the "return" clause represented as a [Lambda]

    - [iv]: impacts reduction of [SProp] matches

    - [c]: the term being matched

    - [br]: branches of the match, represented as [Lambda], [LetIn]

    *)
    Ltac2 make_case (ci : case) (p : constr * Binder.relevance)
        (iv : case_invert) (c : constr) (br : constr array) : constr :=
      make (Case ci p iv c br).

    (**
    [Fix skips i bnds lams] represents the [i]th function projected
    from a mutually recursive bundle [bnds |- lams_j] where [bnds_j]
    is the name and type of the [j]th member of the bundle and where
    [skips_j] is the number of lambdas to skip in that function to
    reach its recursive argument ([0 <= i, j < |skips| = |bnds| =
    |lams|).

    A [CoFix] carries similar data, but lacks [skips].
    *)
    Ltac2 make_fix (skips : int array) (i : int) (bnds : binder array)
        (lams : constr array) : constr :=
      make (Fix skips i bnds lams).

    Ltac2 make_cofix (i : int) (bnds : binder array)
        (lams : constr array) : constr :=
      make (CoFix i bnds lams).

    (** Primitive projection [t.(p)] *)
    Ltac2 make_proj (p : projection) (r : Binder.relevance)
        (t : constr) : constr :=
      make (Proj p r t).

    Ltac2 make_uint63 (i : uint63) : constr :=
      make (Uint63 i).

    Ltac2 make_float (f : float) : constr :=
      make (Float f).

    (**
    [Array ui cs def ty] represents a primitive (persistent) array
    with universe instance [u], terms [cs_i : ty], and a default [def
    : ty]. Universe [u] contains type [ty].
    *)
    Ltac2 make_array (u : instance) (cs : constr array)
        (def : constr) (t : constr) : constr :=
      make (Array u cs def t).

    Ltac2 make_string (s : string) :=
      match Pstring.of_string s with
      | Some p => make (String p)
      | None => Control.throw_invalid_argument "Invalid primitive string: %s" s
      end.

    Ltac2 make_pstring (p : pstring) := make (String p).

    (** ** Declarations *)
    (**
    An inhabitant of type [RelDecl.t] describes a [Rel i] and can be
    used to track local assumptions and definitions when working with
    terms under binders.
    *)

    Module RelDecl.
      Ltac2 Type t := [
      | Assum (binder)
      | Def (binder, term)
      ].

      Ltac2 pp : t pp := fun _ decl =>
        match decl with
        | Assum b => pp_binder () b
        | Def b val => fprintf "%a := %t" pp_binder b val
        end.

      Ltac2 binder (decl : t) : binder :=
        match decl with Assum b => b | Def b _ => b end.

      Ltac2 name (decl : t) : name :=
        Constr.Binder.name (binder decl).

      Ltac2 type (decl : t) : type :=
        Constr.Binder.type (binder decl).

      Ltac2 relevance (decl : t) : Binder.relevance :=
        Constr.Binder.relevance (binder decl).

      Ltac2 value (decl : t) : term option :=
        match decl with Assum _ => None | Def _ val => Some val end.

      Ltac2 is_assum (decl : t) : bool :=
        match decl with Assum _ => true | _ => false end.

      Ltac2 is_def (decl : t) : bool :=
        match decl with Def _ _ => true | _ => false end.

      (** Mapping over a declaration *)

      Ltac2 map_name : (name -> name) -> t -> t := fun f decl =>
        match decl with
        | Assum b => Assum (Constr.Binder.map_name f b)
        | Def b val => Def (Constr.Binder.map_name f b) val
        end.

      Ltac2 map_type : (type -> type) -> t -> t := fun f decl =>
        match decl with
        | Assum b => Assum (Constr.Binder.map_type f b)
        | Def b val => Def (Constr.Binder.map_type f b) val
        end.

      Ltac2 map_value : (term -> term) -> t -> t := fun f decl =>
        match decl with
        | Assum _ => decl
        | Def b val => Def b (f val)
        end.

      Ltac2 map_constr (f : constr -> constr) (decl : t) : t :=
        match decl with
        | Assum b => Assum (Constr.Binder.map_type f b)
        | Def b val => Def (Constr.Binder.map_type f b) (f val)
        end.
    End RelDecl.

    (** ** Iterators *)
    (**
    The following functions visit a term's immediate subterms, from
    left to right. While they are not recursive, they can be useful in
    defining recursive iterators.

    Immediate subterms are those carried by a term's [kind]
    constructor, including terms tucked away in inhabitants of types
    [binder], [array], and [case_invert].

    The [X_with_binders] (resp. [X_with_full_binders]) variants take
    additional arguments [g : 'c -> 'c] (resp. [g : RelDecl.t -> 'c ->
    'c]) and [n : 'c] and use [g] to bump [n] when descending under
    binders. Examples for [X_with_binders]:

    - [g := fun _ => true] (with initial value [false]) detects terms
    under binders

    - [g := Int.add 1] counts binding depth
    *)

    Ltac2 @ external map : (constr -> constr) -> constr -> constr :=
      "ltac2_extensions" "constr_map".
    Ltac2 @ external map_with_binders :
        ('c -> 'c) -> ('c -> constr -> constr) -> 'c -> constr -> constr :=
      "ltac2_extensions" "constr_map_with_binders".
    Ltac2 @ external map_with_full_binders :
        (RelDecl.t -> 'c -> 'c) -> ('c -> constr -> constr) ->
        'c -> constr -> constr :=
      "ltac2_extensions" "constr_map_with_full_binders".

    Ltac2 @ external iter : (constr -> unit) -> constr -> unit :=
      "ltac2_extensions" "constr_iter".
    Ltac2 @ external iter_with_binders :
        ('c -> 'c) -> ('c -> constr -> unit) -> 'c -> constr -> unit :=
      "ltac2_extensions" "constr_iter_with_binders".
    Ltac2 @ external iter_with_full_binders :
        (RelDecl.t -> 'c -> 'c) -> ('c -> constr -> unit) ->
        'c -> constr -> unit :=
      "ltac2_extensions" "constr_iter_with_full_binders".

    Ltac2 @ external fold : (constr -> 'a -> 'a) -> constr -> 'a -> 'a :=
      "ltac2_extensions" "constr_fold".
    Ltac2 @ external fold_with_binders :
      ('c -> 'c) -> ('c -> constr -> 'a -> 'a) -> 'c -> constr -> 'a -> 'a :=
      "ltac2_extensions" "constr_fold_with_binders".
    Ltac2 @ external fold_with_full_binders :
      (RelDecl.t -> 'c -> 'c) -> ('c -> constr -> 'a -> 'a) ->
      'c -> constr -> 'a -> 'a :=
      "ltac2_extensions" "constr_fold_with_full_binders".

    Module Destruct.

      Ltac2 invalid_arg' (whence : string) (what : message) : 'a :=
        let m := Message.of_string whence in
        let m := Message.concat m (Message.of_string ": ") in
        let m := Message.concat m what in
        Control.throw (Invalid_argument (Some m)).

      Ltac2 invalid_arg (whence : string) (t : constr) : 'a :=
        invalid_arg' whence (Message.of_constr t).

      Ltac2 of_ind_app_opt : constr -> (constr * constr array) option := fun t =>
        match kind t with
        | Ind _ _    => Some (t, Array.make 0 t)
        | App c args =>
            match kind c with
            | Ind _ _ => Some (c, args)
            | _       => None
            end
        | _          => None
        end.

      Ltac2 of_ind_app : constr -> constr * constr array := fun t =>
        let panic () := invalid_arg "Constr.Unsafe.Destruct.of_ind_app" t in
        match of_ind_app_opt t with
        | Some v => v
        | None => panic ()
        end.

      Ltac2 of_constructor_app_opt :
          constr -> (constr * instance * constr array) option := fun t =>
        match kind t with
        | Constructor _ inst => Some (t, inst, Array.make 0 t)
        | App c args         =>
            match kind c with
            | Constructor _ inst => Some (c, inst, args)
            | _       => None
            end
        | _          => None
        end.

      Ltac2 of_constructor_app : constr -> constr * instance * constr array :=
          fun t =>
        match of_constructor_app_opt t with
        | Some r => r
        | None   => invalid_arg "Constr.Unsafe.Destruct.of_constructor_app" t
        end.

      Ltac2 of_lambda_opt : constr -> (binder * constr) option := fun t =>
        match kind t with
        | Lambda b t => Some (b, t)
        | _ => None
        end.

      Ltac2 of_lambda : constr -> binder * constr := fun t =>
        match of_lambda_opt t with
        | Some r => r
        | None => invalid_arg "Constr.Unsafe.Destruct.of_lambda" t
        end.

      Ltac2 of_n_lambdas_opt : int -> constr -> (binder list * constr) option := fun i t =>
        let rec go i t (acc : binder list) :=
          if Int.equal i 0 then Some (List.rev acc, t)
          else
            match of_lambda_opt t with
            | Some (b, t) => go (Int.sub i 1) t (b :: acc)
            | None => None
            end
        in
        if Int.ge i 0 then go i t []
        else invalid_arg' "Constr.Unsafe.Destruct.of_n_lambdas_opt" (Message.of_int i).

      Ltac2 of_n_lambdas : int -> constr -> binder list * constr := fun i t =>
        match of_n_lambdas_opt i t with
        | Some r => r
        | None => invalid_arg "Constr.Unsafe.Destruct.of_n_lambdas" t
        end.

      (* Info about an applied projection. *)
      Ltac2 Type projection_info := {
        (** Inductive on which the projection is defined. *)
        pi_structure : inductive;
        (** The index of the projection, i.e. which field it projects out. *)
        pi_index : int;
        (** The unapplied (compatibility) constant of the projection. *)
        pi_proj : constr;
        (** parameters of the projection. *)
        pi_params : constr array;
        (** the record value to which the projection is applied. *)
        pi_recval : constr;
      }.

      Ltac2 @ external of_projection : constr -> projection_info option :=
        "ltac2_extensions" "decompose_proj".
    End Destruct.

    (** [compare] is an unsafe comparison operator that is also used in
        [ConstrSet] and [ConstrMap]. Use at your own peril. *)
    Ltac2 @ external compare : constr -> constr -> int :=
      "sl.Constr" "compare".

  End Unsafe.

  Ltac2 @external is_class : Std.reference -> bool :=
    "ltac2_extensions" "is_class".

  Ltac2 rec is_class_application (c : constr) : bool :=
    match Unsafe.kind c with
    | Unsafe.App c _
    | Unsafe.Prod _ c          => is_class_application c
    | Unsafe.Var id            => is_class (Std.VarRef id)
    | Unsafe.Constant cst _    => is_class (Std.ConstRef cst)
    | Unsafe.Ind ind _         => is_class (Std.IndRef ind)
    | Unsafe.Constructor cst _ => is_class (Std.ConstructRef cst)
    | _                        => false
    end.

  Ltac2 rec is_head_evar (c : constr) : bool :=
    match Unsafe.kind c with
    | Unsafe.Evar _ _ => true
    | Unsafe.App c _  => is_head_evar c
    | _               => false
    end.

  (** [specialize_products ty args] instantiates the first [Array.lenght args]
      [Prod] nodes of type [ty], with the terms in [args]. Weak-head reduction
      is performed at each step, so [c] only needs to be convertible to enough
      nested product types. The value returned is in weak-head normal form. *)
  Ltac2 @ external specialize_products : constr -> constr array -> constr :=
    "ltac2_extensions" "specialize_products".

  Ltac2 @ external debug_print : constr -> message :=
    "ltac2_extensions" "debug_print".

  (** Primitive projections. *)
  Module PProj.
    Ltac2 Type t := constant.

    Ltac2 @ external mkProj : t -> bool -> constr -> constr option :=
      "ltac2_extensions" "mkProj".

    Ltac2 of_compat (c : constr) : t :=
      match Constr.Unsafe.kind c with
      | Constr.Unsafe.Constant c _ => c
      | _ => Control.zero (Invalid_argument (Some (Message.of_string "not a constant")))
      end.

    Ltac2 of_compat_const (c : constr) (b : bool) (x : constr) :=
      mkProj (of_compat c) b x.
  End PProj.

  (** * Sets of [constr]s. *)
  Module ConstrSet.
    Ltac2 Type t.

    Ltac2 @ external empty : t :=
      "sl.ConstrSet" "empty".

    Ltac2 @ external is_empty : t -> bool :=
      "sl.ConstrSet" "is_empty".

    Ltac2 @ external diff : t -> t -> t :=
      "sl.ConstrSet" "diff".

    Ltac2 @ external union : t -> t -> t :=
      "sl.ConstrSet" "union".

    Ltac2 @ external of_list : constr list -> t :=
      "sl.ConstrSet" "of_list".

    Ltac2 @ external mem : constr -> t -> bool :=
      "sl.ConstrSet" "mem".

    Ltac2 @ external elements : t -> constr list :=
      "sl.ConstrSet" "elements".

    Ltac2 @ external add : constr -> t -> t :=
      "sl.ConstrSet" "add".

    Ltac2 @ external remove : constr -> t -> t :=
      "sl.ConstrSet" "remove".
  End ConstrSet.

  (** * Finite maps with [constr] keys. *)
  Module ConstrMap.
    Ltac2 Type 'a t.

    Ltac2 @ external empty : 'a t :=
      "sl.ConstrMap" "empty".

    Ltac2 @ external is_empty : 'a t -> bool :=
      "sl.ConstrMap" "is_empty".

    Ltac2 @ external mem : constr -> 'a t -> bool :=
      "sl.ConstrMap" "mem".

    Ltac2 @ external add : constr -> 'a -> 'a t -> 'a t :=
     "sl.ConstrMap" "add".

    Ltac2 @ external singleton : constr -> 'a -> 'a t :=
      "sl.ConstrMap" "singleton".

    Ltac2 @ external remove : constr -> 'a t -> 'a t :=
      "sl.ConstrMap" "remove".

    Ltac2 @ external cardinal : 'a t -> int :=
      "sl.ConstrMap" "cardinal".

    Ltac2 @ external bindings : 'a t -> (constr * 'a) list :=
      "sl.ConstrMap" "bindings".

    Ltac2 @ external find_opt : constr -> 'a t -> 'a option :=
      "sl.ConstrMap" "find_opt".
  End ConstrMap.
End Constr.
