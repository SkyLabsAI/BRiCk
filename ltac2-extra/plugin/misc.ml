(*
 * Copyright (C) 2021 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
open Ltac2_plugin
open TacUtil
open Tac2ffi
open Tac2val
open Tac2externals
open Rocq_extra.Extra

let define s =
  define Tac2expr.{ mltac_plugin = "ltac2_extensions"; mltac_tactic = s }

open Proofview.Notations

let create_clos_infos ?evars flgs env =
  let env = Environ.set_typing_flags ({(Environ.typing_flags env) with Declarations.share_reduction = false}) env in
  let evars =
    match evars with
    | None -> CClosure.default_evar_handler env
    | Some(evars) -> evars
  in
  CClosure.create_clos_infos ~evars flgs env

let red_flags : Names.GlobRef.t Genredexpr.glob_red_flag Tac2ffi.repr =
  let to_red_strength v =
    let open Genredexpr in
    match v with
    | ValInt 0 -> Norm
    | ValInt 1 -> Head
    | _ -> assert false
  in
  let to_red_flags v =
    let tuple = Tac2ffi.to_tuple v in
    if Array.length tuple <> 8 then assert false;
    let rStrength = to_red_strength tuple.(0) in
    let rBeta  = Tac2ffi.to_bool tuple.(1) in
    let rMatch = Tac2ffi.to_bool tuple.(2) in
    let rFix   = Tac2ffi.to_bool tuple.(3) in
    let rCofix = Tac2ffi.to_bool tuple.(4) in
    let rZeta  = Tac2ffi.to_bool tuple.(5) in
    let rDelta = Tac2ffi.to_bool tuple.(6) in
    let rConst = Tac2ffi.to_list Tac2ffi.to_reference tuple.(7) in
    Genredexpr.{rBeta; rMatch; rFix; rCofix; rZeta; rDelta; rConst; rStrength}
  in
  Tac2ffi.make_repr (fun _ -> assert false) to_red_flags

let _ =
  define "eval_whd"
    (bool @-> list ident @-> red_flags @-> constr @-> tac constr) @@
    fun with_local_opacity dbs flags c ->
  env >>= fun env ->
  evar_map >>= fun sigma ->
  let get_evaluable_reference = function
    | Names.GlobRef.VarRef id -> Proofview.tclUNIT [Evaluable.EvalVarRef id]
    | Names.GlobRef.ConstRef cst ->
        begin
          match Structures.PrimitiveProjections.find_opt cst with
          | None -> Proofview.tclUNIT [Evaluable.EvalConstRef cst]
          | Some p -> Proofview.tclUNIT [Evaluable.EvalProjectionRef p; Evaluable.EvalConstRef cst]
        end
    | r -> Proofview.tclZERO (Tacred.NotEvaluableRef r)
  in
  Proofview.Monad.List.map get_evaluable_reference flags.rConst >>= fun rConst ->
  let rConst = List.concat rConst in
  let ts =
    let ts =
      if with_local_opacity then
        Conv_oracle.get_transp_state (Environ.oracle env)
      else
        if flags.rDelta then TransparentState.full else TransparentState.empty
    in
    let add_ts_from_db ts_acc db =
      let db = Names.Id.to_string db in
      let ts = Hints.Hint_db.transparent_state (Hints.searchtable_map db) in
      TransparentState.inter ts_acc ts
    in
    let ts = List.fold_left add_ts_from_db ts dbs in
    let fn_delta ts egr =
      match egr with
      | Evaluable.EvalVarRef(x) -> TransparentState.remove_var ts x
      | Evaluable.EvalConstRef(c) -> TransparentState.remove_cst ts c
      | Evaluable.EvalProjectionRef(p) -> TransparentState.remove_prj ts p
    in
    let fn_no_delta ts egr =
      match egr with
      | Evaluable.EvalVarRef(x) -> TransparentState.add_var ts x
      | Evaluable.EvalConstRef(c) -> TransparentState.add_cst ts c
      | Evaluable.EvalProjectionRef(p) -> TransparentState.add_prj ts p
    in
    List.fold_left (if flags.rDelta then fn_delta else fn_no_delta) ts rConst
  in
  let reds =
    let open RedFlags in
    let reds = no_red in
    let reds = if flags.rBeta  then red_add reds fBETA  else reds in
    let reds = if flags.rMatch then red_add reds fMATCH else reds in
    let reds = if flags.rFix   then red_add reds fFIX   else reds in
    let reds = if flags.rCofix then red_add reds fCOFIX else reds in
    let reds = if flags.rZeta  then red_add reds fZETA  else reds in
    red_add_transparent (red_add reds fDELTA) ts
  in
  let evars =
    let evar_expand ev = Evd.existential_expand_value0 sigma ev in
    let qvar_irrelevant q =
      let open UState in
      match nf_qvar (Evd.ustate sigma) q with
      | QConstant QSProp -> true
      | _ -> false
    in
    let evar_irrelevant (evk, _) =
      match Evd.find sigma evk with
      | exception Not_found -> true
      | Evd.EvarInfo evi ->
      Evd.is_relevance_irrelevant sigma (Evd.evar_relevance evi)
    in
    let evar_repack (ev, args) =
      let args = List.map EConstr.of_constr args in
      EConstr.Unsafe.to_constr (EConstr.mkLEvar sigma (ev, args))
    in
    CClosure.{evar_expand; evar_repack; qvar_irrelevant; evar_irrelevant}
  in
  let infos = create_clos_infos ~evars reds env in
  let tabs = CClosure.create_tab () in
  let c = CClosure.inject (EConstr.Unsafe.to_constr c) in
  let c = CClosure.whd_val infos tabs c in
  Proofview.tclUNIT (EConstr.of_constr c)

(* [gen_evar] generates and returns an evar of type [ev_ty]. *)
let _ =
  define "gen_evar"
    (bool @-> constr @-> tac constr) @@ fun typeclass_candidate ev_ty ->
  Proofview.Goal.enter_one @@ fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let (sigma, evar) =
    Evarutil.new_evar ~typeclass_candidate env sigma ev_ty
  in
  Proofview.Unsafe.tclEVARS sigma >>= fun _ ->
  Proofview.tclUNIT evar

let _ =
  define "remove_future_goal" (evar @-> tac unit) @@ fun ev ->
  Proofview.Goal.enter_one @@ fun gl ->
  let sigma = Proofview.Goal.sigma gl in
  Proofview.Unsafe.tclEVARS (Evd.remove_future_goal sigma ev)

let _ =
  define "constr_eq_nounivs"
    (constr @-> constr @-> eret bool) @@ fun x y _ sigma ->
  EConstr.eq_constr_nounivs sigma x y

let _ =
  define "has_undef_evar" (constr @-> eret bool) @@ fun c _ sigma ->
  Evarutil.has_undefined_evars sigma c

let _ =
  define "subst_evars" (constr @-> eret (option constr)) @@ fun c _ sigma ->
  Option.map EConstr.of_constr (EConstr.to_constr_opt sigma c)

(* [infer_conv] is used in the [assumption] tactic. We expose it to mirror the same behavior. *)
let _ =
  define "infer_conv" (constr @-> constr @-> tac bool) @@ fun x y ->
  Proofview.Goal.enter_one @@ fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  match (Reductionops.infer_conv env sigma x y) with
  | Some sigma ->
      Proofview.Unsafe.tclEVARS sigma >>= fun _ -> Proofview.tclUNIT true
  | None ->
      Proofview.tclUNIT false

(* Vars functions *)

let _ =
  define "vars_closedn" (int @-> constr @-> eret bool) @@ fun n c _ sigma ->
  Vars.closedn n (EConstr.to_constr ~abort_on_undefined_evars:false sigma c)

let _ =
  define "vars_noccur_between"
    (int @-> int @-> constr @-> eret bool) @@ fun n m c _ sigma ->
  Vars.noccur_between n m (EConstr.to_constr ~abort_on_undefined_evars:false sigma c)

let _ =
  define "liftn" (int @-> int @-> constr @-> eret constr) @@ fun lift min c _ sigma ->
  let c = EConstr.to_constr ~abort_on_undefined_evars:false sigma c in
  let c = Constr.liftn lift min c in
  EConstr.of_constr c

let _ =
  define "vars_rels" (constr @-> eret (list int)) @@ fun c _ sigma ->
  let c = EConstr.to_constr ~abort_on_undefined_evars:false sigma c in
  let module S = Set.Make(Int) in
  let rels = ref S.empty in
  let rec go level c =
    match Constr.kind c with
    | Constr.Rel(k) -> if k > level then rels := S.add (k - level) !rels
    | _             -> Constr.iter_with_binders (fun level -> level + 1) go level c
  in
  go 0 c;
  S.elements !rels


let vars_of_constr c =
  let names = ref Names.Id.Set.empty in
  let rec go level c =
    match Constr.kind c with
    | Constr.Var(n) -> names := Names.Id.Set.add n !names
    | _             -> Constr.iter_with_binders (fun level -> level + 1) go level c
  in
  go 0 c;
  !names

let _ =
  define "vars_vars" (constr @-> eret valexpr) @@ fun c _ sigma ->
  let c = EConstr.to_constr ~abort_on_undefined_evars:false sigma c in
  let names = vars_of_constr c in
  let tag = Tac2core.ident_map_tag in
  let tag_set tag s = Tac2ffi.repr_of Tac2core.set_repr (Tac2core.TaggedSet (tag,s)) in
  tag_set tag names

let _ =
  define "vars_really_needed_unsafe" (constr @-> tac valexpr) @@ fun c ->
  TacUtil.evar_map >>= fun sigma ->
  TacUtil.env >>= fun env ->
  let c = EConstr.Unsafe.to_constr c in
  let names = vars_of_constr c in
  let named = Context.Named.map_het (EConstr.ERelevance.make) (EConstr.of_constr) (Environ.named_context env) in
  let names = Names.Id.Set.of_list @@ Termops.dependency_closure env sigma named names in
  let tag = Tac2core.ident_map_tag in
  let tag_set tag s = Tac2ffi.repr_of Tac2core.set_repr (Tac2core.TaggedSet (tag,s)) in
  Proofview.tclUNIT (tag_set tag names)

let _ =
  define "vars_really_needed" (constr @-> tac valexpr) @@ fun c ->
  TacUtil.evar_map >>= fun sigma ->
  TacUtil.env >>= fun env ->
  let c = EConstr.to_constr ~abort_on_undefined_evars:false sigma c in
  let names = vars_of_constr c in
  let named = Context.Named.map_het (EConstr.ERelevance.make) (EConstr.of_constr) (Environ.named_context env) in
  let names = Names.Id.Set.of_list @@ Termops.dependency_closure env sigma named names in
  let tag = Tac2core.ident_map_tag in
  let tag_set tag s = Tac2ffi.repr_of Tac2core.set_repr (Tac2core.TaggedSet (tag,s)) in
  Proofview.tclUNIT (tag_set tag names)

let _ =
  define "entirely_closed" (constr @-> eret bool) @@ fun c env sigma ->
  let exception Fail in
  let rec go j c =
    match EConstr.kind sigma c with
    | Rel(i)  -> if i > j then raise Fail
    | Var(n)  ->
        begin
          match Environ.named_body n env with
          | None    -> raise Fail
          | Some(b) -> go j (EConstr.of_constr b)
          | exception Not_found -> raise Fail
        end
    | Evar(_) -> raise Fail
    | _       -> EConstr.iter_with_binders sigma Stdlib.succ go j c
  in
  try go 0 c; true with Fail -> false


(* Binder functions *)

let relevance =
  let of_relevance r =
    match r with
    | Sorts.Relevant       -> ValInt 0
    | Sorts.Irrelevant     -> ValInt 1
    | Sorts.RelevanceVar _ -> assert false (* FIXME? *)
  in
  let to_relevance v =
    match v with
    | ValInt 0 -> Sorts.Relevant
    | ValInt 1 -> Sorts.Irrelevant
    | _        -> assert false
  in
  make_repr of_relevance to_relevance

let _ =
  define "debug_print" (constr @-> ret pp) @@ fun c ->
  Constr.debug_print (EConstr.Unsafe.to_constr c)

let _ =
  define "mkProj" (constant @-> bool @-> constr @-> eret (option constr)) @@ fun const b x _env sigma ->
  let proj = (Structures.PrimitiveProjections.find_opt const) in
  Option.map (fun p -> EConstr.of_constr (Constr.mkProj (Names.Projection.make p b, Sorts.Relevant, EConstr.to_constr ~abort_on_undefined_evars:false sigma x))) proj

(* Evar functions *)

let _ =
  define "rename_evar" (evar @-> ident @-> tac unit) @@ fun evar name ->
  with_evarmap @@ fun sigma ->
  let current_name = Evd.evar_ident evar sigma in
  match current_name with
  | Some cname when Names.Id.equal cname name ->
      Proofview.tclUNIT ()
  | Some _ | None ->
      Proofview.Unsafe.tclEVARS (Evd.rename evar name sigma)

let _ =
  define "evar_name" (evar @-> eret (option ident)) @@ fun evar _ sigma ->
  Evd.evar_ident evar sigma

let _ =
  define "evar_is_undefined" (evar @-> tac bool) @@ fun evar ->
  with_evarmap @@ fun sigma ->
  Proofview.tclUNIT (Evd.is_undefined sigma evar)

(* Pretyping *)

let _ =
  define "constr_pretype_at" (option bool @-> option constr @-> preterm @-> tac valexpr) @@ fun use_tc ty c ->
    Tac2core.pf_apply @@ fun env sigma ->
    try
      let Ltac_pretype.{closure = {typed; untyped; idents; _}; term} = c in
      let vars =
        Ltac_pretype.{
          ltac_constrs = typed;
          ltac_uconstrs = untyped;
          ltac_idents = idents;
          ltac_genargs = Names.Id.Map.empty;
        }
      in
      let flags = match use_tc with
        | Some fail -> Pretyping.default_inference_flags fail
        | None -> Pretyping.no_classes_no_fail_inference_flags
      in
      let (sigma, t) =
        let ty = Pretyping.(Option.cata (fun ty -> OfType ty) WithoutTypeConstraint ty) in
        Pretyping.understand_ltac flags env sigma vars ty term
      in
      Proofview.Unsafe.tclEVARS sigma >>= fun _ ->
      Proofview.tclUNIT (Tac2ffi.of_constr t)
    with
    | Logic_monad.Exception _ as e -> raise e
    | e when CErrors.noncritical e ->
      let (e,info) = Exninfo.capture e in Proofview.tclZERO ~info e

(* Retyping *)
let _ =
  define "constr_retype" (constr @-> tac constr) @@ fun c ->
  Tac2core.pf_apply @@ fun env sigma ->
  try Proofview.tclUNIT (Retyping.get_type_of ~lax:true env sigma c)
  with
  | Logic_monad.Exception _ as e -> raise e
  | e when CErrors.noncritical e ->
      let (e,info) = Exninfo.capture e in
      Proofview.tclZERO ~info e


(** ... *)
module RelDecl = struct
  open Proofview
  open Proofview.Notations

  type binder = Names.Name.t EConstr.binder_annot * EConstr.types

  type t =
    | Assum of binder
    | Def of binder * EConstr.t

  let of_val : Tac2val.valexpr -> t = fun v ->
    let open Tac2ffi in
    match v with
    | ValBlk(0, [|b|]   ) -> Assum(repr_to binder b)
    | ValBlk(1, [|b; t|]) -> Def(repr_to binder b, to_constr t)
    | _                   -> assert false

  let to_val : t -> Tac2val.valexpr = fun _ -> assert false

  let repr = Tac2ffi.make_repr to_val of_val

  let make_evar : bool -> bool -> t list -> Evd.econstr -> (Evd.evar_map * EConstr.t Constr.pexistential) tactic =
      fun empty typeclass_candidate rds goal_ty ->
    Goal.enter_one @@ fun gl ->
    let sigma = Goal.sigma gl in
    let env = if empty then Environ.empty_env else Proofview.Goal.env gl in
    let fresh_id =
      let count = ref 0 in
      fun () ->
        incr count;
        Names.Id.of_string (Printf.sprintf "_make_evar_%i_" !count)
    in
    let add rd (subst, env) =
      let to_id id =
        let open Names.Name in
        let id_set =
          Environ.ids_of_named_context_val (Environ.named_context_val env)
        in
        match id with
        | Name(id)  -> Namegen.next_ident_away id id_set
        | Anonymous -> fresh_id ()
      in
      let assum =
        let open Context.Named.Declaration in
        let substitute =
          let subst = List.rev subst in
          EConstr.Vars.substnl subst 0
        in
        let to_constr t =
          let t = substitute t in
          EConstr.to_constr ~abort_on_undefined_evars:false sigma t
        in
        match rd with
        | Assum((id,ty)) ->
            let id = Context.map_annot to_id id in
            let id = Context.map_annot_relevance_het (EConstr.ERelevance.kind sigma) id in
            let ty = to_constr ty in
            LocalAssum(id, ty)
        | Def((id,ty),t) ->
            let id = Context.map_annot to_id id in
            let id = Context.map_annot_relevance_het (EConstr.ERelevance.kind sigma) id in
            let ty = to_constr ty in
            let t  = to_constr t  in
            LocalDef(id, ty, t)
      in
      let id = Context.Named.Declaration.get_id assum in
      (EConstr.mkVar id :: subst, Environ.push_named assum env)
    in
    let (subst, env) = List.fold_right add rds ([], env) in
    let goal_ty = EConstr.Vars.substnl subst 0 goal_ty in
    let (sigma, c) =
      Evarutil.new_evar ~typeclass_candidate env sigma goal_ty
    in
    Unsafe.tclEVARS sigma >>= fun _ ->
    tclUNIT (sigma, EConstr.destEvar sigma c)

  let _ =
    define "make_evar_in_level_env"
      (bool @-> bool @-> list repr @-> constr @-> tac (pair evar (array constr)))
      @@ fun emp b rds t ->
    make_evar emp b rds t >>= fun (sigma, (ev, args)) ->
    let args = Evd.expand_existential sigma (ev,args) in
    Proofview.tclUNIT (ev, Array.of_list args)

end

(* Used for implementing [Obj.magic] in Ltac2. *)
let _ = define "id" (valexpr @-> ret valexpr) Fun.id

let _ =
  define "define_evar" (evar @-> constr @-> tac bool) @@ fun ev v ->
  Proofview.Goal.enter_one @@ fun gl ->
  let open Proofview in
  let sigma = Goal.sigma gl in
  if Evd.is_defined sigma ev then
    tclUNIT false
  else
    Unsafe.tclEVARS (Evd.define ev v sigma) >>= fun _ -> tclUNIT true

let _ =
  define "restrict_evar" (list bool @-> evar @-> tac evar) @@ fun ls e ->
  Proofview.Goal.enter_one @@ fun gl ->
  let sigma = Proofview.Goal.sigma gl in
  let info = Evd.find_undefined sigma e in
  let filter = Evd.Filter.apply_subfilter (Evd.evar_filter info) ls in
  let sigma, e = Evarutil.restrict_evar sigma e filter None in
  let open Proofview.Notations in
  Proofview.Unsafe.tclEVARSADVANCE sigma >>= fun _ ->
  Proofview.tclUNIT e


module HintDb = struct
  let tag : Hints.hint_db Tac2dyn.Val.tag = Tac2dyn.Val.create "hint_db"
  let repr : Hints.hint_db Tac2ffi.repr = Tac2ffi.repr_ext tag
end

let _ =
  define "find_hint_db" (ident @-> ret (option HintDb.repr)) @@ fun id ->
  let id = Names.Id.to_string id in
  try Some(Hints.searchtable_map id) with Not_found -> None

let _ =
  define "typeclasses_eauto_dbs"
    (valexpr @-> list HintDb.repr @-> tac unit) @@ fun config dbs ->
  let (unique, only_classes, best_effort, strategy, depth, dep) =
    match to_tuple config with
    | [|unique; only_classes; best_effort; strategy; depth; dep|] ->
        (unique, only_classes, best_effort, strategy, depth, dep)
    | _ -> assert false
  in
  let unique = Tac2ffi.to_bool unique in
  let only_classes = Tac2ffi.to_bool only_classes in
  let best_effort = Tac2ffi.to_bool best_effort in
  let strategy =
    match Tac2ffi.to_int strategy with
    | 0 -> Class_tactics.Dfs
    | 1 -> Class_tactics.Bfs
    | _ -> assert false
  in
  let depth = Tac2ffi.to_option Tac2ffi.to_int depth in
  let dep = Tac2ffi.to_bool dep in
  let st =
    match dbs with
    | db :: _ -> Hints.Hint_db.transparent_state db
    | _       -> TransparentState.full
  in
  let modes =
    let modes = List.map Hints.Hint_db.modes dbs in
    List.fold_left Hints.Modes.union Hints.Modes.empty modes
  in
  Class_tactics.Search.eauto_tac (modes, st) ~unique ~only_classes
    ~best_effort ~strategy ~depth ~dep dbs

let _ =
  define "is_class" (reference @-> ret bool) Typeclasses.is_class

(* Clean error reporting. *)

let _ =
  define "user_err" (pp @-> tac valexpr) @@ fun p ->
    Proofview.tclZERO (CErrors.UserError p)

(* [pattern_of_constr] *)
let _ =
  define "pattern_of_constr" (constr @-> eret pattern) @@ fun c env sigma ->
  Patternops.pattern_of_constr env sigma c

(* [specialize_products] *)
let _ =
  let exception Not_a_prod in
  let specialize env sigma c cs =
    let infos = CClosure.create_clos_infos RedFlags.all env in
    let tab = CClosure.create_tab () in
    let to_constr c =
      EConstr.to_constr ~abort_on_undefined_evars:false sigma c
    in
    let rec is_empty stk =
      match stk with
      | [] -> true
      | CClosure.Zupdate(_) :: stk -> is_empty stk
      | _ -> false
    in
    let fn c arg =
      let c =
        let (c, stk) = CClosure.whd_stack infos tab c [] in
        if is_empty stk then c else assert false
      in
      let (body, usubs) =
        match CClosure.fterm_of c with
        | FProd(_,_,body,usubs) -> (body, usubs)
        | _ -> raise Not_a_prod
      in
      let arg = CClosure.inject (to_constr arg) in
      let usubs = CClosure.usubs_cons arg usubs in
      CClosure.mk_clos usubs body
    in
    let c = Array.fold_left fn (CClosure.inject (to_constr c)) cs in
    let (c, stk) = CClosure.whd_stack infos tab c [] in
    EConstr.of_constr (CClosure.term_of_process c stk)
  in
  define "specialize_products"
    (constr @-> array constr @-> tac constr) @@ fun c cs ->
  Proofview.Goal.enter_one @@ fun goal ->
  let env = Proofview.Goal.env goal in
  let sigma = Proofview.Goal.sigma goal in
  try Proofview.tclUNIT (specialize env sigma c cs) with Not_a_prod ->
    Proofview.tclZERO (CErrors.UserError(Pp.str "Not enough products"))


(* Obtain the evar from the current focused goal. *)
let _ =
  define "goal_evar" (unit @-> tac evar) @@ fun _ ->
  Proofview.Goal.enter_one @@ fun g ->
  Proofview.tclUNIT (Proofview.Goal.goal g)

let _ = define "is_section_variable" (ident @-> ret bool) @@ fun id ->
  Termops.is_section_variable (Global.env ()) id (* do not use the local environment or the function will fail! *)

(* String functions *)
let err_outofbounds =
  let open Names in
  let core_prefix path n = KerName.make path (Label.of_id (Id.of_string_soft n)) in
  let coq_core n = core_prefix Tac2env.rocq_prefix n in
  Tac2interp.LtacError (coq_core "Out_of_bounds", [||])

let _ =
  define "string_sub" (bytes @-> int @-> int @-> tac bytes) @@ fun s pos len ->
  try Proofview.tclUNIT (Bytes.sub s pos len) with Invalid_argument _ -> Tac2core.throw err_outofbounds

(* TransparentState *)
let _ =
  define "transparent_state_of_db" (ident @-> ret transparent_state) @@ fun db ->
  let db = Hints.searchtable_map (Names.Id.to_string db) in
  Hints.Hint_db.transparent_state db

let _ =
  define "transparent_state_inter"
    (transparent_state @-> transparent_state @-> ret transparent_state)
    TransparentState.inter

(* case_bt *)

let () =
  let set_bt info =
    if !Tac2bt.print_ltac2_backtrace then
      Tac2bt.get_backtrace >>= fun bt ->
      Proofview.tclUNIT (Exninfo.add info Tac2bt.backtrace bt)
    else Proofview.tclUNIT info
  in

  let thaw f = Tac2val.apply f [Tac2ffi.of_unit ()] in

  define "case_bt" (closure @-> tac valexpr) @@ fun f ->
  Proofview.tclCASE (thaw f) >>= begin function
  | Proofview.Next (x, k) ->
    let k = Tac2val.mk_closure arity_one begin fun e ->
      let (e, info) = Tac2ffi.to_exn e in
      set_bt info >>= fun info ->
      k (e, info)
    end in
    Proofview.tclUNIT (Tac2ffi.of_block (0, [| Tac2ffi.of_tuple [| x; Tac2ffi.of_closure k |] |]))
  | Proofview.Fail e ->
    let bt = of_exninfo (snd e) in
    Proofview.tclUNIT (Tac2ffi.of_block (1, [| Tac2ffi.of_exn e; bt |]))
  end
