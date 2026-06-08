(*
 * Copyright (C) BlueRock Security Inc. 2024-2025
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

let option_prefix = ["HintDb"; "Opacity"; "Info"]

type equivalence =
  | Syntactic
  | Modulo of TransparentState.t

let evaluable_constant c env ts =
  (* Hack to work around a broken Print Module implementation, see #2668. *)
  (if Environ.mem_constant c env then Environ.evaluable_constant c env else true) &&
  Structures.PrimitiveProjections.is_transparent_constant ts c

let evaluable_named id env ts =
  (try Environ.evaluable_named id env with Not_found -> true) &&
  TransparentState.is_transparent_variable ts id

let make_ev_funs env equiv =
  match equiv with
  | Modulo ts ->
    (fun v -> evaluable_named v env ts),
    (fun c -> evaluable_constant c env ts)
  | Syntactic -> (fun _ -> false), (fun _ -> false)

module IntMap = Map.Make(Int)

module Label = struct
  type t =
  | GRLabel of Names.GlobRef.t
  | ProjLabel of Names.Projection.Repr.t
  | CaseLabel
  | Meta of Names.Id.t option
  | PatVar of Names.Id.t
  | Lambda
  | IfLabel

  let compare t1 t2 = match t1, t2 with
  | GRLabel gr1, GRLabel gr2 -> Names.GlobRef.UserOrd.compare gr1 gr2
  | ProjLabel pr1, ProjLabel pr2 -> Names.Projection.Repr.UserOrd.compare pr1 pr2
  | _ -> Stdlib.compare t1 t2 (** OK *)


  let get_fq_names : unit -> bool =
    let key = option_prefix @ ["Fully"; "Qualified"] in
    let getter =
      Goptions.declare_bool_option_and_ref
        ~key ~value:false ()
    in
    getter.Goptions.get

  let pr_globref r =
    if get_fq_names () then
      Libnames.pr_qualid (Libnames.qualid_of_path (Nametab.path_of_global r))
    else
      Printer.pr_global r


  let pr (l : t) =
    let open Pp in
    match l with
    | GRLabel gr -> pr_globref gr
    | ProjLabel gr ->
      pr_globref (Names.GlobRef.ConstRef (Names.Projection.Repr.constant gr))
    | CaseLabel -> str "<match>"
    | Meta o ->
      begin
        match o with
        | None -> str "?M_"
        | Some i -> str "?M" ++ Names.Id.print i
      end
    | PatVar v -> str "?P" ++ Names.Id.print v
    | Lambda -> str "<lambda>"
    | IfLabel -> str "<if>"
end


let ignore_outputs : unit -> bool =
  let key = option_prefix @ ["Ignore"; "Outputs"] in
  let getter =
    Goptions.declare_bool_option_and_ref
      ~key ~value:false ()
  in
  getter.Goptions.get

module ModeSet = struct
  include Set.Make(struct
    type t = Hints.hint_mode
    let compare = compare
  end)

  let pp (modes : t) =
    Pp.(str "{" ++ prlist_with_sep spc (Hints.pp_hint_mode) (elements modes) ++ str "}")

  let should_ignore (modes : t) =
    ignore_outputs () && equal modes (singleton Hints.ModeOutput)
end


module Res = struct
  type elt = (ModeSet.t * Label.t * Hints.FullHint.t) list
  type t = elt IntMap.t
  let empty : t = IntMap.empty
  let merge : t -> t -> t =
    IntMap.merge (fun _ o1 o2 ->
        match o1, o2 with
        | None, None -> None
        | (Some _), None -> o1
        | None, (Some _) -> o2
        | Some o1, Some o2 -> Some (List.append o1 o2)
      )
  let singleton depth mode label hint =
    IntMap.singleton depth ([mode, label, hint])
end


type term_label =
| GRLabel of Names.GlobRef.t
| ProjLabel of Names.Projection.Repr.t * int
 (** [ProjLabel (p, n)] represents a possibly partially applied projection [p]
     with [n] arguments missing to be fully applied. [n] is always zero for
     labels derived from [Proj] terms but can be greater than zero for labels
     derived from compatibility constants. *)
| ProdLabel
| SortLabel
| CaseLabel


let evaluable_constant c env ts =
  (* This is a hack to work around a broken Print Module implementation, see
     bug #2668. *)
  (if Environ.mem_constant c env then Environ.evaluable_constant c env else true) &&
  (match ts with None -> true | Some ts -> Structures.PrimitiveProjections.is_transparent_constant ts c)

let evaluable_named id env ts =
  (try Environ.evaluable_named id env with Not_found -> true) &&
  (match ts with None -> true | Some ts -> TransparentState.is_transparent_variable ts id)

let evaluable_projection p _env ts =
  (match ts with None -> true | Some ts -> TransparentState.is_transparent_projection ts (Names.Projection.repr p))


let label_of_opaque_constant env c stack =
  match Structures.PrimitiveProjections.find_opt c with
  | None -> (GRLabel (Names.GlobRef.ConstRef c), stack)
  | Some p ->
    let n_args_needed = Structures.Structure.projection_nparams env c + 1 in (* +1 for the record value itself *)
    let n_args_given = List.length stack in
    let n_args_missing = max (n_args_needed - n_args_given) 0 in
    let n_args_drop = min (n_args_needed - 1) n_args_given in (* we do not drop the record value from the stack *)
    (ProjLabel (p, n_args_missing), CList.skipn n_args_drop stack)

type aux =
  | Cont of (term_label * (int * Pattern.constr_pattern) list)
  | Result of int * Label.t
  | Done

let constr_pat_discr env ts depth p : aux =
  let open Names.GlobRef in
  let open Pattern in
  let rec decomp depth stack p : aux =
    match p with
    | PApp (f,args) -> decomp depth (List.map (fun a -> (depth+1, a)) (Array.to_list args) @ stack) f
    | PProj (p,_) when evaluable_projection p env ts -> Result (depth, Label.ProjLabel (Names.Projection.repr p))
    | PProj (p,c) -> Cont (ProjLabel (Names.Projection.repr p, 0), (depth, c) :: stack)
    | PRef ((IndRef _) as ref)
    | PRef ((ConstructRef _ ) as ref) ->
      let ref = Environ.QGlobRef.canonize env ref in
      Cont (GRLabel ref, stack)
    | PRef (VarRef v) when evaluable_named v env ts -> Result (depth, Label.GRLabel (VarRef v))
    | PRef ((VarRef _) as ref) -> Cont (GRLabel ref, stack)
    | PRef (ConstRef c) when evaluable_constant c env ts -> Result (depth, Label.GRLabel (ConstRef c))
    | PRef (ConstRef c) ->
      let c = Environ.QConstant.canonize env c in
      Cont (label_of_opaque_constant env c stack)
    | PVar v when evaluable_named v env ts -> Result (depth, Label.PatVar v)
    | PVar v -> Cont (GRLabel (VarRef v), stack)
    | PProd (_,d,c) when stack = [] -> Cont (ProdLabel, [(depth, d) ; (depth, c)])
    | PSort _ when stack = [] -> Cont (SortLabel, [])
    | PCase(_,_,p,_) | PIf(p,_,_) ->
      begin
        match decomp (depth + 1) stack p with
        | Cont (GRLabel (ConstructRef _), _) -> Result (depth, Label.CaseLabel) (* over-approximating w.r.t. [fMATCH] *)
        | Cont _ -> Cont (CaseLabel, (depth, p) :: stack)
        | r -> r
      end
    | _ -> Done
  in
  decomp depth [] (Rocq_internals.eta_reduce_pat p)

let pr_hint (hint : Hints.FullHint.t) =
  let open Pp in
  let pr_type =
    match Hints.FullHint.repr hint with
    | Hints.ERes_pf _ -> str "Hint Resolve [Eauto]"
    | Hints.Res_pf _ -> str "Hint Resolve [Auto]"
    | Hints.Give_exact _ -> str "Hint Resolve [Exact]"
    | Hints.Extern _ -> str "Hint Extern"
    | Hints.Res_pf_THEN_trivial_fail _ -> str "Hint Immediate"
    | Hints.Unfold_nth _ -> str "Hint Unfold"
  in
  let open Pp in
  hov 2 (
    pr_type ++ spc () ++ str "(" ++ Hints.FullHint.print (Global.env()) Evd.empty hint ++ str ")"
  )

let no_pattern_warning =
  CWarnings.create ~name:"db-opacity-info-missing-pattern"
    Pp.(fun h ->
        hov 2 (
          str "Hint has no pattern:" ++ spc () ++
          pr_hint h
        )
      )

let exotic_pattern_warning =
  CWarnings.create ~name:"db-opacity-info-exotic-pattern"
    Pp.(fun (cls, h) ->
        hov 2 (
          str "Hint pattern does not start with its class (" ++ Printer.pr_global cls ++ str "):" ++ spc () ++
          pr_hint h
        )
      )


let results_for env ts (cls, h, modes) p : Res.t =
  let rec go mode acc state =
    match state with
    | Done -> acc
    | Result(d,l) -> Res.merge (Res.singleton d mode l h) acc
    | Cont (_, stack) ->
      List.fold_left (fun acc (depth, p) ->
        go mode acc (constr_pat_discr env ts depth p)
      ) acc stack
  in
  let open Pattern in
  match p with
  | PRef h when Names.GlobRef.CanOrd.equal cls h ->
    Res.empty
  | PApp (PRef h, args) when Names.GlobRef.CanOrd.equal cls h  ->
    let depth = 1 in
    CArray.fold_left_i (fun i acc p ->
        let m = if i < Array.length modes then Array.get modes i else ModeSet.empty in
        go m acc (constr_pat_discr env ts depth p)
      ) Res.empty args
  | _ ->
    exotic_pattern_warning (cls, h);
    Res.empty


(* let results_for : Environ.env -> equivalence -> int *)
(*     -> Pattern.constr_pattern -> Res.t = fun env equiv -> *)
(*   let ev_named, ev_const = make_ev_funs env equiv in *)
(*   let rec pattern depth pat = *)
(*     let open Names.GlobRef in *)
(*     let open Pattern in *)
(*     let app args = *)
(*       let pattern = pattern (depth + 1) in *)
(*       (\* FIXME avoid conversion between lists and arrays *\) *)
(*       Array.fold_left (fun r x -> Res.merge r (pattern x)) Res.empty (Array.of_list args) *)
(*     in *)
(*     if depth > !Btermdn.dnet_depth then Res.empty else *)
(*     let (head, args) = decomp_pat pat in *)
(*     match head with *)
(*     | PRef(VarRef(v))   when ev_named v -> Res.singleton depth (GRLabel (VarRef(v))) *)
(*     | PRef(ConstRef(c)) when ev_const c -> Res.singleton depth (GRLabel (ConstRef(c))) *)
(*     | PRef(_)                           -> app args *)
(*     | PVar(v)           when ev_named v -> Res.singleton depth (PatVar v) *)
(*     | PVar(_)                           -> app args *)
(*     | PLambda(_, _, _)                  -> Res.singleton depth Lambda *)
(*     | PSort(_)                          -> assert false *)
(*     | PIf(v, _, _)                      -> app (v :: args) *)
(*     | PCase(_, _, v, _)                 -> app (v :: args) *)
(*     | PMeta(m)                          -> Res.singleton depth (Meta m) *)
(*     | _                                 -> Res.empty *)
(*   in *)
(*   pattern *)


let hint_pattern env sigma (h : Hints.FullHint.t) =
  let open Hints.FullHint in
  match pattern h with
  | Some(_) as pat -> pat
  | _ ->
    match repr h with
    | Hints.Res_pf h
    | Hints.ERes_pf h
      (* NOTE we should be able to call [Clenv.clenv_type], but we do not have
         a way to do so without [Obj] hacks. *)
      (*
      let clnv = Obj.obj (Obj.field (Obj.repr h) 3) in
      let ty = Clenv.clenv_type clnv in
      Some(Patternops.pattern_of_constr env sigma ty)
      *)
    | Hints.Res_pf_THEN_trivial_fail h
    | Hints.Give_exact h ->
      let (_, t) = Hints.hint_as_term h in
      let ty = Retyping.get_type_of env sigma t in
      (* Coq performs full beta iota reduction on hint types that have quantifiers.
         We deviate slightly from this by reducing even when there are no quantifiers.
      *)
      let ty = Reductionops.nf_betaiota env sigma ty in

      (* Code until the last line is not necessary for [Give_exact]. *)
      (* Get the unsubsituted types of the binders (in order) and the body. *)
      let (bs, ty) =
        let rec strip_prods reduced bs ty =
          match EConstr.kind sigma ty with
          | Constr.Prod (b, a, ty) -> strip_prods false ((b,a) :: bs) ty
          | _ when not reduced ->
          (* handling let bindings and other things that get in the way of
             finding a class in head position *)
            let ty = Reductionops.clos_whd_flags RedFlags.(mkflags [fZETA; fBETA]) env sigma ty in
            strip_prods true bs ty
          | _ (* when reduced *) -> (List.rev bs, ty)
        in
        strip_prods false [] ty
      in
      (* Substitute metavariable. *)
      let (sigma, metas) =
        let rec make_evars i evars sigma bs =
          match bs with
          | [] -> (sigma, evars)
          | (b,a) :: bs ->
          let a = EConstr.Vars.substnl evars 0 a in
          let name = (Names.Id.of_string ("H" ^ (string_of_int i)), false) in
          let relevance = Context.binder_relevance b in
          let typeclass_candidate = false in
          let src = (None, Evar_kinds.MatchingVar (Evar_kinds.FirstOrderPatVar (fst name))) in
          let (sigma, evar) = Evd.new_pure_evar ~src ~relevance ~name ~typeclass_candidate Environ.empty_named_context_val sigma a in
          let evar = EConstr.mkEvar (evar, SList.empty) in
          make_evars (i+1) (evar :: evars) sigma bs
        in
        make_evars 0 [] sigma bs
      in
      let ty = EConstr.Vars.substnl metas 0 ty in
      Some(Patternops.pattern_of_constr env sigma ty)
    | _ -> None


let merge_modes = function
  | None -> [||]
  | Some ls ->
    let len = List.fold_left max 0 (List.map Array.length ls) in
    let acc = Array.make len ModeSet.empty in
    let f arr =
      let rec go i =
        if i < Array.length arr then
          begin
            acc.(i) <- ModeSet.add arr.(i) acc.(i);
            go (i + 1)
          end
      in
      go 0
    in
    List.iter f ls;
    acc



let go_db clss o_ts db_name =

  let results = ref Names.GlobRef.Map.empty in

  let db = Hints.searchtable_map (Names.Id.to_string db_name) in
  let modes = Hints.Hint_db.modes db in
  (* TODO: Unexpected breakage from https://github.com/coq/coq/pull/20201 *)
  let modes : Hints.hint_mode array list Names.GlobRef.Map.t = Obj.magic modes in
  let ts =
    match o_ts with
    | Some ts -> ts
    | None -> Hints.Hint_db.transparent_state db
  in

  let go_hint modes head hint =
    match hint_pattern (Global.env()) Evd.empty hint with
    | None -> no_pattern_warning hint
    | Some pat ->
      let res = results_for (Global.env()) (Some ts) (head,hint,modes) pat in
      results := Names.GlobRef.Map.update head (fun o -> match o with None -> Some res | Some r -> Some (Res.merge res r)) (!results)
  in
  List.iter (fun r ->
      let modes = Names.GlobRef.Map.find_opt r modes in
      let modes = merge_modes modes in
      let hints = Hints.Hint_db.map_all ~secvars:Names.Id.Pred.empty r db in
      List.iter (go_hint modes r) hints;
      let open Pp in
      let out = Feedback.msg_info in
      out (str "Db: " ++ Names.Id.print db_name);
      Names.GlobRef.Map.iter (fun k res ->
        out (str "Class: " ++ Printer.pr_global k);
        let fn _ elems =
          let f (modes, l, hint) =
            if not (ModeSet.should_ignore modes) then
              Some (Label.pr l ++ spc ()
                    ++ str "(modes " ++ ModeSet.pp modes ++ str ")" ++ spc ()
                    ++ str "in" ++ spc () ++ pr_hint hint)
            else
              None
          in
          let elems = CList.map_filter f elems in
          if elems = [] then None else Some elems
        in
        let res = IntMap.filter_map fn res in
        if IntMap.is_empty res then
          out (str "No transparent terms found.")
        else
        let _ = () in
        out (str "Transparent terms per depth:");
        IntMap.iter (fun d elems ->
            out (str "Depth " ++ int d ++ str "" ++ fnl () ++
                 spc () ++ spc () ++
                 h (
                   prlist_with_sep fnl (fun x -> x) elems
                 )
                )
        ) res
      ) (!results)
    ) clss

let db_opacity_info dbs o_opacity_db clss =
  let o_ts =
    match o_opacity_db with
    | Some db ->
      let db = Hints.searchtable_map (Names.Id.to_string db) in
      let ts = Hints.Hint_db.transparent_state db in
      Some ts
    | None -> None
  in
  List.iter (go_db clss o_ts) dbs


open Ltac2_plugin
open Tac2ffi
open Tac2externals

let define s = define { mltac_plugin = "tc_db_info"; mltac_tactic = s }

let () =
  define "db_opacity_info" (option ident @-> list ident @-> list reference @-> ret unit) @@
  fun o_ts dbs clss ->
  db_opacity_info dbs o_ts clss
