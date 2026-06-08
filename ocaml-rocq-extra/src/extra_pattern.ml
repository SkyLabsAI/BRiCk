(*
 * Copyright (C) 2023-2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

open Pattern

type t = constr_pattern

let map_w_binders : ('a -> int -> 'a) -> ('a -> t -> t) -> 'a -> t -> 'b =
  fun g f n p ->
  match p with
  | PRef(_)
  | PVar(_)
  | PEvar(_)
  | PRel(_)
  | PSort(_)
  | PMeta(_)
  | PInt(_)
  | PString(_)
  | PFloat(_) -> p
  | PApp(p, ps) ->
      let p = f n p in
      let ps = Array.map (f n) ps in
      PApp(p, ps)
  | PSoApp(v, ps) ->
      let ps = List.map (f n) ps in
      PSoApp(v, ps)
  | PProj(j,p) ->
      PProj(j, f n p)
  | PLambda(x, p1, p2) ->
      let p1 = f n p1 in
      let p2 = f (g n 1) p2 in
      PLambda(x, p1, p2)
  | PProd(x, p1, p2) ->
      let p1 = f n p1 in
      let p2 = f (g n 1) p2 in
      PProd(x, p1, p2)
  | PLetIn(x, p1, po, p2) ->
      let p1 = f n p1 in
      let po = Option.map (f n) po in
      let p2 = f (g n 1) p2 in
      PLetIn(x, p1, po, p2)
  | PIf(pi, pt, pe) ->
      let pi = f n pi in
      let pt = f n pt in
      let pe = f n pe in
      PIf(pi, pt, pe)
  | PCase(cip, o, p, cases) ->
      let o =
        Option.map (fun (ns, p) ->
          (ns, f (g n (Array.length ns)) p)
        ) o
      in
      let p = f n p in
      let cases =
        let f (i, ns, p) =
          (i, ns, f (g n (Array.length ns)) p)
        in
        List.map f cases
      in
      PCase(cip, o, p, cases)
  | PFix(r, (ns, ps1, ps2)) ->
      let ps1 = Array.map (f n) ps1 in
      let ps2 = Array.map (f (g n (Array.length ns))) ps2 in
      PFix(r, (ns, ps1, ps2))
  | PCoFix(i, (ns, ps1, ps2)) ->
      let ps1 = Array.map (f n) ps1 in
      let ps2 = Array.map (f (g n (Array.length ns))) ps2 in
      PCoFix(i, (ns, ps1, ps2))
  | PArray(ps, p1, p2) ->
      let ps = Array.map (f n) ps in
      let p1 = f n p1 in
      let p2 = f n p2 in
      PArray(ps, p1, p2)
  | PExtra(e) -> Util.Empty.abort e

let fold_with_binders : type a b. (a -> int -> a) -> (a -> b -> t -> b) -> a -> b -> t -> b =
  fun g f n acc p ->
  match p with
  | PRef(_)
  | PVar(_)
  | PEvar(_)
  | PRel(_)
  | PSort(_)
  | PMeta(_)
  | PInt(_)
  | PFloat(_) 
  | PString(_) -> acc
  | PApp(p, ps) ->
      f n (Array.fold_left (f n) acc ps) p
  | PSoApp(_, ps) ->
      List.fold_left (f n) acc ps
  | PProj(_,p) ->
      f n acc p
  | PLambda(_, p1, p2) ->
      f n (f (g n 1) acc p2) p1
  | PProd(_, p1, p2) ->
      f n (f (g n 1) acc p2) p1
  | PLetIn(_, p1, po, p2) ->
    let acc = f (g n 1) acc p2 in
    let acc = match po with
      | Some p -> f n acc p
      | None -> acc
    in
    f n acc p1
  | PIf(pi, pt, pe) ->
      let acc = f n acc pi in
      let acc = f n acc pt in
      let acc = f n acc pe in
      acc
  | PCase(_, o, p, cases) ->
      let acc =
        match o with
        | Some (ns, p) ->
          f (g n (Array.length ns)) acc p
        | None -> acc
      in
      let acc = f n acc p in
      let acc =
        let f acc (_, ns, p) =
          f (g n (Array.length ns)) acc p
        in
        List.fold_left f acc cases
      in
      acc
  | PFix(_, (ns, ps1, ps2)) ->
      let acc = Array.fold_left (f n) acc ps1 in
      let acc = Array.fold_left (f (g n (Array.length ns))) acc ps2 in
      acc
  | PCoFix(_, (ns, ps1, ps2)) ->
      let acc = Array.fold_left (f n) acc ps1 in
      let acc = Array.fold_left (f (g n (Array.length ns))) acc ps2 in
      acc
  | PArray(ps, p1, p2) ->
      let acc = Array.fold_left (f n) acc ps in
      let acc = f n acc p1 in
      let acc = f n acc p2 in
      acc
  | PExtra(e) -> Util.Empty.abort e

let rec subst : offset:int -> t -> t array -> t = fun ~offset p args ->
  let fun_subst offset p = subst ~offset p args in
  match p with
  | PEvar(_) -> assert false
  | PRel(i) ->
      let ind = i - offset - 1 in
      if 0 <= ind && ind < Array.length args then args.(ind) else p
  | _ ->
      map_w_binders (fun offset binders -> offset + binders) fun_subst offset p

let term_of_pattern initial_env sigma p =
  let open Pattern in
  let sigma = ref sigma in
  let new_evar =
    let idmap = ref Names.Id.Map.empty in
    fun env oid ->
    let new_evar env =
      let (sigma', (ev_ty, _)) =
        Evarutil.new_type_evar env !sigma Evd.UnivRigid
      in
      let (sigma', ev) = Evarutil.new_evar env sigma' ev_ty in
      sigma := sigma'; ev
    in
    match oid with
    | None     -> new_evar env
    | Some(id) ->
    match Names.Id.Map.find_opt id !idmap with
    | Some(ev) -> ev
    | None     ->
    let ev = new_evar initial_env in
    idmap := Names.Id.Map.add id ev !idmap; ev
  in
  let rec go env (p : constr_pattern) =
    let binder env mk n ty p =
      let ty = go env ty in
      let ty_c = EConstr.to_constr ~abort_on_undefined_evars:false (!sigma) ty in
      let n =
        let r = Relevanceops.relevance_of_term env ty_c in
        Context.make_annot n r
      in
      let body =
        let x = Context.Rel.Declaration.LocalAssum(n, ty_c) in
        go (Environ.push_rel x env) p
      in
      let n = Context.map_annot_relevance_het EConstr.ERelevance.make n in
      mk (n, ty, body)
    in
    match p with
    | PRef(r)               ->
        let (sigma', t) = EConstr.fresh_global env !sigma r in
        sigma := sigma'; t
    | PVar(v)               -> EConstr.mkVar v
    | PEvar((e, ps))        ->
        let ts = List.map (go env) ps in
        EConstr.mkEvar (e, SList.of_full_list ts)
    | PRel(i)               -> EConstr.mkRel i
    | PApp(h, ps)           ->
        let h = go env h in
        let ts = Array.map (go env) ps in
        EConstr.mkApp (h, ts)
    | PProj(p, r)           -> EConstr.mkProj (p, EConstr.ERelevance.make Sorts.Relevant, go env r)
    | PLambda(n, ty, p)     -> binder env EConstr.mkLambda n ty p
    | PProd(n, ty, p)       -> binder env EConstr.mkProd n ty p
    | PLetIn(n, p1, p2, p3) ->
        let t1 = go env p1 in
        let mk (n, t2, t3) = EConstr.mkLetIn (n, t1, t2, t3) in
        let p2 = match p2 with Some(p2) -> p2 | None -> PMeta(None) in
        binder env mk n p2 p3
    | PMeta(oid)            -> new_evar env oid
    | PInt(i)               -> EConstr.mkInt i
    | PFloat(f)             -> EConstr.mkFloat f
    | PString(s)            -> EConstr.mkString s
    | PFix(_, _)            -> assert false
    | PCoFix(_, _)          -> assert false
    | PSoApp(_, _)          -> assert false
    | PSort(_)              -> assert false
    | PIf(_, _, _)          -> assert false
    | PCase(_, _, _, _)     -> assert false
    | PArray(_, _, _)       -> assert false
    | PExtra(e) -> Util.Empty.abort e
  in
  let t = go initial_env p in
  (!sigma, t)
