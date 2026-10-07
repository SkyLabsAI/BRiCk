(*
 * Copyright (C) 2022 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

let iterate = Util.iterate
module Decl = Context.Rel.Declaration

type 'a tactic = 'a Proofview.tactic
let evar_map = TacUtil.evar_map
module Value = TacUtil.Value
type valexpr = Value.valexpr
open TacUtil.Notations

(** * Iterators on constructors *)
(**
Were we to lift OCaml's [==] to an Ltac2 function, we could write
equivalent code in Ltac2. It's simpler to define everything in ML, in
part because we can reuse [EConstr]'s iterators, and in part because
putting just types in Coq module [Constr.Unsafe] makes that module
easier to read.
*)

module ArrayTac : sig
  val smart_map : ('a -> 'a tactic) -> 'a array -> 'a array tactic
end = struct

  (**
  Set [dest.(j) <- f src.(j) | i <= j < n], from left to right, and
  return [dest].

  Uses unsafe array ops.
  *)
  let rec smart_map_map (f : 'a -> 'b tactic) (src : 'a array)
      (dest : 'b array) (i : int) (n : int) : 'a array tactic =
    if i = n then return dest else
    f (Array.unsafe_get src i) >>= fun x ->
    Array.unsafe_set dest i x;
    smart_map_map f src dest (i + 1) n

  (**
  Evaluate [x_i := f src.(i) | 0 <= i < n], from left to right, and
  return either [src] (if [x_i == src.(i)] for all [i]) or a new array
  of the [x_i]s.

  Uses unsafe array ops.
  *)
  let rec smart_map_scan (f : 'a -> 'a tactic) (src : 'a array)
      (i : int) (n : int) : 'a array tactic =
    if i = n then return src else
    let x = Array.unsafe_get src i in
    f x >>= fun x' ->
    if x == x' then smart_map_scan f src (i + 1) n
    else begin
      let dest = Array.make n x' in
      Array.blit src 0 dest 0 i;
      smart_map_map f src dest (i + 1) n
    end

  let smart_map (f : 'a -> 'a tactic) (src : 'a array) : 'a array tactic =
    smart_map_scan f src 0 (Array.length src)

end

module SListTac = struct

  let rec smart_map (f : 'a -> 'a tactic) (xs0 : 'a SList.t) : 'a SList.t tactic =
    match xs0 with
    | SList.Nil -> return SList.empty
    | SList.Default(i, xs) ->
      smart_map f xs >>= fun xs' ->
      return (if xs == xs' then xs0 else SList.defaultn i xs')
    | SList.Cons(x, xs) ->
      f x >>= fun x' ->
      smart_map f xs >>= fun xs' ->
      return (if x == x' && xs == xs' then xs0 else SList.cons x' xs')

end

module ListTac = struct

  let rec smart_map (f : 'a -> 'a tactic) (xs0 : 'a list) : 'a list tactic =
    match xs0 with
    | [] -> return []
    | x :: xs ->
      f x >>= fun x' ->
      smart_map f xs >>= fun xs' ->
      return (if x == x' && xs == xs' then xs0 else x' :: xs')

end

module ConstrTac = struct
  open Constr

  let map_invert (f : 'a -> 'a tactic) (ci0 : 'a pcase_invert) :
      'a pcase_invert tactic =
    match ci0 with
    | NoInvert -> return ci0
    | CaseInvert {indices} ->
      ArrayTac.smart_map f indices >>= fun indices' ->
      return (
        if indices == indices' then ci0
        else CaseInvert {indices=indices'}
      )

  let map_return_predicate (type a r) (f : a -> a tactic) (p0 : (a,r) pcase_return) :
      (a,r) pcase_return tactic =
    let ((bs, t), r) = p0 in
    f t >>= fun t' ->
    return (if t == t' then p0 else ((bs,t'), r))

  let map_return_predicate_with_binders
      (g : 'c -> 'c) (f : 'c -> 'a -> 'a tactic)
      (n : 'c) (p0 : ('a,'r) pcase_return) : ('a,'r) pcase_return tactic =
    let ((bs, t), r) = p0 in
    f (iterate g (Array.length bs) n) t >>= fun t' ->
    return (if t == t' then p0 else ((bs,t'), r))

  let map_branches (f : 'a -> 'a tactic) (brs : ('a,'r) pcase_branch array) :
      ('a,'r) pcase_branch array tactic =
    let f (br0 : ('a,'r) pcase_branch) : ('a,'r) pcase_branch tactic =
      let bs, c = br0 in
      f c >>= fun c' ->
      return (if c == c' then br0 else (bs,c'))
    in
    ArrayTac.smart_map f brs

  let map_branches_with_binders (g : 'c -> 'c) (f : 'c -> 'a -> 'a tactic)
      (n : 'c) (brs : ('a,'r) pcase_branch array) : ('a,'r) pcase_branch array tactic =
    let f (br0 : ('a,'r) pcase_branch) : ('a,'r) pcase_branch tactic =
      let bs, c = br0 in
      f (iterate g (Array.length bs) n) c >>= fun c' ->
      return (if c == c' then br0 else (bs,c'))
    in
    ArrayTac.smart_map f brs

  let map_rec_declaration (f : 'a -> 'a tactic)
      (r0 : ('a,'a,'r) prec_declaration) : ('a,'a,'r) prec_declaration tactic =
    let bs,ts,cs = r0 in
    ArrayTac.smart_map f ts >>= fun ts' ->
    ArrayTac.smart_map f cs >>= fun cs' ->
    return (if ts == ts' && cs == cs' then r0 else (bs,ts',cs'))

  let map_rec_declaration_with_binders
      (g : 'c -> 'c) (f : 'c -> 'a -> 'a tactic)
      (n : 'c) (r0 : ('a,'a,'r) prec_declaration) :
        ('a,'a,'r) prec_declaration tactic =
    let bs,ts,cs = r0 in
    ArrayTac.smart_map (f n) ts >>= fun ts' ->
    ArrayTac.smart_map (f (iterate g (Array.length bs) n)) cs >>= fun cs' ->
    return (if ts == ts' && cs == cs' then r0 else (bs,ts',cs'))

  let map_rec_declaration_with_full_binders
      (g : ('a,'a,'r) Decl.pt -> 'c -> 'c) (f : 'c -> 'a -> 'a tactic)
      (n : 'c) (r0 : ('a,'a,'r) prec_declaration) :
        ('a,'a,'r) prec_declaration tactic =
    let bs,ts,cs = r0 in
    ArrayTac.smart_map (f n) ts >>= fun ts' ->
    let n =
      CArray.fold_left2 (fun acc na t -> g (Decl.LocalAssum (na,t)) acc)
        n bs ts'
    in
    ArrayTac.smart_map (f n) cs >>= fun cs' ->
    return (if ts == ts' && cs == cs' then r0 else (bs,ts',cs'))

  let map_pblock (g : rel_declaration -> 'c -> 'c)
      (f : 'c -> t -> t tactic) (n : 'c) (c0 : t)
      (u, ty, entries, body) : t tactic =
    let rec map_context n ctx =
      match ctx with
      | [] -> return (n, ctx)
      | decl :: rest ->
        map_context n rest >>= fun (n, rest') ->
        (match decl with
        | Decl.LocalAssum (na, ty) ->
          f n ty >>= fun ty' ->
          return (if ty == ty' then decl else Decl.LocalAssum (na, ty'))
        | Decl.LocalDef (na, value, ty) ->
          f n value >>= fun value' ->
          f n ty >>= fun ty' ->
          return (
            if value == value' && ty == ty' then decl
            else Decl.LocalDef (na, value', ty')
          )) >>= fun decl' ->
        return (g decl' n, if decl == decl' && rest == rest' then ctx else decl' :: rest')
    in
    let rec map_entries i n =
      if i = Array.length entries then return (n, []) else
      let entry = entries.(i) in
      map_context n entry.pbe_context >>= fun (entry_n, context') ->
      f entry_n entry.pbe_type >>= fun type' ->
      f entry_n entry.pbe_value >>= fun value' ->
      let entry' =
        if context' == entry.pbe_context && type' == entry.pbe_type
        && value' == entry.pbe_value then entry
        else {entry with pbe_context=context'; pbe_type=type'; pbe_value=value'}
      in
      let hidden_type = Term.it_mkProd_or_LetIn type' context' in
      let hidden = Decl.LocalAssum
        (Context.make_annot Names.Anonymous entry.pbe_relevance, hidden_type)
      in
      map_entries (i + 1) (g hidden n) >>= fun (body_n, rest) ->
      return (body_n, entry' :: rest)
    in
    f n ty >>= fun ty' ->
    map_entries 0 n >>= fun (body_n, entries') ->
    let entries' = Array.of_list entries' in
    let entries' = if CArray.for_all2 (==) entries entries' then entries else entries' in
    f body_n body >>= fun body' ->
    return (
      if ty == ty' && entries == entries' && body == body' then c0
      else mkPBlock (u, ty', entries', body')
    )

  let map_prun (f : t -> t tactic) (c0 : t) (ty, k, b, cont) : t tactic =
    f ty >>= fun ty' ->
    f k >>= fun k' ->
    f b >>= fun b' ->
    f cont >>= fun cont' ->
    return (
      if ty == ty' && k == k' && b == b' && cont == cont' then c0
      else mkPRun (ty', k', b', cont')
    )

  let map (f : t -> t tactic) (c0 : t) : t tactic =
    match kind c0 with

    (* Cases we expect to fire frequently come first. *)

    | Rel _ | Var _ | Const _ | Ind _ -> return c0

    | App (c, args) ->
      f c >>= fun c' ->
      ArrayTac.smart_map f args >>= fun args' ->
      return (if c == c' && args == args' then c0 else mkApp (c',args'))

    | Proj (p, r, c) ->
      f c >>= fun c' ->
      return (if c == c' then c0 else mkProj (p, r, c'))

    | Evar (ev, args) ->
      SListTac.smart_map f args >>= fun args' ->
      return (if args == args' then c0 else mkEvar (ev,args'))

    | Meta _ | Sort _ | Construct _ -> return c0

    | Prod (na, t1, t2) ->
      f t1 >>= fun t1' ->
      f t2 >>= fun t2' ->
      return (if t1 == t1' && t2 == t2' then c0 else mkProd (na,t1',t2'))

    | Lambda (bt, t, c) ->
      f t >>= fun t' ->
      f c >>= fun c' ->
      return (if t == t' && c == c' then c0 else mkLambda (bt,t',c'))

    | LetIn (bt, c1, t, c2) ->
      f c1 >>= fun c1' ->
      f t >>= fun t' ->
      f c2 >>= fun c2' ->
      return (
        if t == t' && c1 == c1' && c2 == c2' then c0
        else mkLetIn (bt,t',c1',c2')
      )

    | Cast (c, cast, ty) ->
      f c >>= fun c' ->
      f ty >>= fun ty' ->
      return (if c == c' && ty == ty' then c0 else mkCast (c',cast,ty'))

    | Case (ci, u, params, p, iv, c, brs) ->
      ArrayTac.smart_map f params >>= fun params' ->
      map_return_predicate f p >>= fun p' ->
      map_invert f iv >>= fun iv' ->
      f c >>= fun c' ->
      map_branches f brs >>= fun brs' ->
      return (
        if params == params'
        && p == p'
        && iv == iv'
        && c == c'
        && brs == brs'
        then c0
        else mkCase (ci,u,params',p',iv',c',brs')
      )

    | Fix (i, rd) ->
      map_rec_declaration f rd >>= fun rd' ->
      return (if rd == rd' then c0 else mkFix (i,rd'))

    | CoFix (i, rd) ->
      map_rec_declaration f rd >>= fun rd' ->
      return (if rd == rd' then c0 else mkCoFix (i,rd'))

    | Int _ | Float _ | String _ -> return c0

    | Array (u,cs,def,t) ->
      ArrayTac.smart_map f cs >>= fun cs' ->
      f def >>= fun def' ->
      f t >>= fun t' ->
      return (
        if cs == cs' && def == def' && t == t' then c0
        else mkArray (u,cs',def',t')
      )

    | PBlock (u, ty, entries, body) ->
      map_pblock (fun _ n -> n) (fun () -> f) () c0 (u, ty, entries, body)

    | PRun (ty, k, b, cont) -> map_prun f c0 (ty, k, b, cont)

  let map_with_binders (g : 'c -> 'c) (f : 'c -> t -> t tactic)
      (n : 'c) (c0 : t) : t tactic =
    match kind c0 with

    (* Cases we expect to fire frequently come first. *)

    | Rel _ | Var _ | Const _ | Ind _ -> return c0

    | App (c, args) ->
      f n c >>= fun c' ->
      ArrayTac.smart_map (f n) args >>= fun args' ->
      return (if c == c' && args == args' then c0 else mkApp (c',args'))

    | Proj (p, r, c) ->
      f n c >>= fun c' ->
      return (if c == c' then c0 else mkProj (p, r, c'))

    | Evar (ev, args) ->
      SListTac.smart_map (f n) args >>= fun args' ->
      return (if args == args' then c0 else mkEvar (ev,args'))

    | Meta _ | Sort _ | Construct _ -> return c0

    | Prod (na, t1, t2) ->
      f n t1 >>= fun t1' ->
      f (g n) t2 >>= fun t2' ->
      return (if t1 == t1' && t2 == t2' then c0 else mkProd (na,t1',t2'))

    | Lambda (bt, t, c) ->
      f n t >>= fun t' ->
      f (g n) c >>= fun c' ->
      return (if t == t' && c == c' then c0 else mkLambda (bt,t',c'))

    | LetIn (bt, c1, t, c2) ->
      f n c1 >>= fun c1' ->
      f n t >>= fun t' ->
      f (g n) c2 >>= fun c2' ->
      return (
        if t == t' && c1 == c1' && c2 == c2' then c0
        else mkLetIn (bt,t',c1',c2')
      )

    | Cast (c, cast, ty) ->
      f n c >>= fun c' ->
      f n ty >>= fun ty' ->
      return (if c == c' && ty == ty' then c0 else mkCast (c',cast,ty'))

    | Case (ci, u, params, p, iv, c, brs) ->
      ArrayTac.smart_map (f n) params >>= fun params' ->
      map_return_predicate_with_binders g f n p >>= fun p' ->
      map_invert (f n) iv >>= fun iv' ->
      f n c >>= fun c' ->
      map_branches_with_binders g f n brs >>= fun brs' ->
      return (
        if params == params'
        && p == p'
        && iv == iv'
        && c == c'
        && brs == brs'
        then c0
        else mkCase (ci,u,params',p',iv',c',brs')
      )

    | Fix (i, rd) ->
      map_rec_declaration_with_binders g f n rd >>= fun rd' ->
      return (if rd == rd' then c0 else mkFix (i,rd'))

    | CoFix (i, rd) ->
      map_rec_declaration_with_binders g f n rd >>= fun rd' ->
      return (if rd == rd' then c0 else mkCoFix (i,rd'))

    | Int _ | Float _ | String _ -> return c0

    | Array (u,cs,def,t) ->
      ArrayTac.smart_map (f n) cs >>= fun cs' ->
      f n def >>= fun def' ->
      f n t >>= fun t' ->
      return (
        if cs == cs' && def == def' && t == t' then c0
        else mkArray (u,cs',def',t')
      )

    | PBlock (u, ty, entries, body) ->
      map_pblock (fun _ n -> g n) f n c0 (u, ty, entries, body)

    | PRun (ty, k, b, cont) -> map_prun (f n) c0 (ty, k, b, cont)

  let map_with_full_binders (env : Environ.env)
      (g : rel_declaration -> 'c -> 'c) (f : 'c -> t -> t tactic)
      (n : 'c) (c0 : t) : t tactic =
    match kind c0 with

    (* Cases we expect to fire frequently come first. *)

    | Rel _ | Var _ | Const _ | Ind _ -> return c0

    | App (c, args) ->
      f n c >>= fun c' ->
      ArrayTac.smart_map (f n) args >>= fun args' ->
      return (if c == c' && args == args' then c0 else mkApp (c',args'))

    | Proj (p, r, c) ->
      f n c >>= fun c' ->
      return (if c == c' then c0 else mkProj (p,r,c'))

    | Evar (ev, args) ->
      SListTac.smart_map (f n) args >>= fun args' ->
      return (if args == args' then c0 else mkEvar (ev,args'))

    | Meta _ | Sort _ | Construct _ -> return c0

    | Prod (na, t1, t2) ->
      f n t1 >>= fun t1' ->
      f (g (Decl.LocalAssum (na,t1')) n) t2 >>= fun t2' ->
      return (if t1 == t1' && t2 == t2' then c0 else mkProd (na,t1',t2'))

    | Lambda (na, t, c) ->
      f n t >>= fun t' ->
      f (g (Decl.LocalAssum (na,t')) n) c >>= fun c' ->
      return (if t == t' && c == c' then c0 else mkLambda (na,t',c'))

    | LetIn (na, c1, t, c2) ->
      f n c1 >>= fun c1' ->
      f n t >>= fun t' ->
      f (g (Decl.LocalDef (na,c1',t')) n) c2 >>= fun c2' ->
      return (
        if t == t' && c1 == c1' && c2 == c2' then c0
        else mkLetIn (na,t',c1',c2')
      )

    | Cast (c, cast, ty) ->
      f n c >>= fun c' ->
      f n ty >>= fun ty' ->
      return (if c == c' && ty == ty' then c0 else mkCast (c',cast,ty'))

    | Case (ci, u, params, p, iv, c, brs) ->
      let ci,ep,iv,c,ebrs =
        Inductive.expand_case env (ci,u,params,p,iv,c,brs)
      in
      let map_expanded (e : constr) : constr tactic =
        let ctx,c = Term.decompose_prod_decls e in
        f (List.fold_right g ctx n) c >>= fun c' ->
        return (
          if c == c' then e
          else (Term.it_mkLambda_or_LetIn c' ctx)
        )
      in
      map_expanded (fst ep) >>= fun ep' ->
      map_invert (f n) iv >>= fun iv' ->
      f n c >>= fun c' ->
      ArrayTac.smart_map map_expanded ebrs >>= fun ebrs' ->
      return (
        if fst ep == ep' && iv == iv' && c == c' && ebrs == ebrs' then c0
        else mkCase (Inductive.contract_case env (ci,(ep',snd ep),iv',c',ebrs'))
      )

    | Fix (i, rd) ->
      map_rec_declaration_with_full_binders g f n rd >>= fun rd' ->
      return (if rd == rd' then c0 else mkFix (i,rd'))

    | CoFix (i, rd) ->
      map_rec_declaration_with_full_binders g f n rd >>= fun rd' ->
      return (if rd == rd' then c0 else mkCoFix (i,rd'))

    | Int _ | Float _ | String _ -> return c0

    | Array (u,cs,def,t) ->
      ArrayTac.smart_map (f n) cs >>= fun cs' ->
      f n def >>= fun def' ->
      f n t >>= fun t' ->
      return (
        if cs == cs' && def == def' && t == t' then c0
        else mkArray (u,cs',def',t')
      )

    | PBlock (u, ty, entries, body) ->
      map_pblock g f n c0 (u, ty, entries, body)

    | PRun (ty, k, b, cont) -> map_prun (f n) c0 (ty, k, b, cont)

end

module EConstrTac = struct

  open EConstr

  let fold (sigma : Evd.evar_map) (f : t -> 'a -> 'a) (c : t) (acc : 'a) : 'a =
    EConstr.fold sigma (fun acc c -> f c acc) acc c

  let fold_with_binders (sigma : Evd.evar_map)
      (g : 'c -> 'c) (f : 'c -> t -> 'a -> 'a)
      (n : 'c) (c : t) (acc : 'a) : 'a =
    EConstr.fold_with_binders sigma g (fun n acc c -> f n c acc) n acc c

  let fold_with_full_binders (env : Environ.env) (sigma : Evd.evar_map)
      (g : rel_declaration -> 'c -> 'c) (f : 'c -> t -> 'a -> 'a)
      (n : 'c) (c : t) (acc : 'a) : 'a =
    Termops.fold_constr_with_full_binders env sigma g
      (fun n acc c -> f n c acc) n acc c

  let of_constr : Constr.t -> EConstr.t = EConstr.of_constr
  let to_constr : EConstr.t -> Constr.t = EConstr.Unsafe.to_constr
  let to_constr_whd : Evd.evar_map -> EConstr.t -> Constr.t =
    fun sigma c -> to_constr (EConstr.whd_evar sigma c)

  let map (sigma : Evd.evar_map) (f : t -> t tactic) (c : t) : t tactic =
    let f (c : Constr.t) : Constr.t tactic =
      f (of_constr c) >>= fun c ->
      return (to_constr c)
    in
    ConstrTac.map f (to_constr_whd sigma c) >>= fun c ->
    return (of_constr c)

  let map_with_binders (sigma : Evd.evar_map)
      (g : 'c -> 'c) (f : 'c -> t -> t tactic) (n : 'c) (c : t) : t tactic =
    let f (n : 'c) (c : Constr.t) : Constr.t tactic =
      f n (of_constr c) >>= fun c ->
      return (to_constr c)
    in
    ConstrTac.map_with_binders g f n (to_constr_whd sigma c) >>= fun c ->
    return (of_constr c)

  let map_with_full_binders (env : Environ.env) (sigma : Evd.evar_map)
      (g : rel_declaration -> 'c -> 'c) (f : 'c -> t -> t tactic)
      (n : 'c) (c : t) : t tactic =
    let g (decl : Constr.rel_declaration) (n : 'c) : 'c =
      g (Decl.map_constr_het (ERelevance.make) of_constr decl) n
    in
    let f (n : 'c) (c : Constr.t) : Constr.t tactic =
      f n (of_constr c) >>= fun c ->
      return (to_constr c)
    in
    let c = to_constr_whd sigma c in
    ConstrTac.map_with_full_binders env g f n c >>= fun c ->
    return (of_constr c)
end

(*
TODO: Ltac2 doesn't expose an ['a repr] for its [case_invert] type. We
cannot yet expose [ConstrTac.map_invert] to Ltac2 code. We hold off on
the other auxiliary tactics, too.
*)

let unit_tac : unit tactic = return ()

(** Ltac2 type ['c -> 'c] *)
let thaw_with_bind (g : valexpr) :
    valexpr tactic -> valexpr tactic =
  Value.thaw1_poly g

(** Ltac2 type [Constr.Unsafe.RelDecl.t -> 'c -> 'c] *)
let thaw_with_full_bind (g : valexpr) :
    EConstr.rel_declaration -> valexpr tactic -> valexpr tactic =
  let g = Value.thaw2 Value.rel_declaration Value.valexpr Value.valexpr g in
  fun decl v -> v >>= fun v -> g decl v

(** Ltac2 type ['c -> constr -> constr] *)
let thaw_with_mapper (f : valexpr) :
    valexpr tactic -> EConstr.t -> EConstr.t tactic =
  let f : valexpr -> EConstr.t -> EConstr.t tactic =
    Value.thaw2 Value.valexpr Value.constr Value.constr f
  in
  fun n c -> n >>= fun n -> f n c

(** Ltac2 type ['c -> constr -> unit] *)
let thaw_with_apper (f : valexpr) :
    valexpr tactic -> EConstr.t -> unit tactic -> unit tactic =
  let f : valexpr -> EConstr.t -> unit tactic =
    Value.thaw2 Value.valexpr Value.constr Value.unit f
  in
  fun n c acc -> acc <*> n >>= fun n -> f n c

(** Ltac2 type ['c -> constr -> 'a -> 'a] *)
let thaw_with_folder (f : valexpr) :
    valexpr tactic -> EConstr.t -> valexpr tactic -> valexpr tactic =
  let f : valexpr -> EConstr.t -> valexpr -> valexpr tactic =
    Value.thaw3 Value.valexpr Value.constr Value.valexpr Value.valexpr f
  in
  fun n c acc -> n >>= fun n -> acc >>= fun acc -> f n c acc

open Ltac2_plugin
open Tac2ffi
open Tac2externals

let define s =
  define Tac2expr.{ mltac_plugin = "ltac2_extensions"; mltac_tactic = s }

let _ =
  define "constr_map" (valexpr @-> valexpr @-> tac constr) @@ fun f c ->
  let f : EConstr.t -> EConstr.t tactic =
    Value.thaw1 Value.constr Value.constr f in
  let c = Value.to_constr c in
  evar_map >>= fun sigma ->
  EConstrTac.map sigma f c

let _ =
  define "constr_map_with_binders"
    (valexpr @-> valexpr @-> valexpr @-> valexpr @-> tac constr)
    @@ fun g f n c ->
  let g = thaw_with_bind g in
  let f = thaw_with_mapper f in
  let n = return n in
  let c = Value.to_constr c in
  evar_map >>= fun sigma ->
  EConstrTac.map_with_binders sigma g f n c

let _ =
  define "constr_map_with_full_binders"
    (valexpr @-> valexpr @-> valexpr @-> valexpr @-> tac constr)
    @@ fun g f n c ->
  let g = thaw_with_full_bind g in
  let f = thaw_with_mapper f in
  let n = return n in
  let c = Value.to_constr c in
  TacUtil.env >>= fun env ->
  evar_map >>= fun sigma ->
  EConstrTac.map_with_full_binders env sigma g f n c

let _ =
  define "constr_iter" (valexpr @-> valexpr @-> tac unit) @@ fun f c ->
  let f : EConstr.t -> unit tactic = Value.thaw1 Value.constr Value.unit f in
  let f (c : EConstr.t) (acc : unit tactic) = acc <*> f c in
  let c = Value.to_constr c in
  evar_map >>= fun sigma ->
  EConstrTac.fold sigma f c unit_tac

let _ =
  define "constr_iter_with_binders"
    (valexpr @-> valexpr @-> valexpr @-> valexpr @-> tac unit)
    @@ fun g f n c ->
  let g = thaw_with_bind g in
  let f = thaw_with_apper f in
  let n = return n in
  let c = Value.to_constr c in
  evar_map >>= fun sigma ->
  EConstrTac.fold_with_binders sigma g f n c unit_tac

let _ =
  define "constr_iter_with_full_binders"
    (valexpr @-> valexpr @-> valexpr @-> valexpr @-> tac unit)
    @@ fun g f n c ->
  let g = thaw_with_full_bind g in
  let f = thaw_with_apper f in
  let n = return n in
  let c = Value.to_constr c in
  TacUtil.env >>= fun env ->
  evar_map >>= fun sigma ->
  EConstrTac.fold_with_full_binders env sigma g f n c unit_tac

let _ =
  define "constr_fold"
    (valexpr @-> valexpr @-> valexpr @-> tac valexpr)
    @@ fun f c acc ->
  let f : EConstr.t -> valexpr -> valexpr tactic =
    Value.thaw2 Value.constr Value.valexpr Value.valexpr f
  in
  let f (c : EConstr.t) (acc : valexpr tactic) = acc >>= fun acc -> f c acc in
  let c = Value.to_constr c in
  let acc = return acc in
  evar_map >>= fun sigma ->
  EConstrTac.fold sigma f c acc

let _ =
  define "constr_fold_with_binders"
    (valexpr @-> valexpr @-> valexpr @-> valexpr @-> valexpr @-> tac valexpr)
    @@ fun g f n c acc ->
  let g = thaw_with_bind g in
  let f = thaw_with_folder f in
  let n = return n in
  let c = Value.to_constr c in
  let acc = return acc in
  evar_map >>= fun sigma ->
  EConstrTac.fold_with_binders sigma g f n c acc

let _ =
  define "constr_fold_with_full_binders"
    (valexpr @-> valexpr @-> valexpr @-> valexpr @-> valexpr @-> tac valexpr)
    @@ fun g f n c acc ->
  let g = thaw_with_full_bind g in
  let f = thaw_with_folder f in
  let n = return n in
  let c = Value.to_constr c in
  let acc = return acc in
  TacUtil.env >>= fun env ->
  evar_map >>= fun sigma ->
  EConstrTac.fold_with_full_binders env sigma g f n c acc
