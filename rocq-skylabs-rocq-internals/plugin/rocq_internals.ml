(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* The following is mostly taken from file [tactics/btermdn.ml]. NOTE: porting
   the code to newer Coq should only involve porting changes to the functions
   from [tactics/btermdn.ml]. The end of the file (function [pattern] and the
   [Make] functor) should not need changes. *)

open Util
open Names
open Pattern

type pat = Pattern.constr_pattern

module Patternops = struct
  include Patternops

  (* Copied from patternops.ml and adapted to consider [PMeta] meta variables
     mentioning no variables. The rationale is that for hint patterns, [PMeta]
     represent the hints arguments. Those cannot possibly mention unbound
     [PRel]s. *)
  let occurn_pattern_meta_closed =
    let rec go n : constr_pattern -> _ = function
    | PRel p -> Int.equal n p
    | PApp (f,args) ->
        (go n f) || (Array.exists (go n) args)
    | PProj (_,arg) -> go n arg
    | PLambda (_na,t,c)  -> (go n t) || (go (n+1) c)
    | PProd (_na,t,c)  -> (go n t) || (go (n+1) c)
    | PLetIn (_na,b,t,c)  ->
      Option.fold_left (fun b t -> b || go n t) (go n b) t ||
      (go (n+1) c)
    | PIf (c,c1,c2)  ->
        (go n c) ||
        (go n c1) || (go n c2)
    | PCase(_, p, c, br) ->
        Option.cata (fun (nas, p) -> go (Array.length nas + n) p) false p ||
        (go n c) ||
        (List.exists (fun (_, nas, p) -> go (Array.length nas + n) p) br)
    | PMeta _ -> false            (* Changed from [true] *)
    | PSoApp _ -> true            (* TODO: change this as well? *)
    | PEvar (_,args) -> List.exists (go n) args
    | PVar _ | PRef _ | PSort _ | PInt _ | PFloat _ | PString _ -> false
    | PFix (_,(_,tl,bl)) ->
      Array.exists (go n) tl || Array.exists (go (n+Array.length tl)) bl
    | PCoFix (_,(_,tl,bl)) ->
      Array.exists (go n) tl || Array.exists (go (n+Array.length tl)) bl
    | PArray (t,def,ty) ->
      Array.exists (go n) t || go n def || go n ty
    | PUninstantiated _ -> .
    in
    go

  let noccurn_pattern_meta_closed n c = not (occurn_pattern_meta_closed n c)
  (* End of patternops.ml code *)
end

let rec eta_reduce_pat (p : constr_pattern) = match p with
| PLambda (_, _, q) ->
  let f, cl = match eta_reduce_pat q with
  | PApp (f, cl) -> f, cl
  | q -> q, [||]
  in
  let napp = Array.length cl in
  if napp > 0 then
    let r = eta_reduce_pat (Array.last cl) in
    match r with
    | PRel 1 ->
      let lc = Array.sub cl 0 (napp - 1) in
      let u = if Array.is_empty lc then f else PApp (f, lc) in
      if Patternops.noccurn_pattern_meta_closed 1 u then
        Patternops.lift_pattern (-1) u
      else
        p
    | _ -> p
  else p
| PRef _ | PVar _ | PEvar _ | PRel _ | PApp _ | PSoApp _ | PProj _ | PProd _
| PLetIn _ | PSort _ | PMeta _ | PIf _ | PCase _ | PFix _ | PCoFix _ | PInt _
| PFloat _ | PString _ | PArray _ -> p
| PUninstantiated _ -> .

let decomp_pat p =
  let rec decrec acc = function
    | PApp (f,args) -> decrec (Array.to_list args @ acc) f
    | PProj (p, c) ->
      let hole = PMeta None in
      let params = List.make (Projection.npars p) hole in
      (PRef (GlobRef.ConstRef (Projection.constant p)), params @ c :: acc)
    | c -> (c,acc)
  in
  decrec [] (eta_reduce_pat p)

let evaluable_constant c env ts =
  (* Hack to work around a broken Print Module implementation, see #2668. *)
  (if Environ.mem_constant c env then Environ.evaluable_constant c env else true) &&
  Structures.PrimitiveProjections.is_transparent_constant ts c

let evaluable_named id env ts =
  (try Environ.evaluable_named id env with Not_found -> true) &&
  TransparentState.is_transparent_variable ts id
