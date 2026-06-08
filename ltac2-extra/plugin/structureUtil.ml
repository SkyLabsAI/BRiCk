(*
 * Copyright (C) 2023 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
open Ltac2_plugin
open TacUtil
open Proofview.Notations
open Structures
open Tac2externals
open Tac2ffi

let define s =
  define Tac2expr.{ mltac_plugin = "ltac2_extensions"; mltac_tactic = s }

type decomp_proj =
  | Prim of { proj: Names.Projection.t; recval: Constr.t }
  | NonPrim of { proj: Names.Constant.t; inst: UVars.Instance.t; args: Constr.t array; recval: Constr.t }

let decompose_proj_args args =
  let recval_pos = Array.length args - 1 in
  let recval = Array.get args recval_pos in
  let args = Array.sub args 0 recval_pos in
  args, recval

(* [decompose_proj t] attempts to decompose an application of a (possibly
   primitive) projection to a record value. The term must not have additional
   trailing arguments after the record value. If the term is not an application
   of a projection or if there are any additional trailing arguments, the
   function returns [None].
*)
let decompose_proj (env : Environ.env) (t : Constr.t) : (Structure.t * decomp_proj) option =
  let open Constr in
  let (h, args) = decompose_app t in
  match kind h, args with
  | Proj (proj, _, recval), [||] ->
    let t = Structure.find_from_projection env (Names.Projection.constant proj) in
    Some (t, Prim {proj; recval})
  | Const (proj, inst), _ ->
    begin
      match Structure.find_from_projection env proj with
      | t ->
        if Array.length args == t.Structure.nparams + 1 then
          let args, recval = decompose_proj_args args in
          Some (t, NonPrim {proj; inst; args; recval})
        else
          None
      | exception Not_found -> None
    end
  | _ -> None

let _ =
  define "decompose_proj" (constr @-> tac valexpr) @@ fun t ->
  with_evarmap @@ fun sigma ->
  TacUtil.env >>= fun env ->
  let t = EConstr.to_constr ~abort_on_undefined_evars:false sigma t in
  let r = decompose_proj env t in
  Proofview.tclUNIT @@
    of_option (fun (t, p) ->
        let (proj, inst, args, recval) = match p with
          | NonPrim { proj; inst; args; recval } -> (proj, inst, args, recval)
          | Prim {proj; recval} ->
            let term = Retyping.expand_projection env sigma proj (EConstr.of_constr recval) [] in
            let (h, args) = Constr.decompose_app (EConstr.to_constr ~abort_on_undefined_evars:false sigma term) in
            let (_, inst) = Constr.destConst h in
            let args, recval = decompose_proj_args args in
            (Names.Projection.constant proj, inst, args, recval)
        in
        let proj_index =
          let id = Names.Constant.label proj in
          (* Projections in [Structure.projection] are allowed to be anonymous.
             We already know that we have projection in [proj] so there must be a matching named projection in the list. *)
          let rec go pos = function
            | [] -> raise Not_found
            | proj' :: projs ->
              match proj'.Structure.proj_name with
              | Names.Name.Name id' when Names.Id.equal id id' -> pos
              | _ -> go (pos + 1) projs
          in
          go 0 (t.Structure.projections)
        in
        let t = repr_of inductive (t.Structure.name) in
        let proj_term = of_constr (EConstr.of_constr (Constr.mkConstU (proj, inst))) in
        let proj_index = of_int proj_index in
        let args = of_array of_constr (Array.map EConstr.of_constr args) in
        let recval = of_constr (EConstr.of_constr recval) in
        of_tuple [|t; proj_index; proj_term; args; recval|]
      ) r
