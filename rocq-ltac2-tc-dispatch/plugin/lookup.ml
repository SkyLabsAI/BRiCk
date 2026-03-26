
open Ltac2_plugin
open Tac2ffi
(* open Tac2val *)
open Tac2externals

let resolve_ltac2_safe (mp : string list) (id : string) : (unit -> unit Proofview.tactic) option =
  let qualid = Libnames.make_qualid
    (Names.DirPath.make (List.map Names.Id.of_string mp))
    (Names.Id.of_string id)
  in
  let is_unit_typ (t : int Tac2expr.glb_typexpr) : bool =
    (* TODO: why does Init.unit have two different representations? *)
    match t with
    | Tac2expr.GTypRef (Tac2expr.Other ty, []) ->
      ty = Tac2core.Core.t_unit
    | Tac2expr.GTypRef (Tac2expr.Tuple 0, []) ->
      true
    | _ -> false
  in
  let is_unit_to_unit ((n, t) : Tac2expr.type_scheme) : bool =
    Int.equal n 0 &&
    match t with
    | Tac2expr.GTypArrow (t1, t2) -> is_unit_typ t1 && is_unit_typ t2
    | _ -> false
  in
  match Tac2env.locate_ltac qualid with
  | Tac2expr.TacConstant kn ->
    let data = Tac2env.interp_global kn in
    if is_unit_to_unit data.Tac2env.gdata_type
    then
      let v = Tac2interp.eval_global kn in
      Some (repr_to (fun1 unit unit) v)
    else
      None
  | Tac2expr.TacAlias _ ->
    None
  | exception Not_found -> None


let define s =
  define Tac2expr.{ mltac_plugin = "ltac2_tc_dispatch"; mltac_tactic = s }

let () =
  define "resolve_ltac2"
    (list string @-> string @-> ret (option (fun1 unit unit))) @@ fun modpath name ->
    resolve_ltac2_safe modpath name
