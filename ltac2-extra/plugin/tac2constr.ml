(*
 * Copyright (C) 2021-2023 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

open Ltac2_plugin
open Tac2ffi
open Tac2externals

let to_constr : Evd.evar_map -> Tac2val.valexpr -> Constr.t = fun sigma c ->
  let c = Tac2ffi.to_constr c in
  EConstr.to_constr ~abort_on_undefined_evars:false sigma c

let of_constr : Constr.t -> Tac2val.valexpr = fun c ->
  Tac2ffi.of_constr (EConstr.of_constr c)

let reference_tag : _ Tac2core.map_tag = Tac2core.register_map ~tag_name:"fmap_reference_tag" (module struct
    module S = Names.GlobRef.Set
    module M = Names.GlobRef.Map
    let repr = Tac2ffi.reference
    type valmap = Tac2val.valexpr M.t
    let valmap_eq = Util.Refl
  end)

let evar_tag : _ Tac2core.map_tag =
  Tac2core.register_map ~tag_name:"fmap_evar_tag" (module struct
    module S = Evar.Set
    module M = Evar.Map
    let repr = Tac2ffi.evar
    type valmap = Tac2val.valexpr M.t
    let valmap_eq = Util.Refl
  end)

(* [compare] must be kept in sync with whatever is used in [ConstrSet] and [ConstrMap] *)
let _ =
  define Tac2expr.{ mltac_plugin = "sl.Constr"; mltac_tactic = "compare" }
    (valexpr @-> valexpr @-> eret int) @@ fun c1 c2 _ sigma ->
    Constr.compare (to_constr sigma c1) (to_constr sigma c2)

module ConstrSet = struct
  include Set.Make(Constr)

  let define s =
    define Tac2expr.{ mltac_plugin = "sl.ConstrSet"; mltac_tactic = s }

  let repr : t Tac2ffi.repr =
    Tac2ffi.repr_ext (Tac2dyn.Val.create "ConstrSet.t")

  let _ = define "empty" (ret repr) empty
  let _ = define "is_empty" (repr @-> ret bool) is_empty
  let _ = define "diff" (repr @-> repr @-> ret repr) diff
  let _ = define "union" (repr @-> repr @-> ret repr) union

  let _ =
    define "of_list" (valexpr @-> eret repr) @@ fun l _ sigma ->
    of_list (Tac2ffi.to_list (fun c -> to_constr sigma c) l)

  let _ =
    define "elements" (repr @-> ret valexpr) @@ fun s ->
    Tac2ffi.of_list of_constr (elements s)

  let _ =
    define "mem" (valexpr @-> repr @-> eret bool) @@ fun elem s _ sigma ->
    mem (to_constr sigma elem) s

  let _ =
    define "add" (valexpr @-> repr @-> eret repr) @@ fun elem s _ sigma ->
    add (to_constr sigma elem) s

  let _ =
    define "remove" (valexpr @-> repr @-> eret repr) @@ fun elem s _ sigma ->
    remove (to_constr sigma elem) s
end

module ConstrMap = struct
  include Map.Make(Constr)

  let define s =
    define Tac2expr.{ mltac_plugin = "sl.ConstrMap"; mltac_tactic = s }

  type vmap = Tac2val.valexpr t

  let repr : vmap Tac2ffi.repr =
    Tac2ffi.repr_ext (Tac2dyn.Val.create "ConstrMap.t")

  let _ = define "empty" (ret repr) empty
  let _ = define "is_empty" (repr @-> ret bool) is_empty
  let _ = define "cardinal" (repr @-> ret int) cardinal

  let _ =
    define "mem" (valexpr @-> repr @-> eret bool) @@ fun k m _ sigma ->
    mem (to_constr sigma k) m

  let _ =
    define "add"
      (valexpr @-> valexpr @-> repr @-> eret repr) @@ fun k v m _ sigma ->
      add (to_constr sigma k) v m

  let _ =
    define "singleton"
      (valexpr @-> valexpr @-> eret repr) @@ fun k v _ sigma ->
      singleton (to_constr sigma k) v

  let _ =
    define "remove" (valexpr @-> repr @-> eret repr) @@ fun k m _ sigma ->
    remove (to_constr sigma k) m

  let _ =
    define "bindings" (repr @-> ret valexpr) @@ fun m ->
    Tac2ffi.of_list (Tac2ffi.of_pair of_constr Fun.id) (bindings m)

  let _ =
    define "find_opt"
      (valexpr @-> repr @-> eret (option valexpr)) @@ fun k m _ sigma ->
      find_opt (to_constr sigma k) m
end
