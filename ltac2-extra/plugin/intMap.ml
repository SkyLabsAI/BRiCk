(*
 * Copyright (C) 2023 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
open Ltac2_plugin
open Tac2ffi
open Tac2externals

let define s =
  define Tac2expr.{ mltac_plugin = "sl.IntMap"; mltac_tactic = s }

module IntMap = struct
  include Map.Make(Int)

  type intmap = Tac2val.valexpr t

  let repr : intmap Tac2ffi.repr =
    Tac2ffi.repr_ext (Tac2dyn.Val.create "IntMap.t")

  let _ = define "empty" (ret repr) empty

  let _ = define "is_empty" (repr @-> ret bool) is_empty

  let _ = define "mem" (int @-> repr @-> ret bool) mem

  let _ = define "add" (int @-> valexpr @-> repr @-> ret repr) add

  let _ = define "singleton" (int @-> valexpr @-> ret repr) singleton

  let _ = define "remove" (int @-> repr @-> ret repr) remove

  let _ = define "cardinal" (repr @-> ret int) cardinal

  let _ = define "bindings" (repr @-> ret (list (pair int valexpr))) bindings

  let _ = define "find_opt" (int @-> repr @-> ret (option valexpr)) find_opt

  let _ =
    define "min_binding_opt"
      (repr @-> ret (option (pair int valexpr))) min_binding_opt

  let _ =
    define "max_binding_opt"
      (repr @-> ret (option (pair int valexpr))) max_binding_opt
end
