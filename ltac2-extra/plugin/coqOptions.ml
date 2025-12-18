(*
 * Copyright (C) 2022 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(** Ltac2 primitives and utilities around Coq options. *)

open Ltac2_plugin
open Tac2externals
open Tac2ffi

let define s =
  define Tac2expr.{ mltac_plugin = "sl.CoqOptions"; mltac_tactic = s }

(** [of_option_state os] converts an option state into the corresponding Ltac2
    type, only covering the [opt_value] field. *)
let of_option_state : Goptions.option_state -> Tac2val.valexpr = fun os ->
  let open Goptions in
  let ov = os.opt_value in
  let block i v = Tac2ffi.of_block (i, [|v|]) in
  let of_string s = Tac2ffi.of_string s in
  match ov with
  | BoolValue(b)       -> block 0 (Tac2ffi.of_bool b)
  | IntValue(io)       -> block 1 (Tac2ffi.of_option Tac2ffi.of_int io)
  | StringValue(s)     -> block 2 (of_string s)
  | StringOptValue(so) -> block 3 (Tac2ffi.of_option of_string so)

let _ =
  define "get" (list string @-> ret valexpr) @@ fun name ->
  let vo = Goptions.(OptionMap.find_opt name (get_tables ())) in
  Tac2ffi.of_option of_option_state vo
