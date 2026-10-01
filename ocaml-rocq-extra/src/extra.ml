(*
 * Copyright (C) 2023-2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

open Stdlib_extra.Extra

let user_err : ('a, 'k) Format.koutfmt -> 'a = fun fmt ->
  let buf = Buffer.create 256 in
  let ff = Format.formatter_of_buffer buf in
  let k _ =
    Format.pp_print_flush ff ();
    CErrors.user_err Pp.(str (Buffer.contents buf))
  in
  Format.kfprintf k ff fmt

module Pp = Extra_pp
module Msg = Extra_msg
module Whd = Extra_whd

(* FIXME extend Pattern -> dynlink error *)
module Extra_pattern = Extra_pattern
module TransparentState = Extra_transparentState
