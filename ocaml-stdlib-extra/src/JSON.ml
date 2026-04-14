(*
 * Copyright (C) 2021-2026 SkyLabs AI, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

type t = Yojson.Basic.t

exception Error of string

let handle f x =
  try f x with Yojson.Json_error(msg) -> raise (Error(msg))

let from_channel : In_channel.t -> t = fun ic ->
  handle Yojson.Basic.from_channel ic

let from_file : string -> t = fun file ->
  handle Yojson.Basic.from_file file

let write : Stdlib.out_channel -> t -> unit =
  Yojson.Basic.to_channel
