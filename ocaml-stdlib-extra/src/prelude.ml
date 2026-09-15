(*
 * Copyright (C) 2021-2026 SkyLabs AI, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

module Buffer = Stdlib.Buffer

type 'a eq = 'a -> 'a -> bool

type 'a cmp = 'a -> 'a -> int

let failwith ?(fail=Stdlib.failwith) fmt =
  let buf = Buffer.create 1024 in
  let ff = Format.formatter_of_buffer buf in
  let k _ =
    Format.pp_print_flush ff ();
    fail (Buffer.contents buf)
  in
  Format.kfprintf k ff fmt

let wrn : 'a Format.outfmt -> 'a = fun fmt ->
  Format.eprintf (Format.Color.yel (fmt ^^ "\n%!"))

let err : 'a Format.outfmt -> 'a = fun fmt ->
  Format.eprintf (Format.Color.red (fmt ^^ "\n%!"))

let panic : ('a,'b) Format.koutfmt -> 'a = fun fmt ->
  Format.kfprintf (fun _ -> exit 1) Format.err_formatter
    (Format.Color.red (fmt ^^ "\n%!"))
