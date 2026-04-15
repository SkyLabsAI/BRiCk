(*
 * Copyright (C) 2021-2026 SkyLabs AI, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

module Buffer = Stdlib.Buffer
module Format = Stdlib.Format

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
