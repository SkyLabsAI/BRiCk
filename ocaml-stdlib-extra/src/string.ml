(*
 * Copyright (C) 2021-2026 SkyLabs AI, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

include Stdlib.String

let take : int -> string -> string = fun i s ->
  try sub s 0 i
  with Invalid_argument(_) -> invalid_arg "String.take"

let drop : int -> string -> string = fun i s ->
  try sub s i (length s - i)
  with Invalid_argument(_) -> invalid_arg "String.drop"

let of_char_list : char list -> string =
  let b = Buffer.create 100 in
  let of_char_list cs =
    Buffer.clear b;
    List.iter (Buffer.add_char b) cs;
    Buffer.contents b
  in
  of_char_list

let sub_from : string -> int -> string = fun s i ->
  sub s i (length s - i)

let trim_leading : char -> string -> string = fun c s ->
  let len = length s in
  let index = ref 0 in
  while !index < len && get s !index = c do incr index done;
  sub_from s !index
