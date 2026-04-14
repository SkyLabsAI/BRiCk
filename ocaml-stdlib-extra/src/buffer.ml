(*
 * Copyright (C) 2021-2026 SkyLabs AI, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

include Stdlib.Buffer

let iter : (char -> unit) -> t -> unit = fun f buf ->
  Seq.iter f (to_seq buf)

let iter_lines : (string -> unit) -> t -> unit = fun f buf ->
  let b = create 2048 in
  let handle_char c =
    match c with
    | '\n' -> f (contents b); clear b
    | _    -> add_char b c
  in
  iter handle_char buf;
  if length b <> 0 then f (contents b)

let is_empty : t -> bool = fun b ->
  try ignore (nth b 0); false with Invalid_argument(_) -> true

let add_full_channel : t -> in_channel -> unit = fun b ic ->
  try while true do add_char b (input_char ic) done with End_of_file -> ()

let add_file : t -> string -> unit = fun b file ->
  In_channel.with_open_text file (add_full_channel b)

let from_file : string -> t = fun fname ->
  let buf = create 4096 in add_file buf fname; buf

let to_file : string -> t -> unit = fun file b ->
  Out_channel.with_open_text file (fun oc -> output_buffer oc b)
