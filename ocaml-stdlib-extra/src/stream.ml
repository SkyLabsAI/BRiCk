(*
 * Copyright (C) 2021-2026 SkyLabs AI, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

type 'a t = 'a Seq.t ref

let of_seq = ref

let next r =
  match !r () with
  | Seq.Nil        -> None
  | Seq.Cons(e, s) -> r := s; Some(e)

let from f =
  let rec from () =
    match f () with
    | None    -> Seq.Nil
    | Some(e) -> Seq.Cons(e, from)
  in
  ref from
