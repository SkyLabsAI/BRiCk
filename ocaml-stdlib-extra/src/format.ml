(*
 * Copyright (C) 2021-2026 SkyLabs AI, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

include Stdlib.Format

type 'a outfmt = ('a, formatter, unit) format

type ('a, 'k) koutfmt = ('a, formatter, unit, unit, unit, 'k) format6

type ('a, 'b, 'c, 'd, 'e, 'f) transformer =
  ('a, 'b, 'c, 'd, 'e, 'f) format6 -> ('a, 'b, 'c, 'd, 'e, 'f) format6

module Color = struct
  let with_color k fmt = "\027[" ^^ k ^^ "m" ^^ fmt ^^ "\027[0m%!"

  let red fmt = with_color "31" fmt
  let gre fmt = with_color "32" fmt
  let yel fmt = with_color "33" fmt
  let blu fmt = with_color "34" fmt
  let mag fmt = with_color "35" fmt
  let cya fmt = with_color "36" fmt
end

type 'a pp = formatter -> 'a -> unit

module type PP = sig
  type t
  val pp : t pp
end
