(*
 * Copyright (C) 2021-2026 SkyLabs AI, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

include Stdlib.Format

type ('a, 'k) koutfmt = ('a, formatter, unit, unit, unit, 'k) format6

type 'a pp = formatter -> 'a -> unit

module type PP = sig
  type t
  val pp : t pp
end
