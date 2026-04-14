(*
 * Copyright (C) 2021-2026 SkyLabs AI, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

(** Extension of [Stdlib.Format] *)

include module type of Stdlib.Format

(** Type of a formatter of type ['a] with continuation of type ['k]. *)
type ('a, 'k) koutfmt = ('a, formatter, unit, unit, unit, 'k) format6

(** Standard type of a pretty-printing function. *)
type 'a pp = formatter -> 'a -> unit

(** Type of a module with a pretty-printing function. *)
module type PP = sig
  type t
  val pp : t pp
end
