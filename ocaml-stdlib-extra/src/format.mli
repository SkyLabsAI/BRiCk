(*
 * Copyright (C) 2021-2026 SkyLabs AI, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

(** Extension of [Stdlib.Format] *)

include module type of Stdlib.Format

(** Short name for a standard formatter. *)
type 'a outfmt = ('a, formatter, unit) format

(** Type of a formatter of type ['a] with continuation of type ['k]. *)
type ('a, 'k) koutfmt = ('a, formatter, unit, unit, unit, 'k) format6

(** Type of a format transformer (e.g., changing the color). *)
type ('a, 'b, 'c, 'd, 'e, 'f) transformer =
  ('a, 'b, 'c, 'd, 'e, 'f) format6 -> ('a, 'b, 'c, 'd, 'e, 'f) format6

module Color : sig
  val red : ('a, 'b, 'c, 'd, 'e, 'f) transformer
  val gre : ('a, 'b, 'c, 'd, 'e, 'f) transformer
  val yel : ('a, 'b, 'c, 'd, 'e, 'f) transformer
  val blu : ('a, 'b, 'c, 'd, 'e, 'f) transformer
  val mag : ('a, 'b, 'c, 'd, 'e, 'f) transformer
  val cya : ('a, 'b, 'c, 'd, 'e, 'f) transformer
end

(** Standard type of a pretty-printing function. *)
type 'a pp = formatter -> 'a -> unit

(** Type of a module with a pretty-printing function. *)
module type PP = sig
  type t
  val pp : t pp
end
