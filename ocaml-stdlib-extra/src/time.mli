(*
 * Copyright (C) 2021-2026 SkyLabs AI, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

(** High-level interface to timing data. *)

(** Time since the start of the process (using the [Unix] module). *)
module Unix : sig
  (** Time representation in user+system seconds since the process start. *)
  type t = float

  (** [get ()] gives the current time. *)
  val get : unit -> t
end

(** Monotonic clock. *)
module Monotonic : sig
  (** Representation of a monotonic timestamp. *)
  type t

  (** [now ()] gives a timestamp representing the current time. *)
  val now : unit -> t

  (** [in_mus t] gives the representation of timestamp [t] in micro-seconds. A
      timestamp value is meaningless in absolute terms. *)
  val in_mus : t -> int

  (** [diff_mus t0 t1] computes the difference between the timestamps [t1] and
      [t0], expressed in number of micro-seconds. If [t1] happened before [t0]
      then the exception [Invalid_argument] is raised. *)
  val diff_mus : t -> t -> int
end
