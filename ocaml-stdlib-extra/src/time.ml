(*
 * Copyright (C) 2021-2026 SkyLabs AI, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

module Unix = struct
  open Unix

  type t = float

  let get : unit -> t = fun _ ->
    let t = times () in
    t.tms_utime +. t.tms_stime
end

module Monotonic = struct
  (* Monotomic timestamp in nano-seconds, divided by 4. *)
  type t = int

  let now : unit -> t = fun _ ->
    let t = Mtime.to_uint64_ns (Mtime_clock.now ()) in
    let t = Int64.shift_right_logical t 2 in
    Int64.to_int t

  let in_mus : t -> int = fun t -> t / 250

  let diff_mus : t -> t -> int = fun t0 t1 ->
    if t0 <= t1 then (t1 - t0) / 250 else
      invalid_arg "Time.Monotonic.diff_mus"
end
