(*
 * Copyright (C) 2022-2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

(** Measurement combinators over [Control.mtime] and [Control.instr]. *)
Require Export skylabs.ltac2.extra.internal.control.
Import Ltac2.

(** [between before after diff f] samples [f] and each resumption of its
    backtracking continuation separately. Each successful result carries only
    that execution's measurement, excluding earlier executions and caller work
    between results. Callers may sum these measurements if desired. Failures
    are forwarded without running the after hook. *)
Ltac2 rec between
  (before : unit -> 'bef)
  (after : unit -> 'aft)
  (diff : 'aft -> 'bef -> 'dif) (f : unit -> 'a) : ('dif * 'a) :=
  let start := before () in
  match Control.case f with
  | Val (v, handler) =>
      let delta := diff (after ()) start in
      Control.plus
        (fun () => (delta, v))
        (fun e => between before after diff (fun () => handler e))
  | Err e => Control.zero e
  end.

Ltac2 with_mtime (f : unit -> 'a) : (int * 'a) :=
  between Control.mtime Control.mtime Int.sub f.

Ltac2 with_instr (f : unit -> 'a) : (int * 'a) :=
  between Control.instr Control.instr Int.sub f.

Ltac2 Type measurement := { mtime : int; instr : int }.

(** Component-wise addition and subtraction using Ltac2 integer arithmetic. *)
Ltac2 add (x : measurement) (y : measurement) : measurement :=
  { mtime := Int.add (x.(mtime)) (y.(mtime));
    instr := Int.add (x.(instr)) (y.(instr)) }.

Ltac2 sub (x : measurement) (y : measurement) : measurement :=
  { mtime := Int.sub (x.(mtime)) (y.(mtime));
    instr := Int.sub (x.(instr)) (y.(instr)) }.

(** [with_msmt f] measures both monotonic microseconds and instructions.
    The time readings surround the instruction readings, keeping clock
    sampling outside the instruction interval. *)
Ltac2 with_msmt (f : unit -> 'a) : (measurement * 'a) :=
  let before () :=
    let mtime := Control.mtime () in
    { mtime; instr := Control.instr () }
  in
  let after () :=
    let instr := Control.instr () in
    { mtime := Control.mtime (); instr }
  in
  between before after sub f.
