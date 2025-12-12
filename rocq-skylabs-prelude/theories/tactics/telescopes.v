(*
 * Copyright (C) 2021-2022 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bluerock.prelude.telescopes.

(** * Telescopes *)
(**
The tactic [destruct_tele] projects bound variables out of every
[tele_arg] in the Coq context, enabling telescopic function
applications to reduce. The variant [destruct_tele/=] follows this
with [cbn in *] to simplify away, e.g., any lingering [tele_app]s.

THIS CODE IS DEPRECATED: The need for this tactic arose from the
inductive representation of [tele_arg] which stdpp previously used.
The current fixpoint representation needs no extra [destruct]s to
reduce [tele_app]s.
*)
Ltac destruct_tele :=
  repeat lazymatch goal with
  | tx : tele_arg (TeleS _) |- _ =>
    let x := fresh tx in let t := fresh tx in
    destruct (tele_arg_inv tx) as (x & t & ->); clear tx
  | t : tele_arg TeleO |- _ =>
    generalize (tele_arg_O_inv t); intros ->; clear t
  end.
Tactic Notation "destruct_tele" "/=" := destruct_tele; cbn in *.
