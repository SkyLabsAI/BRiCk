(*
 * Copyright (C) 2021-2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import skylabs.ltac2.extra.internal.control.
Require Import skylabs.ltac2.extra.internal.constr.
Require Import skylabs.ltac2.extra.internal.std.

(** Typeclasses. *)
Module TC.
  Import Ltac2.
  Import Constr.Unsafe.

  Ltac2 resolve := fun dbs (t: constr) =>
    let (tc_evar, tc_inst) := Constr.Evar.of_constr (Constr.Evar.make t) in
    let tc := Evar tc_evar tc_inst in
    (* Make sure we have exactly 1 goal under focus so that we can add a
       second one and refer to it its absolute index. *)
    Control.enter (fun _ =>
      Control.new_goal tc_evar >
      [|
       (* We need to make sure that TC searches stuck because of constraints
          do not count as successful searches. Hence, we add `progress` *)
       solve [ Std.typeclasses_eauto None None dbs ]
      ]
    );
    tc.
End TC.
