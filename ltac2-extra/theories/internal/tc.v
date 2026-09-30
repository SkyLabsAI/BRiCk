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

  (* [resolve_dbs_all dbs t] resolves the goal [t] using typeclass search with
     [Std.default_tc_config]. Like [typeclasses eauto], it is a multi-success
     tactic. Unlike [typeclasses_eauto] it does not use any default
     databases. *)
  Ltac2 resolve_dbs_all (dbs : Std.hint_db list) (t : constr) :=
    let (tc_evar, tc_inst) := Constr.Evar.of_constr (Constr.Evar.make t) in
    let tc := Evar tc_evar tc_inst in
    Control.new_goal tc_evar > [
      | Control.unshelve
          (fun () =>
             Std.typeclasses_eauto_dbs Std.default_tc_config dbs
          )
        (* fail if there are any goals left *)
        > [
          zero_invalid! "typeclasses_eauto_dbs left unsolved goals"
          ..
        ]
      ];
    tc.

  (* [resolve_dbs dbs t] is a non-backtracking version of [resolve_all_dbs dbs t],
     i.e. it commits to the first instance that solves the goal. *)
  Ltac2 resolve_dbs dbs t :=
    Control.once (fun () => resolve_dbs_all dbs t).

  #[deprecated(since="20260424", note="Use [resolve_dbs] or [resolve_dbs_all]")]
  Ltac2 resolve := fun dbs (t: constr) =>
    let (tc_evar, tc_inst) := Constr.Evar.of_constr (Constr.Evar.make t) in
    let tc := Evar tc_evar tc_inst in
    (* Make sure we have exactly 1 goal under focus so that we can add a
       second one and refer to it its absolute index. *)
    Control.enter (fun _ =>
      Control.new_goal tc_evar >
      [|
       (* We need to make sure that TC searches stuck because of constraints
          do not count as successful searches. Hence, we add `solve` *)
       solve [ Std.typeclasses_eauto None None dbs ]
      ]
    );
    tc.
End TC.
