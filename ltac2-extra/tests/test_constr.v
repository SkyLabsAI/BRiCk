(*
 * Copyright (C) 2021-2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import skylabs.ltac2.extra.internal.init.
Require Import skylabs.ltac2.extra.internal.constr.

Module ConstrSet_test.
  Import Ltac2.
  Import Constr.ConstrSet.

  (* Make sure that all operations on [ConstrSet] work on 0, 1, and many goals
     even when the goals are not currently focussed. *)
  Ltac2 test_multi_goal tac :=
    let t := 'True in
    let f := 'False in
    split; tac t f.

  Goal True /\ True.
   Succeed test_multi_goal (fun _ _ =>
     let _ := empty in ()
   ).
   Succeed test_multi_goal (fun _ _ =>
     if is_empty empty then () else fail
   ).
   Succeed test_multi_goal (fun _ _ =>
     if is_empty (diff empty empty) then () else fail
   ).
   Succeed test_multi_goal (fun t f =>
     let _ := of_list [t; f] in ()
   ).
   Succeed test_multi_goal (fun t f =>
     if mem t (of_list [t; f]) then () else fail
   ).
   Succeed test_multi_goal (fun t f =>
     if mem f (of_list [t; f]) then () else fail
   ).
   Succeed test_multi_goal (fun t f =>
     if mem f (diff (of_list [t; f]) (of_list [f])) then fail else ()
   ).
   Succeed test_multi_goal (fun t f =>
     if mem t (diff (of_list [t; f]) (of_list [f])) then () else fail
   ).
   Succeed test_multi_goal (fun t f =>
     let _ :=
       let l := elements (diff (of_list [t; f]) (of_list [f])) in
       (if List.mem Constr.equal t l then () else fail);
       (if List.mem Constr.equal f l then fail else ())
     in ()
   ).
  Abort.
End ConstrSet_test.

Module DecomposeProj_Tests.
  Import Ltac2.
  Import Constr.Unsafe.Destruct.

  Ltac2 test t :=
    match of_projection t with
    | Some _ => exact I
    | _ => Control.throw (Invalid_argument None)
    end.

  Module NonPrim.
    Record test {n: nat} := TEST { m: nat; H: m=n }.
    Notation t :=
      ltac:(let t := constr:((TEST 1 1 eq_refl).(H)) in exact t)
      (only parsing).
    Goal True. test 't. Qed.
  End NonPrim.

  Module Prim.
    #[projections(primitive)]
    Record test {n: nat} := TEST { m: nat; H: m=n }.
    Notation t1 :=
      ltac:(let t := eval lazy delta [H] in (TEST 1 1 eq_refl).(H) in exact t)
      (only parsing).
    Goal True. test 't1. Qed.

    Notation t2 :=
      ltac:(let t := constr:((TEST 1 1 eq_refl).(H)) in exact t)
      (only parsing).
    Goal True. test 't2. Qed.
  End Prim.
End DecomposeProj_Tests.


Module Vars_Test.
  Import Ltac2.
  Import printf.Printf.

  #[projections(primitive)]
  Record ty (u : unit) := R { f : unit }.

  Lemma test u (r : ty u) : @f u r = tt.
  Proof.
    intros.
    Control.enter (fun () =>
      let g := Control.goal () in
      let v := Constr.Vars.vars_really_needed g in
      Control.assert_true (FSet.mem @u v)
    ).
  Abort.

End Vars_Test.
