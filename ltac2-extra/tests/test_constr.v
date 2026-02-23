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


Module Evar_Test.
  Import Ltac2 Constr Unsafe Printf.

  Goal forall a b : bool, exists x : unit, forall y, a = y -> x = tt /\ x = tt.
  Proof.
    intros.
    Set Printing All.
    Set Printing Existential Instances.
    eexists ?[x].
    lazy_match! goal with
    | [ |- forall y (_ : a = y), ?l = _ /\ _ ] =>
      match kind l with
      | Evar e inst =>
          let ctx := Evar.context e in
          let ids := List.map (fun (id, _, _) => id) ctx in
          Control.assert_true (List.equal Ident.equal ids [@a; @b]);
          let inst := Array.to_list inst in
          (* printf "inst:"; *)
          (* List.iter (printf "%t") inst; *)
          let cmb := List.combine ids (List.rev inst) in
          (* printf "ids:"; *)
          (* List.iter (printf "%I") ids; *)
          Control.assert_true (List.for_all (fun (id, c) => Constr.equal (make_var id) c) cmb)
      | _ => Control.throw (Invalid_argument None)
      end
    end.
    intros.
    split.
    -
      pose (evar := ?x).
      Succeed ltac1:(rename a into c).
      Fail ltac1:(rename a into c); Unification.unify TransparentState.empty constr:(?x) constr:(?x).
      Succeed ltac1:(rename a into c); Unification.unify TransparentState.empty constr:(evar) constr:(evar).
      Succeed ltac1:(rename a into c); Unification.unify TransparentState.empty constr:(?x@{a:=c;b:=b}) constr:(?x@{a:=c;b:=b}).
      Fail ltac1:(rename a into c); ltac1:(instantiate (1 := if c then tt else tt)). (* solution is interpreted using the substitution defined by the instance *)
      Succeed ltac1:(rename a into c); ltac1:(instantiate (1 := if a then tt else tt)). (* solution is interpreted using the substitution defined by the instance *)
      subst a.
      Succeed Unification.unify TransparentState.empty constr:(evar) constr:(evar).
      ltac1:(instantiate (1 := if a then tt else tt)). (* solution is interpreted using the substitution defined by the instance *)
      ltac1:(now destruct y).
    - ltac1:(now destruct a).
  Qed.

End Evar_Test.
