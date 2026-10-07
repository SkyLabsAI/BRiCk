(*
 * Copyright (C) 2026 SkyLabs AI, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import Corelib.Force.
Require Import skylabs.ltac2.extra.internal.init.
Require Import skylabs.ltac2.extra.internal.constr.

Import Ltac2.

Module BlockedIterators.
  Axiom dep : forall n : nat, Blocked (n = n).
  Axiom nested : Blocked (Blocked nat).

  Ltac2 check_depth n c :=
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.Rel i => Control.assert_true (Int.le i n)
    | _ => ()
    end.

  Ltac2 rec walk n c :=
    check_depth n c;
    Constr.Unsafe.map_with_binders (Int.add 1) walk n c.

  Ltac2 rec walk_full n c :=
    check_depth n c;
    Constr.Unsafe.map_with_full_binders
      (fun _ n => Int.add n 1) walk_full n c.

  Ltac2 rec replace_zero c :=
    if Constr.equal c '0 then '1
    else Constr.Unsafe.map replace_zero c.

  Goal True.
  Proof.
    let c := constr:(__block _
      (fun n : nat => let m := n in __unblock (dep m))) in
    Control.assert_true (Constr.equal (walk 0 c) c);
    Control.assert_true (Constr.equal (walk_full 0 c) c);
    let c := constr:(__block _ (__unblock (__unblock nested))) in
    Control.assert_true (Constr.equal (walk 0 c) c);
    Control.assert_true (Constr.equal (walk_full 0 c) c);
    let c := constr:(__block _
      (__unblock (__block _ 0), __unblock (__block _ 0))) in
    let expected := constr:(__block _
      (__unblock (__block _ 1), __unblock (__block _ 1))) in
    Control.assert_true (Constr.equal (replace_zero c) expected);
    let c := constr:(__run _ _ (__block _ 0) (fun n : nat => n + 0)) in
    let expected := constr:(__run _ _ (__block _ 1) (fun n : nat => n + 1)) in
    Control.assert_true (Constr.equal (replace_zero c) expected);
    Control.assert_true (Constr.equal (walk 0 c) c);
    Control.assert_true (Constr.equal (walk_full 0 c) c);
    let ty := constr:(forall b : Blocked nat, __run _ _ b (fun n : nat => n = n)) in
    let actual := Constr.specialize_products ty [|constr:(__block _ 0)|] in
    Control.assert_true (Constr.equal actual constr:(0 = 0));
    exact I.
  Qed.
End BlockedIterators.
