(*
 * Copyright (C) 2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import skylabs.ltac2.extra.internal.init.
Require Import skylabs.ltac2.extra.internal.constr.
Require Import skylabs.ltac2.extra.internal.level_env.
Require Import skylabs.ltac2.extra.internal.printf.
Require Import skylabs.ltac2.extra.internal.control.

Module Substitute.
  Import Ltac2.
  Import LevelEnv.
  Import Constr Unsafe.
  Import Printf.
  Import Control.

  Axiom test : nat -> nat -> nat -> nat -> Prop.

  Ltac2 assert_constr_eq a b : unit :=
    if Constr.equal a b then
      ()
    else
      throw_invalid! "%t ≠ %t" a b.
  Ltac2 assert_rel_decl_eq a b : unit :=
    assert_constr_eq (RelDecl.type a) (RelDecl.type b);
    match RelDecl.value a, RelDecl.value b with
    | Some a, Some b => assert_constr_eq a b
    | None, None => ()
    | _, _ => throw_invalid! "%a and %a disagree on having a value" RelDecl.pp a RelDecl.pp b
    end.

  Ltac2 test_env_with_let offset :=
    let make_rel i := make_rel (Int.add i offset) in
    let e := LevelEnv.empty_w_offset offset in
    let e := LevelEnv.add_decl_level e (RelDecl.Assum (Binder.make (Some @a) 'nat)) in
    let e := LevelEnv.add_decl_level e (RelDecl.Assum (Binder.make (Some @A) (make_app1 '(@eq nat 1) (make_rel 1)))) in
    let e := LevelEnv.add_decl_level e (RelDecl.Assum (Binder.make (Some @b) 'nat)) in
    let e := LevelEnv.add_decl_level e (RelDecl.Assum (Binder.make (Some @B) (make_app1 '(@eq nat 2) (make_rel 3)))) in
    let e := LevelEnv.add_decl_level e (RelDecl.Assum (Binder.make (Some @C) (make_app1 '(@eq nat 3) '3))) in
    let e := LevelEnv.add_decl_level e (RelDecl.Assum (Binder.make (Some @d) 'nat)) in
    let e := LevelEnv.add_decl_level e (RelDecl.Assum (Binder.make (Some @D) (make_app1 '(@eq nat 4) (make_rel 6)))) in
    (* printf "%a" LevelEnv.pp_named e; *)
    e.

  Ltac2 test_env_wo_let offset :=
    let make_rel i := make_rel (Int.add i offset) in
    let e := LevelEnv.empty_w_offset offset in
    let e := LevelEnv.add_decl_level e (RelDecl.Assum (Binder.make (Some @a) 'nat)) in
    let e := LevelEnv.add_decl_level e (RelDecl.Assum (Binder.make (Some @A) (make_app1 '(@eq nat 1) (make_rel 1)))) in
    let e := LevelEnv.add_decl_level e (RelDecl.Assum (Binder.make (Some @b) 'nat)) in
    let e := LevelEnv.add_decl_level e (RelDecl.Assum (Binder.make (Some @B) (make_app1 '(@eq nat 2) (make_rel 3)))) in
    let e := LevelEnv.add_decl_level e (RelDecl.Def (Binder.make (Some @c) 'nat) '3) in
    let e := LevelEnv.add_decl_level e (RelDecl.Assum (Binder.make (Some @C) (make_app1 '(@eq nat 3) (make_rel 5)))) in
    let e := LevelEnv.add_decl_level e (RelDecl.Assum (Binder.make (Some @d) 'nat)) in
    let e := LevelEnv.add_decl_level e (RelDecl.Assum (Binder.make (Some @D) (make_app1 '(@eq nat 4) (make_rel 7)))) in
    (* printf "%a" LevelEnv.pp_named e; *)
    e.

  Ltac2 test_substitute_def offset :=
    let make_rel i := make_rel (Int.add i offset) in
    let (ref_env, ref_term) :=
      let e := test_env_with_let offset in
      let t := make_app4 '@test (make_rel 1) (make_rel 3) '3 (make_rel 6) in
      (e, t)
    in

    let (env, term) :=
      let e := test_env_wo_let offset in
      let t := make_app4 '@test (make_rel 1) (make_rel 3) (make_rel 5) (make_rel 7) in
      let (e, subs) := LevelEnv.substitute_defs e in
      (* printf "%a" (pp_list pp_constr) subs; *)
      (e, substnl subs offset t)
    in
    (* printf "%a" LevelEnv.pp_named ref_env; *)
    (* printf "%t" ref_term; *)
    (* printf "%a" LevelEnv.pp_named env; *)
    (* printf "%t" term; *)
    List.iter2 assert_rel_decl_eq (LevelEnv.to_list ref_env) (LevelEnv.to_list env);
    assert_constr_eq ref_term term.


  Goal True.
  Proof.
    test_substitute_def 0.
    test_substitute_def 1.
    test_substitute_def 2.
    test_substitute_def 3.
    test_substitute_def 4.
    test_substitute_def 5.
    test_substitute_def 6.
    test_substitute_def 7.
    exact I.
  Qed.


  Goal True.
  Proof.
    let e := test_env_with_let 1 in
    let (p,s) := LevelEnv.cut e 2 in
    let e' := LevelEnv.append p s in
    List.iter2 assert_rel_decl_eq (LevelEnv.to_list e) (LevelEnv.to_list e').
    exact I.
  Qed.

  Goal True.
    intros.
    let e := LevelEnv.empty in
      let e := LevelEnv.add_decl_level e (RelDecl.Def (Binder.make (Some @c) 'nat) '3) in
    let (ev, _) := make_evar_in_level_env true e 'nat in
    Control.new_goal ev > [|exact &c] > [exact I].
  Qed.

End Substitute.
