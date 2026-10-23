(*
 * Copyright (C) 2021-2025 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Export skylabs.prelude.named_binder.
Require Import skylabs.iris.extra.proofmode.proofmode.

#[global] Instance from_forall_named_binder {SI : sidx} {PROP : bi} {A} {name} {id}
  {Φ : NamedBinder A name -> PROP}
  {Φ' : A -> PROP} :
  IdOfBS name id ->
  TCForceEq Φ Φ' ->
  FromForall (∀ x : NamedBinder A name, Φ x) Φ' id | 0.
Proof. move => _ ->. by rewrite /FromForall. Qed.

#[global] Instance into_exist_named_binder {SI : sidx} {PROP : bi} {A} {name} {id}
  {Φ : NamedBinder A name -> PROP}
  {Φ' : A -> PROP} :
  IdOfBS name id ->
  TCForceEq Φ Φ' ->
  IntoExist (∃ x : NamedBinder A name, Φ x) Φ' id | 0.
Proof. move => _ ->. by rewrite /IntoExist. Qed.

Module Type Test.
  Tactic Notation "test" ident(name) := (assert (name = ()) by (destruct name; reflexivity)).

  Goal forall {SI : sidx} {PROP : bi}, ⊢@{PROP} ∀ x : NamedBinder unit "name", False.
  Proof.
    intros SI PROP.
    (* The name returned in [FromForall] is only honored if we explicitly introduce [(?)] *)
    assert_fails (iIntros; test name).
    assert_succeeds (iIntros (?); test name).
  Abort.

  Goal forall {SI : sidx} {PROP : bi},
      (∃ x : NamedBinder unit "name", False) ⊢@{PROP} False.
  Proof.
    intros SI PROP.
    assert_succeeds (iIntros "[% ?]"; test name).
    assert_succeeds (iIntros "H"; iDestruct "H" as (?) "H"; test name).
  Abort.
End Test.
