(*
 * Copyright (c) 2021-2023 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import elpi.apps.locker.locker.
Require Import iris.proofmode.tactics.
Require Import bluerock.iris.extra.bi.prelude.
Require Import bluerock.iris.extra.bi.observe.
Import ChargeNotation.

Module Export Errors.	(* <-- historic *)

mlock Definition ERROR {PROP : bi} {T} (t : T) : PROP := False.
#[global] Arguments ERROR {_ _} _ : assert.	(* mlock bug *)

mlock Definition UNSUPPORTED {PROP : bi} {T} (t : T) : PROP := False.
#[global] Arguments UNSUPPORTED {_ _} _ : assert.	(* mlock bug *)

mlock Definition UNREACHABLE {PROP : bi} {T} (t : T) : PROP := False.
#[global] Arguments UNREACHABLE {_ _} _ : assert.	(* mlock bug *)

Section Errors.
  Context {PROP : bi} {T : Type}.
  Implicit Types (t : T).

  #[local] Notation ERROR := (ERROR (PROP:=PROP)).

  Lemma ERROR_elim t : ERROR t |-- False.
  Proof. by rewrite unlock. Qed.
  Lemma ERROR_elim' t P : ERROR t |-- P.
  Proof. rewrite unlock. apply bi.False_elim. Qed.

  Lemma ERROR_False t : ERROR t -|- False.
  Proof. by rewrite unlock. Qed.

  Example destruct_ERROR t : ERROR t |-- False.
  Proof. Fail iIntros "[]". Abort.

  #[global] Instance ERROR_from_assumption pers t : KnownLFromAssumption pers (ERROR t) False.
  Proof. do 2 red. rewrite ERROR_elim. destruct pers; simpl; eauto. Qed.

  Example destruct_ERROR t : ERROR t |-- False.
  Proof. iIntros "[]". Succeed Qed. Abort.

  #[global] Instance ERROR_sep t : LeftAbsorb equiv (ERROR t) bi_sep.
  Proof. rewrite unlock. apply _. Qed.
  #[global] Instance sep_ERROR t : RightAbsorb equiv (ERROR t) bi_sep.
  Proof. rewrite unlock. apply _. Qed.

  #[global] Instance ERROR_and t : LeftAbsorb equiv (ERROR t) bi_and.
  Proof. rewrite unlock. apply _. Qed.
  #[global] Instance and_ERROR t : RightAbsorb equiv (ERROR t) bi_and.
  Proof. rewrite unlock. apply _. Qed.

  #[global] Instance ERROR_or t : LeftId equiv (ERROR t) bi_or.
  Proof. rewrite unlock. apply _. Qed.
  #[global] Instance or_ERROR t : RightId equiv (ERROR t) bi_or.
  Proof. rewrite unlock. apply _. Qed.

  #[global] Instance observe_from_ERROR Q t : Observe Q (ERROR t).
  Proof. rewrite unlock. apply _. Qed.

  #[global] Instance ERROR_persistent t : Persistent (ERROR t).
  Proof. rewrite unlock. apply _. Qed.
  #[global] Instance ERROR_affine t : Affine (ERROR t).
  Proof. rewrite unlock. apply _. Qed.

  #[local] Notation UNSUPPORTED := (UNSUPPORTED (PROP:=PROP)).

  Lemma UNSUPPORTED_elim t : UNSUPPORTED t |-- False.
  Proof. by rewrite unlock. Qed.
  Lemma UNSUPPORTED_elim' t P : UNSUPPORTED t |-- P.
  Proof. rewrite unlock. apply bi.False_elim. Qed.

  Lemma UNSUPPORTED_False t : UNSUPPORTED t -|- False.
  Proof. by rewrite unlock. Qed.

  Example destruct_UNSUPPORTED t : UNSUPPORTED t |-- False.
  Proof. Fail iIntros "[]". Abort.

  #[global] Instance UNSUPPORTED_from_assumption pers t : KnownLFromAssumption pers (UNSUPPORTED t) False.
  Proof. do 2 red. rewrite UNSUPPORTED_elim. destruct pers; simpl; eauto. Qed.

  Example destruct_UNSUPPORTED t : UNSUPPORTED t |-- False.
  Proof. iIntros "[]". Succeed Qed. Abort.

  #[global] Instance UNSUPPORTED_sep t : LeftAbsorb equiv (UNSUPPORTED t) bi_sep.
  Proof. rewrite unlock. apply _. Qed.
  #[global] Instance sep_UNSUPPORTED t : RightAbsorb equiv (UNSUPPORTED t) bi_sep.
  Proof. rewrite unlock. apply _. Qed.

  #[global] Instance UNSUPPORTED_and t : LeftAbsorb equiv (UNSUPPORTED t) bi_and.
  Proof. rewrite unlock. apply _. Qed.
  #[global] Instance and_UNSUPPORTED t : RightAbsorb equiv (UNSUPPORTED t) bi_and.
  Proof. rewrite unlock. apply _. Qed.

  #[global] Instance UNSUPPORTED_or t : LeftId equiv (UNSUPPORTED t) bi_or.
  Proof. rewrite unlock. apply _. Qed.
  #[global] Instance or_UNSUPPORTED t : RightId equiv (UNSUPPORTED t) bi_or.
  Proof. rewrite unlock. apply _. Qed.

  #[global] Instance observe_from_UNSUPPORTED Q t : Observe Q (UNSUPPORTED t).
  Proof. rewrite unlock. apply _. Qed.

  #[global] Instance UNSUPPORTED_persistent t : Persistent (UNSUPPORTED t).
  Proof. rewrite unlock. apply _. Qed.
  #[global] Instance UNSUPPORTED_affine t : Affine (UNSUPPORTED t).
  Proof. rewrite unlock. apply _. Qed.

  #[local] Notation UNREACHABLE := (UNREACHABLE (PROP:=PROP)).

  Lemma UNREACHABLE_elim t : UNREACHABLE t |-- False.
  Proof. by rewrite unlock. Qed.
  Lemma UNREACHABLE_elim' t P : UNREACHABLE t |-- P.
  Proof. rewrite unlock. apply bi.False_elim. Qed.

  Lemma UNREACHABLE_False t : UNREACHABLE t -|- False.
  Proof. by rewrite unlock. Qed.

  Example destruct_UNREACHABLE t : UNREACHABLE t |-- False.
  Proof. Fail iIntros "[]". Abort.

  #[global] Instance UNREACHABLE_from_assumption pers t : KnownLFromAssumption pers (UNREACHABLE t) False.
  Proof. do 2 red. rewrite UNREACHABLE_elim. destruct pers; simpl; eauto. Qed.

  Example destruct_UNREACHABLE t : UNREACHABLE t |-- False.
  Proof. iIntros "[]". Succeed Qed. Abort.

  #[global] Instance UNREACHABLE_sep t : LeftAbsorb equiv (UNREACHABLE t) bi_sep.
  Proof. rewrite unlock. apply _. Qed.
  #[global] Instance sep_UNREACHABLE t : RightAbsorb equiv (UNREACHABLE t) bi_sep.
  Proof. rewrite unlock. apply _. Qed.

  #[global] Instance UNREACHABLE_and t : LeftAbsorb equiv (UNREACHABLE t) bi_and.
  Proof. rewrite unlock. apply _. Qed.
  #[global] Instance and_UNREACHABLE t : RightAbsorb equiv (UNREACHABLE t) bi_and.
  Proof. rewrite unlock. apply _. Qed.

  #[global] Instance UNREACHABLE_or t : LeftId equiv (UNREACHABLE t) bi_or.
  Proof. rewrite unlock. apply _. Qed.
  #[global] Instance or_UNREACHABLE t : RightId equiv (UNREACHABLE t) bi_or.
  Proof. rewrite unlock. apply _. Qed.

  #[global] Instance observe_from_UNREACHABLE Q t : Observe Q (UNREACHABLE t).
  Proof. rewrite unlock. apply _. Qed.

  #[global] Instance UNREACHABLE_persistent t : Persistent (UNREACHABLE t).
  Proof. rewrite unlock. apply _. Qed.
  #[global] Instance UNREACHABLE_affine t : Affine (UNREACHABLE t).
  Proof. rewrite unlock. apply _. Qed.
End Errors.
End Errors.	(* <-- historic *)
