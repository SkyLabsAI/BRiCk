(*
 * Copyright (C) 2020 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *
 *
 * Some of the following code is derived from code original to the
 * Iris project. That original code is
 *
 *	Copyright Iris developers and contributors
 *
 * and used according to the following license.
 *
 *	SPDX-License-Identifier: BSD-3-Clause
 *
 * Original Iris License:
 * https://gitlab.mpi-sws.org/iris/iris/-/blob/ecad6c9fc48752b52678119c923dc4fff8e96f15/LICENSE-CODE
 *)
Require Export iris.bi.lib.atomic.
Require Import iris.bi.lib.fixpoint_mono.
Require Import skylabs.iris.extra.bi.telescopes.
Require Import skylabs.iris.extra.proofmode.proofmode.
Set Default Proof Using "Type".

(** * Small improvements to atomic updates *)
(** We add a few TC instances that are missing from
[iris.bi.lib.atomic] and are not automatically inferred. *)

Section atomic.
  Context `{BiFUpd PROP} {TA TB : tele}.
  Implicit Types (α : TA → PROP).
  Implicit Types (β Φ : TA → TB → PROP).

  Local Existing Instance atomic_update_pre_mono.

  Lemma atomic_update_mask Eo Ed α β Φ :
    atomic_update Eo (Eo∖Ed) α β Φ ⊣⊢ ∀ E, ⌜Eo ⊆ E⌝ → atomic_update E (E∖Ed) α β Φ.
  Proof.
    iSplit; last first.
    { iIntros "AU". iApply ("AU" with "[% //]"). }
    rewrite atomic.atomic_update_unseal {2}/atomic.atomic_update_def /=.
    iIntros "AU" (E HE).
    iApply (greatest_fixpoint_coiter _ (λ _, atomic.atomic_update_def Eo (Eo ∖ Ed) α β Φ)); last done.
    iIntros "!>" ([]).
    rewrite {1}/atomic.atomic_update_def greatest_fixpoint_unfold.
    rewrite /atomic_update_pre atomic_acc_mask.
    iIntros "AAC". by iApply "AAC".
  Qed.

  Global Instance aacc_proper Eo Ei :
    Proper (
      pointwise_relation TA (≡) ==>
      (≡) ==>
      pointwise_relation TA (pointwise_relation TB (≡)) ==>
      pointwise_relation TA (pointwise_relation TB (≡)) ==>
      (≡)
    ) (atomic_acc (PROP:=PROP) Eo Ei).
  Proof. solve_proper. Qed.

  Global Instance aacc_mono' Eo Ei :
    Proper (
      pointwise_relation TA (≡) ==>
      (⊢) ==>
      pointwise_relation TA (pointwise_relation TB (flip (⊢))) ==>
      pointwise_relation TA (pointwise_relation TB (⊢)) ==>
      (⊢)
    ) (atomic_acc (PROP:=PROP) Eo Ei).
  Proof.
    intros α1 α2 Hα P1 P2 HP β1 β2 Hβ Φ1 Φ2 HΦ. rewrite/atomic_acc.
    repeat f_equiv; by rewrite ?Hα ?Hβ ?HP.
  Qed.

  Global Instance aacc_flip_mono' Eo Ei :
    Proper (
      pointwise_relation TA (≡) ==>
      flip (⊢) ==>
      pointwise_relation TA (pointwise_relation TB (⊢)) ==>
      pointwise_relation TA (pointwise_relation TB (flip (⊢))) ==>
      flip (⊢)
    ) (atomic_acc (PROP:=PROP) Eo Ei).
  Proof. repeat intro. by rewrite -aacc_mono'. Qed.

  Global Instance aupd_proper Eo Ei :
    Proper (
      pointwise_relation TA (≡) ==>
      pointwise_relation TA (pointwise_relation TB (≡)) ==>
      pointwise_relation TA (pointwise_relation TB (≡)) ==>
      (≡)
    ) (atomic_update (PROP:=PROP) Eo Ei).
  Proof.
    rewrite atomic.atomic_update_unseal /atomic.atomic_update_def /atomic_update_pre.
    solve_proper.
  Qed.

  Global Instance aupd_mono' Eo Ei :
    Proper (
      pointwise_relation TA (≡) ==>
      pointwise_relation TA (pointwise_relation TB (flip (⊢))) ==>
      pointwise_relation TA (pointwise_relation TB (⊢)) ==>
      (⊢)
    ) (atomic_update (PROP:=PROP) Eo Ei).
  Proof.
    rewrite atomic.atomic_update_unseal /atomic.atomic_update_def /atomic_update_pre.
    solve_proper.
  Qed.

  Global Instance aupd_flip_mono' Eo Ei :
    Proper (
      pointwise_relation TA (≡) ==>
      pointwise_relation TA (pointwise_relation TB (⊢)) ==>
      pointwise_relation TA (pointwise_relation TB (flip (⊢))) ==>
      flip (⊢)
    ) (atomic_update (PROP:=PROP) Eo Ei).
  Proof. repeat intro. by rewrite -aupd_mono'. Qed.

End atomic.
