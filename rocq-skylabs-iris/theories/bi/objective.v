(*
 * Copyright (c) 2021 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import iris.bi.monpred.
Require Import skylabs.iris.extra.proofmode.proofmode.
Require Import iris.proofmode.monpred.

Require Import skylabs.iris.extra.bi.only_provable.
Require Import skylabs.iris.extra.bi.observe.

Section objective.

  Context {PROP : bi}.
  Context {I J K : biIndex}.

  Lemma objective_of_obs {P : monPred I PROP} Q :
    (Q -> Objective P) ->
    Observe [| Q |] P ->
    Objective P.
  Proof.
    move => HP /observe_monPred_at Hobs i j.
    iIntros "A"%string. iDestruct (Hobs with "A") as %?.
    by iStopProof; apply: HP.
  Qed.

End objective.
