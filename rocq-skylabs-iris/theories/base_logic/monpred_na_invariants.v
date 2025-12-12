(**
 * Copyright (C) 2025 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *
 * This file is derived from code original to the GPFSL project. That
 * original code is
 *
 *  Copyright: GPFSL developers and contributors
 *
 * and used according to the following license.
 *
 *  SPDX-License-Identifier: BSD-3-Clause
 *
 * Original Code:
 * https://gitlab.mpi-sws.org/iris/gpfsl/-/blob/35a7c7df492237047d24d996d33f7f102f75e7c5/gpfsl/logic/na_invariants.v
 *
 * Original GPFSL License:
 * https://gitlab.mpi-sws.org/iris/gpfsl/-/blob/35a7c7df492237047d24d996d33f7f102f75e7c5/LICENSE
 *)

Require Import iris.bi.monpred.
Require Import iris.base_logic.lib.invariants. (* << [invGS] *)
Require Import iris.proofmode.monpred.

Require Import bluerock.iris.extra.proofmode.proofmode.

Require Import bluerock.iris.extra.base_logic.iprop_prop.
Require Import bluerock.iris.extra.base_logic.iprop_invariants.
Require Export bluerock.iris.extra.bi.monpred_na_invariants.

(* The [monPred I (iProp Σ)] instances for true thread-local non-atomic invariants.

This is strictly stronger than the version in
bluerock.iris.extra.base_logic.monpred_invariants, as it does not require
the [WeaklyObjective] side-condition.
*)

Section props.
  Context {I : biIndex}.
  Context `{!invGS Σ}.
  Context `{!inG Σ (naEnableMapFunR I)}.
  Context `{!inG Σ (naEnableMapR I)}.

  Lemma na_inv_alloc p E N (P : monPred I (iProp Σ))  :
    ▷ P ={E}=∗ na_inv p N P.
  Proof.
    iIntros "HP".
    iDestruct (monPred_in_intro with "HP") as (s) "[#HV HP]".
    iMod (own_unit (PROP:=iPropI Σ) (A:=naEnableMapFunR I) p) as "Hempty".
    iMod (own_alloc (PROP:=iPropI Σ) (● None)) as (γ) "Hdis"; [by apply auth_auth_valid|].
    destruct (fresh_inv_name ∅ N) as (i & _ & HiN). unfold na_inv.
    iExists i, s, γ. iFrame "# %".
    iMod (inv_alloc N with "[-]") as "$"; [|done].
    iLeft. rewrite monPred_at_later. iNext. iFrame.
  Qed.
End props.
