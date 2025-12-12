(*
 * Copyright (c) 2020-2025 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *
 * This file is derived from code original to the Iris project. That
 * original code is
 *
 *	Copyright Iris developers and contributors
 *
 * and used according to the following license.
 *
 *	SPDX-License-Identifier: BSD-3-Clause
 *
 * Original Code:
 * https://gitlab.mpi-sws.org/iris/iris/-/blob/5bb93f57729a8cc7d0ffeaab769cd24728e51a38/iris/base_logic/lib/cancelable_invariants.v
 *
 * Original Iris License:
 * https://gitlab.mpi-sws.org/iris/iris/-/blob/5bb93f57729a8cc7d0ffeaab769cd24728e51a38/LICENSE-CODE
 *)

(** Extraction of cancelable invariants that is general w.r.t HasOwn, and not
  tied to iProp.

  Most proofs in this file generalize those of Iris, see the link above.
  In many cases, the proofs are unchanged and are exact duplicates of those in
  Iris. But their types did change and become more general.

  TODO: These should be upstreamed to Iris. **)

Require Import iris.bi.lib.fractional.
Require Export iris.algebra.frac.
Require Export iris.base_logic.lib.cancelable_invariants. (* << exporting [cinvG] *)

Require Import iris.bi.derived_laws.
Import bi.

Require Import bluerock.iris.extra.proofmode.proofmode.

Require Export bluerock.iris.extra.bi.invariants.
Require Export bluerock.iris.extra.bi.own.

Set Default Proof Using "Type".
Set Suggest Proof Using.

#[global] Hint Opaque
  base_logic.lib.cancelable_invariants.cinv
  base_logic.lib.cancelable_invariants.cinv_own : br_opacity.

(** Duplicates from cancelable_invariants. This one is not tied to iProp. *)
(* The statements and (most of) the proofs should stay the same as those of
  iProp's cancelable invariants. *)
Section defs.
  Context `{!BiFUpd PROP} `{!HasOwn PROP fracR}.

  Definition cinv_own (γ : gname) (p : frac) : PROP := own γ p.

  Definition cinv (N : namespace) (γ : gname) (P : PROP) : PROP :=
    inv N (P ∨ cinv_own γ 1).
End defs.

#[global] Instance: Params (@cinv) 5 := {}.

(* TODO: allocation rules are missing. These rely on the specific model of PROP,
  so the client of this library needs the provide the corresponding model of
  invariants for their PROP, and then prove the allocation rules. *)
(* Such a model exists for iProp, see
  https://gitlab.mpi-sws.org/iris/iris/-/blob/5bb93f57729a8cc7d0ffeaab769cd24728e51a38/iris/base_logic/lib/invariants.v#L27 *)

Section proofs.
  (* TODO: too many ... Also, not all lemmas need all of these (which may affect
    performance). *)
  Context `{!BiEmbed siPropI PROP}
          `{!BiBUpd PROP} `{!BiFUpd PROP} `{!BiBUpdFUpd PROP}
          `{!BiLaterContractive PROP}
          `{!HasOwn PROP fracR} `{!HasOwnValid PROP fracR}.
  Local Set Default Proof Using "Type*".

  Global Instance cinv_own_timeless γ p : Timeless (cinv_own γ p).
  Proof. rewrite /cinv_own; apply _. Qed.

  Global Instance cinv_contractive N γ : Contractive (cinv N γ).
  Proof. solve_contractive. Qed.
  Global Instance cinv_ne N γ : NonExpansive (cinv N γ).
  Proof. exact: contractive_ne. Qed.
  Global Instance cinv_proper N γ : Proper ((≡) ==> (≡)) (cinv N γ).
  Proof. exact: ne_proper. Qed.

  Global Instance cinv_persistent N γ P : Persistent (cinv N γ P).
  Proof. rewrite /cinv; apply _. Qed.
  Global Instance cinv_affine N γ P: Affine (PROP:=PROP) (cinv N γ P).
  Proof. rewrite /cinv; apply _. Qed.

  Global Instance cinv_own_fractional γ : Fractional (cinv_own γ) | 0.
  Proof. intros ??. by rewrite /cinv_own -own_op. Qed.
  Global Instance cinv_own_as_fractional γ q :
    AsFractional (cinv_own γ q) (cinv_own γ) q.
  Proof. split. done. apply _. Qed.

  (**
  Absent in Iris upstream.
  TODO: switch to ⌜q ≤ 1⌝%Qp conclusion, maybe after Iris bump.
  we currently lack [frac_validI] to do that.. *)
  Lemma cinv_own_valid_1 γ q : cinv_own γ q ⊢ ✓ q.
  Proof. apply (own_valid γ q). Qed.

  Lemma cinv_own_valid γ q1 q2 :
    cinv_own γ q1 ⊢ cinv_own γ q2 -∗ ✓ (q1 + q2)%Qp.
  Proof. apply (own_valid_2 γ q1 q2). Qed.

  Lemma cinv_own_1_l γ q : cinv_own γ 1 -∗ cinv_own γ q -∗ False.
  Proof.
    iIntros "H1 H2".
    iDestruct (cinv_own_valid with "H1 H2") as %[]%(exclusive_l 1%Qp).
  Qed.

  Lemma cinv_iff N γ P Q : cinv N γ P -∗ □ ▷ (P ∗-∗ Q) -∗ cinv N γ Q.
  Proof.
    iIntros "HI #HPQ". iApply (inv_iff with "HI"). iIntros "!> !>".
    iSplit; try iIntros "[?|?]"; by [iRight | iLeft; iApply "HPQ" ].
  Qed.

  (*** Accessors *)
  Lemma cinv_acc_strong E N γ p P :
    ↑N ⊆ E →
    cinv N γ P -∗ (cinv_own γ p ={E,E∖↑N}=∗
    ▷ P ∗ cinv_own γ p ∗ (∀ E' : coPset, ▷ P ∨ cinv_own γ 1 ={E',↑N ∪ E'}=∗ emp)).
  Proof.
    iIntros (?) "Hinv Hown".
    iPoseProof (inv_acc (↑ N) N with "Hinv") as "H"; first done.
    rewrite difference_diag_L.
    iPoseProof (fupd_mask_frame_r _ _ (E ∖ ↑ N) with "H") as "H"; first set_solver.
    rewrite left_id_L -union_difference_L //. iMod "H" as "[[$ | >Hown'] H]".
    - iIntros "{$Hown} !>" (E') "HP".
      iPoseProof (fupd_mask_frame_r _ _ E' with "(H [HP])") as "H"; first set_solver.
      { iDestruct "HP" as "[?|?]"; eauto. }
      by rewrite left_id_L.
    - iDestruct (cinv_own_1_l with "Hown' Hown") as %[].
  Qed.

  Lemma cinv_acc E N γ p P :
    ↑N ⊆ E →
    cinv N γ P -∗ cinv_own γ p ={E,E∖↑N}=∗ ▷ P ∗ cinv_own γ p ∗ (▷ P ={E∖↑N,E}=∗ emp).
  Proof.
    iIntros (?) "#Hinv Hγ".
    iMod (cinv_acc_strong with "Hinv Hγ") as "($ & $ & H)"; first done.
    iIntros "!> HP".
    rewrite {2}(union_difference_L (↑N) E)=> //.
    iApply "H". by iLeft.
  Qed.

  (*** Other *)
  Lemma cinv_cancel E N γ P : ↑N ⊆ E → cinv N γ P -∗ cinv_own γ 1 ={E}=∗ ▷ P.
  Proof.
    iIntros (?) "#Hinv Hγ".
    iMod (cinv_acc_strong with "Hinv Hγ") as "($ & Hγ & H)"; first done.
    rewrite {2}(union_difference_L (↑N) E)=> //.
    iMod ("H" with "[Hγ]"); last done. by iRight.
  Qed.

  Global Instance into_inv_cinv N γ P : IntoInv (cinv N γ P) N := {}.

  Global Instance into_acc_cinv E N γ P p :
    IntoAcc (X:=unit) (cinv N γ P)
            (↑N ⊆ E) (cinv_own γ p) (fupd E (E∖↑N)) (fupd (E∖↑N) E)
            (λ _, ▷ P ∗ cinv_own γ p)%I (λ _, ▷ P)%I (λ _, None).
  Proof.
    rewrite /IntoAcc /accessor. iIntros (?) "#Hinv Hown".
    rewrite exist_unit -assoc.
    iMod (cinv_acc with "Hinv Hown") as "($ & $ & Close)"; [done|].
    iIntros "!> P". by iMod ("Close" with "P").
  Qed.
End proofs.

#[global] Hint Opaque cinv_own cinv : typeclass_instances br_opacity.
