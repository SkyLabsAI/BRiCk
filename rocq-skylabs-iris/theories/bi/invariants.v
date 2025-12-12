(*
 * Copyright (c) 2020 BlueRock Security, Inc.
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
 * https://gitlab.mpi-sws.org/iris/iris/-/blob/5bb93f57729a8cc7d0ffeaab769cd24728e51a38/iris/base_logic/lib/invariants.v
 *
 * Original Iris License:
 * https://gitlab.mpi-sws.org/iris/iris/-/blob/5bb93f57729a8cc7d0ffeaab769cd24728e51a38/LICENSE-CODE
 *)

(** Extraction of invariants that doesn't depend on iProp.
  Most proofs in this file generalize those of Iris, see the link above.
  In many cases, the proofs are unchanged and are exact duplicates of those in
  Iris. But their types did change and become more general.

  TODO: These should be upstreamed to Iris. **)

Require Export iris.base_logic.lib.invariants. (* << export [invGS] *)

Require bluerock.prelude.tactics.base_dbs.
Require Import bluerock.iris.extra.proofmode.proofmode.

Set Default Proof Using "Type".
Set Suggest Proof Using.

Implicit Types (N : namespace).

Section defs.
  Context `{!BiFUpd PROP}.

  (* Duplicates from Iris, but for general [bi], instead of being tied to [iProp]. *)
  Definition inv_def N (P : PROP) : PROP :=
    (□ ∀ E : coPset, ⌜↑N ⊆ E⌝ → |={E,E ∖ ↑N}=> ▷ P ∗ (▷ P ={E ∖ ↑N,E}=∗ emp))%I.
  Local Definition inv_aux : seal (@inv_def). Proof. by eexists. Qed.
  Definition inv := inv_aux.(unseal).
  Definition inv_eq : @inv = @inv_def := inv_aux.(seal_eq).
  #[global] Hint Opaque inv : br_opacity.

  Section instances.
    Context `{CON: BiLaterContractive PROP}.
    Global Instance inv_contractive N : Contractive (inv N).
    Proof using CON. rewrite inv_eq. solve_contractive. Qed.

    Global Instance inv_ne `{BiLaterContractive PROP} N : NonExpansive (inv N).
    Proof using CON. apply contractive_ne, _. Qed.

    Global Instance inv_proper N : Proper (equiv ==> equiv) (inv N).
    Proof using CON. apply ne_proper, _. Qed.
  End instances.

  Global Instance inv_persistent N P : Persistent (inv N P).
  Proof. rewrite inv_eq. apply _. Qed.
  Global Instance inv_affine N P : Affine (inv N P).
  Proof. rewrite inv_eq. apply _. Qed.
End defs.

Arguments inv {_ _} N P%_I.
#[global] Instance : Params (@inv) 3 := {}.

(* TODO: allocation rules are missing. These rely on the specific model of PROP,
  so the client of this library needs the provide the corresponding model of
  invariants for their PROP, and then prove the allocation rules. *)
(* Such a model exists for iProp, see
  https://gitlab.mpi-sws.org/iris/iris/-/blob/5bb93f57729a8cc7d0ffeaab769cd24728e51a38/iris/base_logic/lib/invariants.v#L27 *)

Section inv_properties.
Context `{!BiFUpd PROP}.

Implicit Types (P Q : PROP) (E : coPset).

(* Duplicates from Iris, but do not tie to iProp *)
(* These statements (and probably proofs) are the same, except where required
for linearity. *)
Lemma inv_alter N P Q :
  inv N P -∗ □ ▷ (P -∗ Q ∗ (Q -∗ P)) -∗ inv N Q.
Proof.
  rewrite inv_eq. iIntros "#HI #HPQ !>" (E SUB).
  iMod ("HI" $! E SUB) as "[HP Hclose]".
  iDestruct ("HPQ" with "HP") as "[$ HQP]".
  iIntros "!> HQ". iApply "Hclose". iApply "HQP". done.
Qed.

Lemma inv_iff N P Q : inv N P -∗ □ ▷ (P ∗-∗ Q) -∗ inv N Q.
Proof.
  iIntros "#HI #HPQ". iApply (inv_alter with "HI").
  iIntros "!> !> HP". iSplitL "HP".
  - by iApply "HPQ".
  - iIntros "HQ". by iApply "HPQ".
Qed.

Lemma inv_acc E N P :
  ↑N ⊆ E → inv N P ={E,E∖↑N}=∗ ▷ P ∗ (▷ P ={E∖↑N,E}=∗ emp).
Proof.
  rewrite inv_eq /inv_def; iIntros (?) "HI". by iApply ("HI" $! E with "[%//]").
Qed.

Lemma inv_combine N1 N2 N P Q :
  N1 ## N2 →
  ↑N1 ∪ ↑N2 ⊆@{coPset} ↑N →
  inv N1 P -∗ inv N2 Q -∗ inv N (P ∗ Q).
Proof.
  rewrite inv_eq. iIntros (??) "#HinvP #HinvQ !>"; iIntros (E ?).
  iMod ("HinvP" with "[%]") as "[$ HcloseP]"; first set_solver.
  iMod ("HinvQ" with "[%]") as "[$ HcloseQ]"; first set_solver.
  iMod (fupd_mask_subseteq (E ∖ ↑N)) as "Hclose"; first set_solver.
  iIntros "!> [HP HQ]".
  iMod "Hclose" as "_". iMod ("HcloseQ" with "HQ") as "?". by iMod ("HcloseP" with "HP").
Qed.

Lemma inv_combine_dup_l `{BiAffine PROP} N P Q :
  □ ▷ (P -∗ P ∗ P) -∗
  inv N P -∗ inv N Q -∗ inv N (P ∗ Q).
Proof.
  rewrite inv_eq. iIntros "#HPdup #HinvP #HinvQ !>" (E SUB).
  iMod ("HinvP" with "[%//]") as "[HP HcloseP]".
  iDestruct ("HPdup" with "HP") as "[$ HP]".
  iMod ("HcloseP" with "HP") as "?".
  iMod ("HinvQ" with "[%//]") as "[$ HcloseQ]".
  iIntros "!> [HP HQ]". by iMod ("HcloseQ" with "HQ").
Qed.

(** ** Proof mode integration *)
Global Instance into_inv_inv N P : IntoInv (inv N P) N := {}.

Global Instance into_acc_inv N P E:
  IntoAcc (X := unit) (inv N P)
          (↑N ⊆ E) emp (fupd E (E ∖ ↑N)) (fupd (E ∖ ↑N) E)
          (λ _ : (), (▷ P)%I) (λ _ : (), (▷ P)%I) (λ _ : (), None).
Proof.
  rewrite inv_eq /IntoAcc /accessor bi.exist_unit.
  iIntros (?) "Hinv _". iMod ("Hinv" $! E with "[%//]") as "[$ Close]".
  iIntros "!> P /=". by iMod ("Close" with "P") as "?".
Qed.

(** ** Derived properties *)
Lemma inv_acc_strong E N P :
  ↑N ⊆ E → inv N P ={E,E∖↑N}=∗ ▷ P ∗ ∀ E', ▷ P ={E',↑N ∪ E'}=∗ emp.
Proof.
  iIntros (?) "Hinv".
  iPoseProof (inv_acc (↑ N) N with "Hinv") as "H"; first done.
  rewrite difference_diag_L.
  iPoseProof (fupd_mask_frame_r _ _ (E ∖ ↑ N) with "H") as "H"; first set_solver.
  rewrite left_id_L -union_difference_L //. iMod "H" as "[$ H]"; iModIntro.
  iIntros (E') "HP".
  iPoseProof (fupd_mask_frame_r _ _ E' with "(H HP)") as "H"; first set_solver.
  by rewrite left_id_L.
Qed.

Lemma inv_acc_timeless E N P `{!Timeless P} :
  ↑N ⊆ E → inv N P ={E,E∖↑N}=∗ P ∗ (P ={E∖↑N,E}=∗ emp).
Proof.
  iIntros (?) "Hinv". iMod (inv_acc with "Hinv") as "[>HP Hclose]"; auto.
  iIntros "!> {$HP} HP". iApply "Hclose"; auto.
Qed.

Lemma inv_split_l N P Q : inv N (P ∗ Q) -∗ inv N P.
Proof.
  iIntros "#HI". iApply inv_alter; eauto.
  iIntros "!> !> [$ $] $".
Qed.
Lemma inv_split_r N P Q : inv N (P ∗ Q) -∗ inv N Q.
Proof.
  iIntros "#HI". iApply inv_alter; eauto.
  iIntros "!> !> [$ $] $".
Qed.
Lemma inv_split N P Q : inv N (P ∗ Q) -∗ inv N P ∗ inv N Q.
Proof.
  iIntros "#H".
  iPoseProof (inv_split_l with "H") as "$".
  iPoseProof (inv_split_r with "H") as "$".
Qed.
End inv_properties.
