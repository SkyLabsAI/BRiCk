(*
 * Copyright (c) 2021-2025 BlueRock Security, Inc.
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
 * https://gitlab.mpi-sws.org/iris/iris/-/blob/90b6007faea2b61546aed01fe0ed9936b55468d1/iris/base_logic/lib/na_invariants.v
 *
 * Original Iris License:
 * https://gitlab.mpi-sws.org/iris/iris/-/blob/90b6007faea2b61546aed01fe0ed9936b55468d1/LICENSE-CODE
 *)

Require Import iris.algebra.gset iris.algebra.coPset.
Require Export iris.base_logic.lib.na_invariants. (* << exporting [na_inv_pool_name], [na_invG] *)
Require Import iris.bi.bi.

Require Import skylabs.iris.extra.proofmode.proofmode.

Require Export skylabs.iris.extra.bi.invariants.
Require Import skylabs.iris.extra.bi.own.

Set Default Proof Using "Type".
Set Suggest Proof Using.

#[global] Hint Opaque
  base_logic.lib.na_invariants.na_inv
  base_logic.lib.na_invariants.na_own : br_opacity.

(** Extraction of non-atomic invariants that is general w.r.t HasOwn,
  and not tied to iProp.

  Most proofs in this file generalize those of Iris, see the link above.
  In many cases, the proofs are unchanged and are exact duplicates of those in
  Iris. But their types did change and become more general.

  TODO: These should be upstreamed to Iris. **)

Local Notation na_ownR :=
  (prodR coPset_disjR (gset_disjR positive)) (only parsing).

Section defs.
  Context `{!BiFUpd PROP} `{!HasOwn PROP na_ownR}.

  Definition na_own (p : na_inv_pool_name) (E : coPset) : PROP :=
    own p (CoPset E, GSet ∅).

  Definition na_inv (p : na_inv_pool_name) (N : namespace) (P : PROP) : PROP :=
    (*
    Note: Building on atomic invariants in this way leads to, under
    [PROP := monPredI], a side-condition something like [Objective P].
    *)
    (∃ i, ⌜i ∈ (↑N:coPset)⌝ ∧
          inv N (P ∗ own p (CoPset ∅, GSet {[i]}) ∨ na_own p {[i]}))%I.
End defs.

Global Instance: Params (@na_inv) 5 := {}.

#[global] Hint Opaque na_own na_inv : typeclass_instances br_opacity.

(* TODO: allocation rules are missing. These rely on the specific model of PROP,
  so the client of this library needs the provide the corresponding model of
  invariants for their PROP, and then prove the allocation rules. *)
(* Such a model exists for iProp, see
  https://gitlab.mpi-sws.org/iris/iris/-/blob/90b6007faea2b61546aed01fe0ed9936b55468d1/iris/base_logic/lib/invariants.v#L27 *)

Section proofs.
  Context `{!BiEmbed siPropI PROP}.
  Context `{!BiBUpd PROP, !BiFUpd PROP, !BiBUpdFUpd PROP}.
  Context `{!BiLaterContractive PROP}.
  Context `{!HasOwn PROP na_ownR, !HasOwnValid PROP na_ownR}.
  Context `{!HasOwnUpd PROP na_ownR}.
  Import bi.

  Local Set Default Proof Using "Type*".

  (* Duplicates from Iris, but do not tie to iProp *)
  (* These statements and proofs are the same, except where required
  for non-affine BIs. *)

  Global Instance na_own_timeless p E : Timeless (na_own p E).
  Proof. rewrite /na_own; apply _. Qed.

  Global Instance na_inv_contractive p N : Contractive (na_inv p N).
  Proof. rewrite /na_inv. solve_contractive. Qed.
  Global Instance na_inv_ne p N : NonExpansive (na_inv p N).
  Proof. apply (contractive_ne _). Qed.
  Global Instance na_inv_proper p N : Proper ((≡) ==> (≡)) (na_inv p N).
  Proof. apply (ne_proper _). Qed.

  Global Instance na_inv_persistent p N P : Persistent (na_inv p N P).
  Proof. rewrite /na_inv; apply _. Qed.
  Global Instance na_inv_affine p N P : Affine (na_inv p N P).
  Proof. rewrite /na_inv; apply _. Qed.

  Lemma na_inv_iff p N P Q : na_inv p N P -∗ □ ▷ (P ∗-∗ Q) -∗ na_inv p N Q.
  Proof.
    iIntros "HI #HPQ". rewrite /na_inv. iDestruct "HI" as (i ?) "HI".
    iExists i. iSplit; first done. iApply (inv_iff with "HI").
    iIntros "!> !>".
    iSplit; by iIntros "[[? Ho]|?]"; [| by iRight]; iLeft; iFrame "Ho"; iApply "HPQ".
  Qed.

  Lemma na_alloc_strong (P : na_inv_pool_name → Prop) :
    pred_infinite P → ⊢ |==> ∃ p, ⌜P p⌝ ∗ na_own p ⊤.
  Proof.
    intros. by iMod (own_alloc_strong _ P) as (p ?) "?"; auto.
  Qed.

  Lemma na_alloc : ⊢ |==> ∃ p, na_own p ⊤.
  Proof. by apply own_alloc. Qed.

  Lemma na_own_disjoint p E1 E2 : na_own p E1 ⊢ na_own p E2 -∗ ⌜E1 ## E2⌝.
  Proof.
    apply wand_intro_r.
    rewrite /na_own -own_op own_valid -coPset_disj_valid_op. by iIntros ([? _]).
  Qed.

  Lemma na_own_union p E1 E2 :
    E1 ## E2 → na_own p (E1 ∪ E2) ⊣⊢ na_own p E1 ∗ na_own p E2.
  Proof.
    intros ?. by rewrite /na_own -own_op -pair_op coPset_disj_union.
  Qed.

  Lemma na_own_acc E2 E1 tid :
    E2 ⊆ E1 → na_own tid E1 -∗ na_own tid E2 ∗ (na_own tid E2 -∗ na_own tid E1).
  Proof.
    intros HF. assert (E1 = E2 ∪ (E1 ∖ E2)) as -> by exact: union_difference_L.
    rewrite na_own_union; last by set_solver+. iIntros "[$ $]". auto.
  Qed.

  Lemma na_inv_acc p E F N P :
    ↑N ⊆ E → ↑N ⊆ F →
    na_inv p N P -∗ na_own p F ={E}=∗ ▷ P ∗ na_own p (F∖↑N) ∗
                       (▷ P ∗ na_own p (F∖↑N) ={E}=∗ na_own p F).
  Proof.
    rewrite /na_inv. iIntros (??) "#Hnainv Htoks".
    iDestruct "Hnainv" as (i) "[% Hinv]".
    rewrite [F as X in na_own p X](union_difference_L (↑N) F) //.
    rewrite [X in (X ∪ _)](union_difference_L {[i]} (↑N)) ?na_own_union; [|set_solver..].
    iDestruct "Htoks" as "[[Htoki $] $]".
    iInv "Hinv" as "[[$ >Hdis]|>Htoki2]" "Hclose".
    - iMod ("Hclose" with "[Htoki]") as "_"; first auto.
      iIntros "!> [HP $]".
      iInv N as "[[? >Hdis2]|>Hitok]".
      + iDestruct (own_valid_2 with "Hdis Hdis2") as %[_ Hval%gset_disj_valid_op].
        set_solver.
      + iSplitR "Hitok"; last by iFrame. eauto with iFrame.
    - iDestruct (na_own_disjoint with "Htoki Htoki2") as %?. set_solver.
  Qed.

  Global Instance into_inv_na p N P : IntoInv (na_inv p N P) N := {}.

  Global Instance into_acc_na p F E N P :
    IntoAcc (X:=unit) (na_inv p N P)
            (↑N ⊆ E ∧ ↑N ⊆ F) (na_own p F) (fupd E E) (fupd E E)
            (λ _, ▷ P ∗ na_own p (F∖↑N))%I (λ _, ▷ P ∗ na_own p (F∖↑N))%I
              (λ _, Some (na_own p F))%I.
  Proof.
    rewrite /IntoAcc /accessor. iIntros ((?&?)) "#Hinv Hown".
    rewrite exist_unit -assoc /=.
    iApply (na_inv_acc with "Hinv"); done.
  Qed.

End proofs.
