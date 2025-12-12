(*
 * Copyright (C) 2020 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import stdpp.coPset.
Require Import iris.bi.bi.
Require Import iris.bi.updates.
Require Import iris.bi.monpred.
Require Import iris.proofmode.environments.
Require Import bluerock.iris.extra.proofmode.proofmode.
Set Default Proof Using "Type".

(** * Bidirectional fancy updates *)
(** We leave [fupd_iff] transparent for the same (poor) reason as
[bi_wand_iff]. We'd otherwise have to develop a proper theory,
including proof mode instances. *)
Definition fupd_iff `{BiFUpd PROP} (E1 E2 : coPset) (P Q : PROP) : PROP :=
  ((P ={E1,E2}=∗ Q) ∧ (Q ={E2,E1}=∗ P))%I.
Arguments fupd_iff {_ _} _ _ _%_I _%_I : assert, simpl never.
#[global] Instance: Params (@fupd_iff) 2 := {}.

Notation "P ∗={ E1 , E2 }=∗ Q" := (fupd_iff E1 E2 P Q)
  (at level 99, E1,E2 at level 50, Q at level 200, no associativity,
   format "'[' P  '/' ∗={ E1 , E2 }=∗  Q ']'") : bi_scope.
Notation "P ∗={ E }=∗ Q" := (fupd_iff E E P Q)
  (at level 99, E at level 50, Q at level 200, no associativity,
   format "'[' P  '/' ∗={ E }=∗  Q ']'") : bi_scope.
(* cf [iris.bi.ascii] *)
Notation "P *={ E1 , E2 }=* Q" := (P ∗={E1,E2}=∗ Q)%I
  (at level 99, E1,E2 at level 50, Q at level 200, no associativity,
   only parsing) : bi_scope.
Notation "P *={ E }=* Q" := (P ∗={E}=∗ Q)%I
  (at level 99, E at level 50, Q at level 200, no associativity,
   only parsing) : bi_scope.

Section fupd_iff.
  Context `{BiFUpd PROP}.
  Implicit Types P Q : PROP.

  Global Instance fupd_iff_ne E1 E2 : NonExpansive2 (@fupd_iff PROP _ E1 E2).
  Proof. solve_proper. Qed.
  Global Instance fupd_iff_proper E1 E2 :
    Proper ((⊣⊢) ==> (⊣⊢) ==> (⊣⊢)) (@fupd_iff PROP _ E1 E2) := ne_proper_2 _.

  Lemma fupd_iff_intro E P Q : P ∗-∗ Q ⊢ (P ∗={E}=∗ Q).
  Proof.
    rewrite/bi_wand_iff.
    apply bi.and_intro; [apply bi.and_elim_l'|apply bi.and_elim_r'];
      auto using bi.wand_mono, fupd_intro.
  Qed.
  Lemma fupd_iff_refl P E : ⊢ P ∗={E}=∗ P.
  Proof.
    apply bi.and_intro; apply bi.wand_intro_l; rewrite right_id; apply fupd_intro.
  Qed.
  Lemma fupd_iff_sym P Q E1 E2 : (P ∗={E1,E2}=∗ Q) ⊢ Q ∗={E2,E1}=∗ P.
  Proof.
    iIntros "HPQ". iSplit; iIntros "H"; by iMod ("HPQ" with "H") as "$".
  Qed.
  Lemma fupd_iff_trans R E2 P Q E1 E3 :
    (P ∗={E1,E2}=∗ R) ⊢ (R ∗={E2,E3}=∗ Q) -∗ P ∗={E1,E3}=∗ Q.
  Proof.
    iIntros "PR RQ". iSplit.
    - iIntros "P". iMod ("PR" with "P") as "R". by iMod ("RQ" with "R") as "$".
    - iIntros "Q". iMod ("RQ" with "Q") as "R". by iMod ("PR" with "R") as "$".
  Qed.
End fupd_iff.

Section monpred.
  Context {I : biIndex} `{BiFUpd PROP}.
  Implicit Types P Q : monPred I PROP.

  Global Instance fupd_iff_objective E1 E2 P Q `{!Objective P, !Objective Q} :
    Objective (P ∗={E1,E2}=∗ Q).
  Proof. apply _. Qed.

  Lemma monPred_at_fupd_iff E1 E2 (i : I) P Q :
    monPred_at (P ∗={E1,E2}=∗ Q) i ⊣⊢ ∀ j, (⌜i ⊑ j⌝ → P j ∗={E1,E2}=∗ Q j).
  Proof.
    rewrite monPred_at_and !monPred_at_wand. setoid_rewrite monPred_at_fupd.
    apply (anti_symm _). (* todo: shorten the following *)
    - iIntros "HPQ" (j) "%". iSplit; iIntros "H";
        [iDestruct "HPQ" as "[HPQ _]"|iDestruct "HPQ" as "[_ HPQ]"];
        by iApply ("HPQ" with "[%]").
    - iIntros "HPQ". iSplit; iIntros (j) "% H";
        [iDestruct ("HPQ" $! j with "[%]") as "[HPQ _]"
        |iDestruct ("HPQ" $! j with "[%]") as "[_ HPQ]"]; auto;
        by iApply "HPQ".
  Qed.
End monpred.

Lemma embed_fupd_iff `{BiEmbedFUpd PROP1 PROP2} E1 E2 (P Q : PROP1) :
  ⎡P ∗={E1,E2}=∗ Q⎤ ⊣⊢@{PROP2} (⎡P⎤ ∗={E1,E2}=∗ ⎡Q⎤).
Proof. by rewrite embed_and !embed_wand !embed_fupd. Qed.

(** cf the "Automation" section of [iris.proofmode.ltac_tactics] *)
#[global] Hint Extern 1 (envs_entails _ (_ ∗={_,_}=∗ _)) => iSplit : core.
