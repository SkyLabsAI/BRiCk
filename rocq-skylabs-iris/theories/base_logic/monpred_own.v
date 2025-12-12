(*
 * Copyright (c) 2021 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(** Own instances for monPred **)
(* TODO: these should be upstreamed to Iris. *)
Require Import iris.si_logic.bi.
Require Import iris.bi.monpred.
Require Import iris.base_logic.lib.own.

Require Import bluerock.iris.extra.bi.embedding.
Require Import bluerock.iris.extra.bi.own.
Require Import bluerock.iris.extra.bi.weakly_objective.
Require Import bluerock.iris.extra.base_logic.iprop_own.

(* Instances for monpred *)

Section si_monpred_embedding.
  Context {I : biIndex} {Σ : gFunctors}.
  Notation monPredI := (monPredI I (iPropI Σ)).
  Import compose_embed_instances.

  (** We could easily replace the hard-coded [iPropI Σ] with any BI
      that embeds [siProp]. *)
  #[global] Instance si_monpred_embedding : BiEmbed siPropI monPredI := _.
  #[global] Instance si_monpred_emp : BiEmbedEmp siPropI monPredI := _.
  #[global] Instance si_monpred_later : BiEmbedLater siPropI monPredI := _.
  #[global] Instance si_monpred_internal_eq : BiEmbedInternalEq siPropI monPredI := _.
  #[global] Instance si_monpred_plainly : BiEmbedPlainly siPropI monPredI := _.

  (* TODO: uPred_cmra_valid should have been defined as si_cmra_valid.
    This is to be fixed upstream in Iris. *)
  Lemma monPred_si_cmra_valid_validI `{inG Σ A} (a : A) :
    ⎡ si_cmra_valid a ⎤ ⊣⊢@{monPredI} ⎡ uPred_cmra_valid a ⎤.
  Proof. by rewrite -si_cmra_valid_validI embedding.embed_embed. Qed.
End si_monpred_embedding.

Section monpred_instances.
  Context {I : biIndex} `{Hin: inG Σ A}.

  Notation iPropI   := (iPropI Σ).
  Notation monPred  := (monPred I iPropI).
  Notation monPredI := (monPredI I iPropI).

  (* sealing here should boost performance, but it requires us to re-export
    properties of embedding. *)
  Program Definition has_own_monpred_def : HasOwn monPredI A := {|
    own := λ γ a , ⎡ own γ a ⎤%I |}.
  Next Obligation. intros. by rewrite -embed_sep -own_op. Qed.
  Next Obligation. solve_proper. Qed.
  Next Obligation. solve_proper. Qed.
  #[local] Definition has_own_monpred_aux : seal (@has_own_monpred_def). Proof. by eexists. Qed.
  #[global] Instance has_own_monpred : HasOwn monPredI A := has_own_monpred_aux.(unseal).
  Definition has_own_monpred_eq :
    @has_own_monpred = @has_own_monpred_def := has_own_monpred_aux.(seal_eq).

  #[local] Ltac unseal_monpred :=
    constructor; intros; rewrite /own has_own_monpred_eq /has_own_monpred_def; red.

  #[global] Instance has_own_valid_monpred: HasOwnValid monPredI A.
  Proof. unseal_monpred. by rewrite own_valid -embedding.embed_embed. Qed.

  #[global] Instance has_own_update_monpred : HasOwnUpd monPredI A.
  Proof.
    unseal_monpred.
    - setoid_rewrite <-(@embed_pure iPropI).
      setoid_rewrite <-embed_affinely.
      setoid_rewrite <-(@embed_sep iPropI).
      setoid_rewrite <-embed_exist.
      by rewrite -embed_bupd -own_updateP.
    - setoid_rewrite <-(@embed_pure iPropI).
      setoid_rewrite <-embed_affinely.
      setoid_rewrite <-(@embed_sep iPropI).
      setoid_rewrite <-embed_exist. rewrite -embed_bupd -(@embed_emp iPropI).
      by rewrite -own_alloc_strong_dep.
  Qed.

  (* some re-exporting of embedding properties *)
  #[global] Instance monPred_own_objective γ (a : A) :
    Objective (own γ a).
  Proof. rewrite has_own_monpred_eq. apply _. Qed.

  #[global] Instance monPred_own_weakly_objective γ x :
    @WeaklyObjective I iPropI (own γ x).
  Proof. rewrite has_own_monpred_eq. apply _. Qed.

End monpred_instances.

#[global] Instance has_own_unit_monpred {I : biIndex} {Σ} {A : ucmra} `{Hin: inG Σ A} :
  HasOwnUnit (monPredI I (iPropI Σ)) A.
Proof.
  constructor; intros; rewrite /own has_own_monpred_eq /has_own_monpred_def; red.
  by rewrite -(@embed_emp (iPropI _)) -embed_bupd own_unit.
Qed.
