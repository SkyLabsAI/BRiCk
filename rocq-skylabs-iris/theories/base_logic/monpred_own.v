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

Require Import skylabs.iris.extra.bi.embedding.
Require Import skylabs.iris.extra.bi.own.
Require Import skylabs.iris.extra.bi.weakly_objective.
Require Import skylabs.iris.extra.base_logic.iprop_own.

Implicit Type (γ : gname).

(* Instances for monpred I PROP *)
Section with_PROP.
  Context {I : biIndex} {PROP : bi}.

  Notation monPred  := (monPred I PROP).
  Notation monPredI := (monPredI I PROP).

  Section with_cmra.
    Context {A : cmra} `{Hown: HasOwn PROP A}.
    Implicit Type (a : A).

    (* sealing here should boost performance, but it requires us to re-export
      properties of embedding. *)
    #[program]
    Definition has_own_monpred_def : HasOwn monPredI A := {|
      own := λ γ a , ⎡ own γ a ⎤%I |}.
    Next Obligation. intros. by rewrite -embed_sep -own_op. Qed.
    Next Obligation. solve_proper. Qed.
    Next Obligation. solve_proper. Qed.
    #[local] Definition has_own_monpred_aux : seal (@has_own_monpred_def). Proof. by eexists. Qed.
    #[global] Instance has_own_monpred : HasOwn monPredI A := has_own_monpred_aux.(unseal).
    Definition has_own_monpred_eq :
      @has_own_monpred = @has_own_monpred_def := has_own_monpred_aux.(seal_eq).

    (* some re-exporting of embedding properties *)
    #[global] Instance monPred_own_objective γ a :
      Objective (own γ a).
    Proof. rewrite has_own_monpred_eq. apply _. Qed.

    #[global] Instance monPred_own_weakly_objective γ a :
      WeaklyObjective (own γ a).
    Proof. rewrite has_own_monpred_eq. apply _. Qed.

    #[local] Ltac unseal_monpred :=
      constructor; intros; rewrite /own has_own_monpred_eq /has_own_monpred_def.

    #[global] Instance has_own_update_monpred `{!BiBUpd PROP, !HasOwnUpd PROP A} :
      HasOwnUpd monPredI A.
    Proof.
      unseal_monpred.
      - rewrite own_updateP //.
        rewrite embed_bupd embed_exist.
        (do 2 f_equiv) => x.
        by rewrite embed_sep embed_affinely embed_pure.
      - rewrite /bi_emp_valid -embed_emp own_alloc_strong_dep //.
        rewrite embed_bupd embed_exist.
        (do 2 f_equiv) => x.
        by rewrite embed_sep embed_affinely embed_pure.
    Qed.

    Section with_compose_embed_instances.
      Import compose_embed_instances.

      #[global] Instance has_own_valid_monpred
        `{!BiEmbed siPropI PROP, !HasOwnValid PROP A} :
        HasOwnValid monPredI A.
      Proof. unseal_monpred. by rewrite own_valid -embedding.embed_embed. Qed.
    End with_compose_embed_instances.
  End with_cmra.

  Section with_ucmra.
    Context {A : ucmra}.
    Context `{Hown: HasOwn PROP A}.

    #[global] Instance has_own_unit_monpred `{!BiBUpd PROP, !HasOwnUnit PROP A}:
      HasOwnUnit monPredI A.
    Proof.
      constructor; intros; rewrite /own has_own_monpred_eq /has_own_monpred_def; red.
      by rewrite -(@embed_emp PROP) -embed_bupd own_unit.
    Qed.
  End with_ucmra.
End with_PROP.

(* Instances for monpred I iPropI *)
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
