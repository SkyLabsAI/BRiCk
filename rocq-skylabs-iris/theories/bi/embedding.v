(*
 * Copyright (c) 2021 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Export iris.bi.embedding.
Require Import bluerock.iris.extra.bi.prelude.

(** * Composing embeddings *)
(** Given embeddings [Embed PROP1 PROP2] and [Embed PROP2 PROP3],
[compose_embed PROP2] is the induced embedding [Embed PROP1 PROP3].
Its [BiEmbed], etc instances are available after [Import
compose_embed_instances]. *)

Definition compose_embed_def {A B C} `{!Embed B C, !Embed A B} : Embed A C :=
  λ P, embed (embed P).
Definition compose_embed_aux : seal (@compose_embed_def). Proof. by eexists. Qed.
Definition compose_embed := compose_embed_aux.(unseal).
Definition compose_embed_eq : @compose_embed = _ := compose_embed_aux.(seal_eq).
#[global] Arguments compose_embed
  {_}%_type_scope _%_type_scope {_}%_type_scope {_ _} _%_bi_scope : assert.

Section instances.
  Context {PROP1 PROP2 PROP3 : bi}.
  Context `{!BiEmbed PROP2 PROP3, !BiEmbed PROP1 PROP2}.

  #[local] Ltac unseal :=
    unfold embed, bi_embed_embed; cbn;
    rewrite !compose_embed_eq; unfold compose_embed_def; cbn.

  Lemma compose_embedding_mixin : BiEmbedMixin PROP1 PROP3 (compose_embed PROP2).
  Proof.
    split.
    - intros n P1 P2 ?. unseal. solve_proper.
    - intros P1 P2 ?. unseal. solve_proper.
    - intros P. unseal. by rewrite !embed_emp_valid.
    - intros. unseal. by rewrite !embed_interal_inj. 
    - unseal. by rewrite !embed_emp_2.
    - intros. unseal. by rewrite !embed_impl_2.
    - intros. unseal. by rewrite !embed_forall_2.
    - intros. unseal. by rewrite !embed_exist_1.
    - intros. unseal. by rewrite !embed_sep.
    - intros. unseal. by rewrite !embed_wand_2.
    - intros. unseal. by rewrite !embed_persistently.
  Qed.
  #[local] Instance compose_embedding : BiEmbed PROP1 PROP3 :=
    {| bi_embed_mixin := compose_embedding_mixin |}.

  Lemma embed_embed P : embed P ⊣⊢@{PROP3} embed (embed P).
  Proof. rewrite {1}/embed/bi_embed_embed/=. by rewrite compose_embed_eq. Qed.

  #[local] Instance compose_embed_emp
      `{!BiEmbedEmp PROP2 PROP3, !BiEmbedEmp PROP1 PROP2} :
    BiEmbedEmp PROP1 PROP3.
  Proof. rewrite/BiEmbedEmp. by rewrite embed_embed !embed_emp_1. Qed.

  #[local] Instance compose_embed_later
      `{!BiEmbedLater PROP2 PROP3, !BiEmbedLater PROP1 PROP2} :
    BiEmbedLater PROP1 PROP3.
  Proof. intros P. by rewrite !embed_embed !embed_later. Qed.

  #[local] Instance compose_embed_internal_eq
      `{!BiInternalEq PROP1, !BiInternalEq PROP2, !BiInternalEq PROP3}
      `{!BiEmbedInternalEq PROP2 PROP3, !BiEmbedInternalEq PROP1 PROP2} :
    BiEmbedInternalEq PROP1 PROP3.
  Proof. intros A x y. by rewrite embed_embed !embed_internal_eq_1. Qed.

  #[local] Instance compose_embed_bupd
      `{!BiBUpd PROP1, !BiBUpd PROP2, !BiBUpd PROP3}
      `{!BiEmbedBUpd PROP2 PROP3, !BiEmbedBUpd PROP1 PROP2} :
    BiEmbedBUpd PROP1 PROP3.
  Proof. intros P. by rewrite !embed_embed !embed_bupd. Qed.

  #[local] Instance compose_embed_fupd
      `{!BiFUpd PROP1, !BiFUpd PROP2, !BiFUpd PROP3}
      `{!BiEmbedFUpd PROP2 PROP3, !BiEmbedFUpd PROP1 PROP2} :
    BiEmbedFUpd PROP1 PROP3.
  Proof. intros E1 E2 P. by rewrite !embed_embed !embed_fupd. Qed.

  #[local] Instance compose_embed_plainly
      `{!BiPlainly PROP1, !BiPlainly PROP2, !BiPlainly PROP3}
      `{!BiEmbedPlainly PROP2 PROP3, !BiEmbedPlainly PROP1 PROP2} :
    BiEmbedPlainly PROP1 PROP3.
  Proof. intros P. by rewrite !embed_embed !embed_plainly. Qed.
End instances.

Module compose_embed_instances.
  #[export] Hint Resolve
    compose_embedding
    compose_embed_emp
    compose_embed_later
    compose_embed_internal_eq
    compose_embed_bupd
    compose_embed_fupd
    compose_embed_plainly
  : typeclass_instances.
End compose_embed_instances.
