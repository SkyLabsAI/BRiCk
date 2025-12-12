(*
 * Copyright (c) 2021 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(** Own instances for iProp **)
(* TODO: these should be upstreamed to Iris. *)
Require Export bluerock.iris.extra.si_logic.bi.

Require Export iris.base_logic.lib.own. (* << exporting [inG] and [gFunctors] *)

Require Export bluerock.iris.extra.bi.own.

(* Instances for iProp *)

(* Embedding of si in iProp. It seems that such an embedding doesn't exist
  upstream yet. *)
Program Definition si_embed_def {M} : Embed siPropI (uPredI M) :=
  λ P, {| uPred_holds n x := siProp_holds P n |}.
Solve Obligations with naive_solver eauto using siProp_closed.
Definition si_embed_aux : seal (@si_embed_def). Proof. by eexists. Qed.
Definition si_embed := si_embed_aux.(unseal).
Definition si_embed_eq : @si_embed = _ := si_embed_aux.(seal_eq).
#[global] Arguments si_embed {_} _%_bi_scope : assert.

Section si_embedding.
  #[local] Existing Instance si_embed.
  Context {M : ucmra}.
  Notation PROP := (uPredI M).

  #[local] Arguments siProp_holds !_ _ / : assert.
  #[local] Arguments uPred_holds _ !_ _ _ / : assert.
  #[local] Coercion uPred_holds : uPred >-> Funclass.

  Program Definition si_unembed (P : PROP) : siProp :=
    {| siProp_holds n := P n ε |}.
  Next Obligation. move=>P n1 n2 /= HP Hn. by eapply uPred_mono. Qed.

  #[local] Instance si_unembed_ne : NonExpansive si_unembed.
  Proof.
    intros n P1 P2 HP. constructor=>??. apply HP; auto using ucmra_unit_validN.
  Qed.

  Lemma si_embed_unembed P : si_unembed (embed P) ≡ P.
  Proof. rewrite si_embed_eq. by constructor. Qed.

  #[local] Ltac unseal :=
    unfold embed, bi_embed_embed; cbn;
    do ?rewrite si_embed_eq; unfold si_embed_def; cbn;
    try uPred.unseal;
    (* FIXME: figure out what is happening. *)
    cbv [siPropI bi_emp bi_later siProp_plainlyC siProp_internal_eq bi_internal_eq_internal_eq bi_plainly_plainly];
    siProp.unseal;
    try siProp_primitive.unseal.

  #[local] Ltac unseal' :=
    let n := fresh "n" in let x := fresh "x" in
    constructor; intros n x ?; unseal.

  Lemma si_embedding_mixin : BiEmbedMixin siPropI PROP si_embed.
  Proof.
    split.
    - intros n P1 P2 HP. unseal'=>?. by apply HP.
    - intros P1 P2 HP. unseal'. by apply HP.
    - intros P [HP]. constructor=>n _. generalize (HP n ε).
      unseal. auto using ucmra_unit_validN.
    - intros PROP' ? P Q.
      rewrite -{2}(si_embed_unembed P) -{2}(si_embed_unembed Q). apply (f_equivI _).
    - by unseal'.
    - intros. unseal'=>HPQ ??. eapply HPQ; [done..|by eapply cmra_validN_le].
    - intros. by unseal'.
    - intros. by unseal'.
    - intros. unseal'. split; last naive_solver.
      intros []. exists ε. eexists. by rewrite left_id.
    - intros P Q. unseal'=> PQ ??.
      apply (PQ _ ε); [done|rewrite right_id; by eapply cmra_validN_le].
    - intros P. by unseal'.
  Qed.
  #[global] Instance si_embedding : BiEmbed siPropI PROP :=
    {| bi_embed_mixin := si_embedding_mixin |}.

  #[global] Instance si_embed_emp : BiEmbedEmp siPropI PROP.
  Proof. rewrite /BiEmbedEmp. by unseal'. Qed.

  #[global] Instance si_embed_later : BiEmbedLater siPropI PROP.
  Proof. intros P. constructor=>-[]; by repeat unseal. Qed.

  #[global] Instance si_embed_internal_eq : BiEmbedInternalEq siPropI PROP.
  Proof. intros A x y. unseal'. by repeat unseal. Qed.

  #[global] Instance si_embed_plainly : BiEmbedPlainly siPropI PROP.
  Proof. intros P. unseal'. by unseal. Qed.

  (* TODO: uPred_cmra_valid should have been defined as si_cmra_valid.
    This is to be fixed upstream. *)
  Lemma si_cmra_valid_validI {A : cmra} (a : A) :
    ⎡ si_cmra_valid a ⎤ ⊣⊢@{uPredI M} uPred_cmra_valid a.
  Proof.
    constructor => ???. unseal. by rewrite si_cmra_valid_eq.
  Qed.
End si_embedding.

Section iprop_instances.
  Context `{Hin: inG Σ A}.

  Notation iPropI := (iPropI Σ).

  Definition has_own_iprop_def : HasOwn iPropI A := {|
    own := base_logic.lib.own.own ;
    own_op := base_logic.lib.own.own_op ;
    own_mono := base_logic.lib.own.own_mono ;
    own_ne := base_logic.lib.own.own_ne ;
    own_timeless := base_logic.lib.own.own_timeless ;
    own_core_persistent := base_logic.lib.own.own_core_persistent ;
  |}.
  #[local] Definition has_own_iprop_aux : seal (@has_own_iprop_def). Proof. by eexists. Qed.
  #[global] Instance has_own_iprop : HasOwn iPropI A := has_own_iprop_aux.(unseal).
  Definition has_own_iprop_eq :
    @has_own_iprop = @has_own_iprop_def := has_own_iprop_aux.(seal_eq).

  Lemma uPred_cmra_valid_bi_cmra_valid (a : A) :
    (uPred_cmra_valid a) ⊣⊢@{iPropI} bi_cmra_valid a.
  Proof.
    (* FIXME: this rewrite used to be taken care of by simpl (or /=). *)
    assert (bi_cmra_valid a = si_embed (si_cmra_valid a)) as -> by by lazy.
    by rewrite /= si_cmra_valid_eq upred.uPred_cmra_valid_unseal si_embed_eq.
  Qed.

  #[global] Instance has_own_valid_iprop : HasOwnValid iPropI A.
  Proof.
    constructor. intros. rewrite -uPred_cmra_valid_bi_cmra_valid.
    by rewrite has_own_iprop_eq /= base_logic.lib.own.own_valid.
  Qed.

  #[global] Instance has_own_update_iprop : HasOwnUpd iPropI A.
  Proof.
    constructor; rewrite has_own_iprop_eq /=.
    - setoid_rewrite (bi.affine_affinely (bi_pure _)).
      by apply base_logic.lib.own.own_updateP.
    - setoid_rewrite (bi.affine_affinely (bi_pure _)).
      by apply base_logic.lib.own.own_alloc_strong_dep.
  Qed.
End iprop_instances.

#[global] Instance has_own_unit_iprop {Σ} {A : ucmra} `{Hin: inG Σ A} :
  HasOwnUnit (iPropI Σ) A.
Proof. constructor; rewrite has_own_iprop_eq /=. by apply base_logic.lib.own.own_unit. Qed.
