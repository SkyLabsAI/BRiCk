(*
 * Copyright (c) 2021 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import iris.bi.monpred.
Require Import bluerock.iris.extra.bi.entailsN.

(** [monPred I PROP] supports [entailsN] if [PROP] does *)
Section monPred_entailsN.
  Context {I : biIndex} `{BiEntailsN PROP}.
  Notation monPred := (monPred I PROP).
  Notation monPredI := (monPredI I PROP).
  Implicit Types i : I.
  Implicit Types P Q : monPred.

  Inductive monPred_entailsN' (n : nat) (P Q : monPred) : Prop :=
    { monPred_in_entailsN i : P i ⊢{n} Q i }.
  #[local] Instance monPred_entailsN : EntailsN monPred := monPred_entailsN'.

  Lemma monPred_entailsN_mixin : BiEntailsNMixin monPredI.
  Proof.
    split.
    - (** entailsN_trans *) intros P Q R n [HPQ] [HQR]. split=>i.
      by rewrite (HPQ i) (HQR i).
    - (** entails_entailsN *) intros P Q. split.
      + move=>[HPQ] n. split=>i. apply entails_entailsN, HPQ.
      + intros HPQ. split=>i. apply entails_entailsN=>n. apply HPQ.
    - (** dist_entailsN *) intros P Q. split.
      + case. setoid_rewrite dist_entailsN=>HPQ.
        split; split=>i; by destruct (HPQ i).
      + intros [[?] [?]]. split=>i. apply dist_entailsN. by split.
    - (** pure_elimN' *) intros P Q n HQ. split=>i.
      rewrite monPred_at_pure. apply pure_elimN'=>HP.
      rewrite -(monPred_at_pure i). apply (HQ HP).
    - (** and_introN *) intros P Q R n [HQ] [HR]. split=>i.
      rewrite monPred_at_and. by apply and_introN.
    - (** impl_introN_r *) intros P Q R n [HR]. split=>i.
      rewrite monPred_at_impl. apply forall_introN=>j.
      apply impl_introN_l, impl_elimN_l'. apply pure_elimN'=>Hj.
      apply impl_introN_r, impl_introN_r. rewrite left_id.
      rewrite -(HR j) monPred_at_and. f_equiv.
      by apply entails_entailsN, monPred_mono.
    - (** forall_introN *) intros A P Q n HQ. split=>i.
      rewrite monPred_at_forall. apply forall_introN=>a. apply (HQ a).
    - (** exist_elimN *) intros A P Q n HQ. split=>i.
      rewrite monPred_at_exist. apply exist_elimN=>a. apply (HQ a).
    - (** sep_monoN *) intros P P' Q Q' n [HQ] [HQ']. split=>i.
      rewrite !monPred_at_sep. by apply sep_monoN.
    - (** wand_introN_r *) intros P Q R n [HR]. split=>i.
      rewrite monPred_at_wand. apply forall_introN=>j.
      apply impl_introN_l, impl_elimN_l'. apply pure_elimN'=>Hj.
      apply impl_introN_r. rewrite left_id. apply wand_introN_r.
      rewrite -(HR j) monPred_at_sep. f_equiv.
      by apply entails_entailsN, monPred_mono.
  Qed.
  #[global] Instance monPred_bi_entailsN : BiEntailsN monPredI :=
    {| bi_entailsN_mixin := monPred_entailsN_mixin |}.
End monPred_entailsN.

Section monpred.
  Context {I : biIndex} `{BiEntailsN PROP}.
  Implicit Types i j : I.
  Implicit Types P Q : monPred I PROP.

  Lemma monPred_monoN n i j P : i ⊑ j → monPred_at P i ⊢{n} monPred_at P j.
  Proof. intros. by apply entails_entailsN, monPred_mono. Qed.
End monpred.
