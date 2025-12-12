(*
 * Copyright (c) 2021 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bluerock.iris.extra.bi.entailsN.

(** [uPred M] supports [entailsN] *)
Section uPred_entailsN.
  Context {M : ucmra}.

  Inductive uPred_entailsN' (n : nat) (P Q : uPred M) : Prop :=
    { uPred_in_entailsN : ∀ n' x, n' ≤ n -> ✓{n'} x → uPred_holds P n' x → uPred_holds Q n' x }.
  #[local] Instance uPred_entailsN : EntailsN (uPred M) := uPred_entailsN'.

  Lemma uPred_entailsN_mixin : BiEntailsNMixin (uPredI M).
  Proof.
    split.
    - (** entailsN_trans *) intros P Q R n HPQ HQR. split=>n' x Hn Hx HP.
      apply HQR; auto. by apply HPQ.
    - (** entails_entailsN *) intros P Q. split.
      + case=>HPQ n. split; naive_solver.
      + intros HPQ. split=>n x Hn Hx. by apply (HPQ n).
    - (** dist_entailsN *) intros P Q n. split.
      + intros HPQ. by split; split; apply HPQ.
      + intros [[?] [?]]. split; naive_solver.
    - (** pure_elimN' *) intros P Q n. uPred.unseal=>HPQ.
      split=>n' x Hn Hx HP. by apply HPQ.
    - (** and_introN *) intros P Q R n HPQ HPR. uPred.unseal. constructor.
      split. by apply HPQ. by apply HPR.
    - (** impl_introN *) intros P Q R n. repeat uPred.unseal=>-[HPQ].
      split=>n1 x Hn1 Hx HP. intros n2 y Hinc Hn2 Hy HQ.
      apply HPQ; [by etrans|done|split; last done].
      eauto using uPred_mono, cmra_included_includedN.
    - (** forall_introN *) intros A P Q n HPQ. split=>n' r Hn Hr HP.
      uPred.unseal=>a. by apply (HPQ a).
    - (** exist_elimN *) intros A P Q n HPQ. split=>n' r Hn Hr.
      uPred.unseal. intros [x Hx]. by apply (HPQ x).
    - (** sep_monoN *) intros P P' Q Q' n [HPQ] [HPQ']. uPred.unseal.
      constructor=>n' x Hn Hv. intros (y1 & y2 & Hy & HP1 & HP2).
      rewrite {}Hy in Hv *. exists y1, y2.
      naive_solver eauto using cmra_validN_op_l, cmra_validN_op_r.
    - (** wand_introN_r *) uPred.unseal=>P Q R n -[HPQ].
      split=>n1 x1 Hn1 Hv1 HP n2 x2 Hn2 Hv2 HQ. apply HPQ; [by etrans|done|].
      exists x1, x2. split_and?; [done|by eapply uPred_mono |done].
  Qed.
  #[global] Instance uPred_bi_entailsN : BiEntailsN (uPredI M) :=
    {| bi_entailsN_mixin := uPred_entailsN_mixin |}.
End uPred_entailsN.
