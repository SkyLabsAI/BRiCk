(*
 * Copyright (C) 2020-21 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *
 *)
Require Import bluerock.iris.extra.algebra.telescopes.
Require Export iris.bi.telescopes.
Require Export bluerock.iris.extra.bi.prelude.
Require iris.proofmode.class_instances.
Import ChargeNotation.

#[local] Set Universe Polymorphism.
#[local] Set Printing Universes.
#[local] Set Printing Coercions.

(** Analogues of [bi_texist] and [bi_tforall], with extra universe
polymorphism and a slightly different interface. *)
Fixpoint tbi_exist@{X Z Y} {PROP : bi} {t : tele@{X}}
  : forall (P : tele_fun@{X Z Y} t PROP), PROP :=
  match t as t0 return ((t0 -t> PROP) → PROP) with
  | [tele] => fun x : PROP => x
  | @TeleS X binder =>
    fun P : (∀ x : X, binder x -t> PROP) => Exists x : X, tbi_exist (P x)
  end.

Fixpoint tbi_forall@{X Z Y} {PROP : bi} {t : tele@{X}}
  : forall (P : tele_fun@{X Z Y} t PROP), PROP :=
  match t as t0 return ((t0 -t> PROP) → PROP) with
  | [tele] => fun x : PROP => x
  | @TeleS X binder =>
    fun P : (∀ x : X, binder x -t> PROP) => Forall x : X, tbi_forall (P x)
  end.

(** Small improvements to [bi_tforall], [bi_texist] *)
Section telescopes.
  Context {PROP : bi} {TT : tele}.

  (** Enable, e.g., [f_equiv] on proofmode goals [(∀.. x, P) -∗ ∀.. x, Q]. *)
  #[global] Instance bi_tforall_mono' :
    Proper (pointwise_relation _ (⊢) ==> (⊢)) (@bi_tforall PROP TT).
  Proof. intros f1 f2 Hf. rewrite !bi_tforall_forall. solve_proper. Qed.

  #[global] Instance bi_texist_mono' :
    Proper (pointwise_relation _ (⊢) ==> (⊢)) (@bi_texist PROP TT).
  Proof. intros f1 f2 Hf. rewrite !bi_texist_exist. solve_proper. Qed.

  (** Enable, e.g., [f_equiv] on goals [(∀.. x, P) -∗ ∀.. x, Q]. *)
  #[global] Instance bi_tforall_flip_mono' :
    Proper (
      pointwise_relation _ (flip (⊢)) ==>
      (flip (⊢))
    ) (@bi_tforall PROP TT).
  Proof. intros f1 f2 Hf. rewrite !bi_tforall_forall. solve_proper. Qed.

  #[global] Instance bi_texist_flip_mono' :
    Proper (pointwise_relation _ (⊢) ==> (⊢)) (@bi_texist PROP TT).
  Proof. intros f1 f2 Hf. rewrite !bi_texist_exist. solve_proper. Qed.
End telescopes.

Section tele_fun_quantifiers.
  Context {PROP : bi}.
  Implicit Types t : tele.

  Lemma tbi_exist_bi_texist {t} (P : t -t> PROP) : tbi_exist P -|- ∃.. x, tele_app P x.
  Proof. induction t as [|?? IH]; simpl; first done. f_equiv=>x. by rewrite IH. Qed.
  Lemma bi_texist_tbi_exist {t} (R : t -> PROP) : (∃.. x, R x) -|- tbi_exist (tele_bind R).
  Proof. rewrite tbi_exist_bi_texist. f_equiv=>x. by rewrite tele_app_bind. Qed.

  (** Avoid the preceding lemmas which would unduly constrain universe [Y]. *)
  Lemma tbi_exist_exist@{X Z Y} {t : tele@{X}} (P : tele_fun@{X Z Y} t PROP) :
    tbi_exist P -|- Exists x, tele_app P x.
  Proof.
    induction t as [|B bnd IH]; simpl; split'.
    - by rewrite -(bi.exist_intro TargO).
    - apply bi.exist_elim=>x. by rewrite (tele_arg_O_inv x).
    - apply bi.exist_elim=>b. rewrite IH. apply bi.exist_elim=>ys.
      by rewrite -(bi.exist_intro (TargS b ys)).
    - apply bi.exist_elim=>ys. destruct (tele_arg_S_inv ys) as (b & arg & ->). simpl.
      rewrite -(bi.exist_intro b) IH. by rewrite -(bi.exist_intro arg).
  Qed.

  Lemma tbi_exist_mono@{X Z Y} {t : tele@{X}} (P1 P2 : tele_fun@{X Z Y} t PROP) :
    tele_fun_pointwise@{X Z Y} (⊢) P1 P2 -> tbi_exist P1 ⊢ tbi_exist P2.
  Proof. intros. rewrite !tbi_exist_exist. solve_proper. Qed.

  Lemma tbi_exist_ne@{X Z Y} {t : tele@{X}} n (P1 P2 : tele_fun@{X Z Y} t PROP) :
    tele_fun_pointwise@{X Z Y} (dist n) P1 P2 ->
    dist n (tbi_exist P1) (tbi_exist P2).
  Proof. intros. rewrite !tbi_exist_exist. solve_proper. Qed.

  Lemma tbi_exist_proper@{X Z Y} {t : tele@{X}} (P1 P2 : tele_fun@{X Z Y} t PROP) :
    tele_fun_pointwise@{X Z Y} equiv P1 P2 ->
    equiv (tbi_exist P1) (tbi_exist P2).
  Proof. intros. rewrite !tbi_exist_exist. solve_proper. Qed.

  Lemma tbi_forall_bi_tforall {t} (P : t -t> PROP) : tbi_forall P -|- ∀.. x, tele_app P x.
  Proof. induction t as [|?? IH]; simpl; first done. f_equiv=>x. by rewrite IH. Qed.
  Lemma bi_tforall_tbi_forall {t} (R : t -> PROP) : (∀.. x, R x) -|- tbi_forall (tele_bind R).
  Proof. rewrite tbi_forall_bi_tforall. f_equiv=>x. by rewrite tele_app_bind. Qed.

  Lemma tbi_forall_forall@{X Z Y} {t : tele@{X}} (P : tele_fun@{X Z Y} t PROP) :
    tbi_forall P -|- Forall x, tele_app P x.
  Proof.
    induction t as [|B bnd IH]; simpl; split'.
    - apply bi.forall_intro=>x. by rewrite tele_app_bind.
    - by rewrite (bi.forall_elim TargO).
    - apply bi.forall_intro=>ys. destruct (tele_arg_S_inv ys) as (b & arg & ->).
      simpl. by rewrite (bi.forall_elim b) IH (bi.forall_elim arg).
    - apply bi.forall_intro=>b. rewrite IH. apply bi.forall_intro=>ys.
      by rewrite (bi.forall_elim (TargS b ys)).
  Qed.

  Lemma tbi_forall_mono@{X Z Y} {t : tele@{X}} (P1 P2 : tele_fun@{X Z Y} t PROP) :
    tele_fun_pointwise@{X Z Y} (⊢) P1 P2 -> tbi_forall P1 ⊢ tbi_forall P2.
  Proof. intros. rewrite !tbi_forall_forall. solve_proper. Qed.

  Lemma tbi_forall_ne@{X Z Y} {t : tele@{X}} n (P1 P2 : tele_fun@{X Z Y} t PROP) :
    tele_fun_pointwise@{X Z Y} (dist n) P1 P2 ->
    dist n (tbi_forall P1) (tbi_forall P2).
  Proof. intros. rewrite !tbi_forall_forall. solve_proper. Qed.

  Lemma tbi_forall_proper@{X Z Y} {t : tele@{X}} (P1 P2 : tele_fun@{X Z Y} t PROP) :
    tele_fun_pointwise@{X Z Y} equiv P1 P2 ->
    equiv (tbi_forall P1) (tbi_forall P2).
  Proof. intros. rewrite !tbi_forall_forall. solve_proper. Qed.

  #[global] Instance: Params (@tbi_exist) 2 := {}.
  #[global] Instance tbi_exist_ne' t : NonExpansive (@tbi_exist PROP t).
  Proof. repeat intro. by apply tbi_exist_ne. Qed.
  #[global] Instance tbi_exist_proper' t : Proper (equiv ==> equiv) (@tbi_exist PROP t).
  Proof. repeat intro. by apply tbi_exist_proper. Qed.
  #[global] Instance tbi_exist_mono' {t} :
    Proper (tele_fun_pointwise (⊢) ==> (⊢)) (@tbi_exist PROP t).
  Proof. repeat intro. by apply tbi_exist_mono. Qed.
  #[global] Instance tbi_exist_flip_mono' {t} :
    Proper (tele_fun_pointwise (⊢) --> flip (⊢)) (@tbi_exist PROP t).
  Proof. repeat intro. by apply tbi_exist_mono. Qed.

  #[global] Instance: Params (@tbi_forall) 2 := {}.
  #[global] Instance tbi_forall_ne' t : NonExpansive (@tbi_forall PROP t).
  Proof. repeat intro. by apply tbi_forall_ne. Qed.
  #[global] Instance tbi_forall_proper' t : Proper (equiv ==> equiv) (@tbi_forall PROP t).
  Proof. repeat intro. by apply tbi_forall_proper. Qed.
  #[global] Instance tbi_forall_mono' {t} :
    Proper (tele_fun_pointwise (⊢) ==> (⊢)) (@tbi_forall PROP t).
  Proof. repeat intro. by apply tbi_forall_mono. Qed.
  #[global] Instance tbi_forall_flip_mono' {t} :
    Proper (tele_fun_pointwise (⊢) --> flip (⊢)) (@tbi_forall PROP t).
  Proof. repeat intro. by apply tbi_forall_mono. Qed.

  Section proofmode.
    Import proofmode.classes.

    #[global] Instance tbi_exist_into_exist t (P : t -> PROP) name :
      AsIdentName P name -> IntoExist (tbi_exist (tele_bind P)) P name.
    Proof.
      rewrite /IntoExist=>?. rewrite tbi_exist_exist.
      f_equiv=>x. by rewrite tele_app_bind.
    Qed.
    #[global] Instance tbi_exist_from_exist t (P : t -> PROP) :
      FromExist (tbi_exist (tele_bind P)) P.
    Proof.
      rewrite /FromExist. rewrite tbi_exist_exist.
      f_equiv=>x. by rewrite tele_app_bind.
    Qed.

    #[global] Instance tbi_forall_into_forall t (P : t -> PROP) :
      IntoForall (tbi_forall (tele_bind P)) P.
    Proof.
      rewrite /IntoForall. rewrite tbi_forall_forall.
      f_equiv=>x. by rewrite tele_app_bind.
    Qed.
    #[global] Instance tbi_forall_from_forall t (P : t -> PROP) name :
      AsIdentName P name -> FromForall (tbi_forall (tele_bind P)) P name.
    Proof.
      rewrite /FromForall=>?. rewrite tbi_forall_forall.
      f_equiv=>x. by rewrite tele_app_bind.
    Qed.
  End proofmode.

End tele_fun_quantifiers.
#[global] Hint Opaque tbi_exist tbi_forall : typeclass_instances.

(** On [Import], hide IPM instances related to telescopic quantifiers.
    Those instances can impose spurious universe constraints when
    proving universe polymorphic lemmas about [tbi_exist],
    [tbi_forall]. For example, [iDestruct] on a hypothesis of the form
    [tbi_exist@{X Z Y} (tele_bind ...)] uses the [IntoExist] instance
    for [bi_texist] with the side-effect of constraining universe [Y]
    to being below a small universe like [Type.0]. *)
Module disable_proofmode_telescopes.
  #[export] Remove Hints
    class_instances.into_exist_texist class_instances.from_exist_texist
    class_instances.into_forall_tforall class_instances.from_forall_tforall
    tbi_exist_into_exist tbi_exist_from_exist
    tbi_forall_into_forall tbi_forall_from_forall
  : typeclass_instances.
End disable_proofmode_telescopes.
