(*
 * Copyright (c) 2020-2023 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
(**
This file defines the core [bi] (called [mpred]) that we use for all of our logics.
It is a [bi] parameterized by:
1. a thread information (via [monPred]) that allows distinguishing between
  different implicit contexts, and
2. a CMRA structure in the style of Iris, i.e. [gFunctors], that allows for
  higher-order ghost state.

The construction also bakes in the common pattern of allowing to store global
ghost names directly in the logic rather than needing to pass them separately.
*)

Require Import iris.base_logic.lib.own.
Require Import iris.base_logic.lib.cancelable_invariants.
Require Import iris.bi.monpred.

Require Import bluerock.prelude.base.
Require Import bluerock.iris.extra.bi.prelude.
Require Import bluerock.iris.extra.bi.entailsN.
Require Import bluerock.iris.extra.bi.monpred_entailsN.
Require Import bluerock.iris.extra.base_logic.upred_entailsN.
Import ChargeNotation.

Section mpred.
  Context {thread_info : biIndex} {Σ : gFunctors}.

  (* TODO: seal *)
  Definition mpredI : bi := monPredI thread_info (iPropI Σ).
  Definition mpred := bi_car mpredI.

  Canonical Structure mpredO : ofe := monPredO thread_info (iPropI Σ).

  (* We name this, for manual use later when importing [linearity]. *)
  Lemma mpred_BiAffine : BiAffine mpredI.
  Proof. apply _. Qed.

  (* HACK: this is to prevent IPM from simplifying [mpred] into [monPred].
  Sealing mpred is better *)
  #[global] Instance mpred_bi_bupd : BiBUpd mpredI | 0 := monPred_bi_bupd _ _.
  #[global] Instance mpred_bi_fupd `{!invGS Σ} : BiFUpd mpredI | 0 := monPred_bi_fupd _ _.
  #[global] Instance mpred_bi_bupd_fupd `{!invGS Σ} : BiBUpdFUpd mpredI | 0.
  Proof. apply _. Qed.

  #[global] Instance : BiEntailsN mpredI | 0 := monPred_bi_entailsN.

End mpred.

Bind Scope bi_scope with mpred.

(**
We are making [gFunctors] and [biIndex] classes in our development, so that
we do not have to mention them explicitly in [mpred]. The CONS of this are:
- It it unsafe when there are multiple [gFunctors] or [biIndex] in the context,
  and [mpred] might pick up the wrong one. In case of ambiguity, it is best
  to specify them explicitly, i.e. with [@mpred thread_info Σ].
  In most of our code base, there is likely always one [gFunctors] and one
  [biIndex] in the context.
- It has some performance cost, because now [mpred] has to use typeclass
  resolution for [biIndex]. ([mpred] previously already needs to use typeclass
  resolution for Σ.)
*)
Existing Class gFunctors.
Existing Class biIndex.

(**
To implement higher-order ghost state mentioning [mpred], we
presuppose [mpred ≈ I -mon> iProp] and use the discrete OFE [I -d>
iProp Σ] rather than [monPredO]. We cannot use [monPredO] because Iris
lacks a functor [monPredOF].
*)
Definition later_mpredO (Σ : gFunctors) (thread_info : biIndex) : ofe :=
  laterO (thread_info -d> iPropI Σ).
Definition later_mpredOF (thread_info : biIndex) : oFunctor :=
  laterOF (thread_info -d> idOF).
Definition later_mpred {thread_info : biIndex} {Σ : gFunctors} (P : mpred) :
    later (thread_info -d> iPropI Σ) :=
  Next (monPred_at P).

Section later_mpred.
  Context {thread_info : biIndex} {Σ : gFunctors}.

  #[global] Instance later_mpred_contractive : Contractive later_mpred.
  Proof.
    move => n ?? HP. apply: Next_contractive.
    dist_later_intro. by destruct HP.
  Qed.
  #[global] Instance later_mpred_ne : NonExpansive later_mpred.
  Proof. exact: contractive_ne. Qed.
  #[global] Instance later_mpred_proper : Proper (equiv ==> equiv) later_mpred.
  Proof. exact: ne_proper. Qed.

  Lemma equivI_later_mpred (P Q : mpred) :
    later_mpred P ≡ later_mpred Q -|-@{mpred} |> (P ≡ Q).
  Proof.
    rewrite /later_mpred later_equivI.
    by rewrite discrete_fun_equivI monPred_equivI.
  Qed.
End later_mpred.
#[global] Hint Opaque later_mpred : typeclass_instances.

Section internal_eq.
  Context {thread_info : biIndex} {Σ : gFunctors}.

  Lemma mpred_internal_eq_soundness {A : ofe} (x y : A) :
    |-@{mpredI} x ≡ y -> x ≡ y.
  Proof.
    rewrite monPred_internal_eq_unfold embed_emp_valid.
    apply uPred.internal_eq_soundness.
  Qed.
  Lemma mpred_internal_eq_entails {A B : ofe} (a1 a2 : A) (b1 b2 : B) :
    (∀ n, a1 ≡{n}≡ a2 -> b1 ≡{n}≡ b2) -> a1 ≡ a2 |-@{mpredI} b1 ≡ b2.
  Proof.
    intros. rewrite monPred_internal_eq_unfold. constructor=>i.
    rewrite !monPred_at_embed. by apply uPred.internal_eq_entails.
  Qed.
End internal_eq.
