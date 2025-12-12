(**
 * Copyright (C) 2022 BlueRock Security, Inc.
 * All rights reserved.
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)

Require Import bluerock.iris.extra.proofmode.proofmode.
Require Import bluerock.iris.extra.algebra.dfrac_agree.
Require Import bluerock.iris.extra.bi.spec.frac_splittable.
Require Import bluerock.iris.extra.bi.spec.knowledge.
Require Import bluerock.lang.cpp.logic.
Require Import bluerock.iris.extra.base_logic.own_instances.

Set Printing Coercions.

(**
Ghost reference cell:

- [dfrac_agree.own (g : dfrac_agree.gname A) (q : Qp) (x : A) : mpred]
represents fractional ownership of ghost cell [g] currently containing
[x]

- [dfrac_agree.know (g : dfrac_agree.gname A) (x : A) : mpred]
represents knowledge that ghost cell contains [x]

*)

Module Type DFRAC_AGREE.

  (** CMRA *)

  Parameter G : ∀ (A : Type) (Σ : gFunctors), Set.
  Existing Class G.
  Parameter Σ : ∀ (A : Type), gFunctors.
  #[global] Declare Instance subG {A Σ} : subG (DFRAC_AGREE.Σ A) Σ -> G A Σ.

  (** Ghosts *)

  Parameter gname : ∀ (A : Type), Set.

  #[global] Declare Instance gname_inhabited A : Inhabited (gname A).
  #[global] Declare Instance gname_eq_dec A : EqDecision (gname A).
  #[global] Declare Instance gname_countable A : Countable (gname A).

  (** Predicates *)

  Parameter own : ∀ {A} {thread_info : biIndex} {Σ} `{!DFRAC_AGREE.G A Σ}
    (g : gname A) (q : Qp) (x : A), mpred.
  Parameter know : ∀ {A} {thread_info : biIndex} {Σ} `{!DFRAC_AGREE.G A Σ}
    (g : gname A) (x : A), mpred.

  Section properties.
    Context {A} {thread_info : biIndex} {Σ} `{!DFRAC_AGREE.G A Σ}.

    (** Structure *)

    #[global] Declare Instance own_objective : Objective3 own.
    #[global] Declare Instance own_frac g : FracSplittable_1 (own g).
    #[global] Declare Instance own_agree g : AgreeF1 (own g).

    #[global] Declare Instance know_objective : Objective2 know.
    #[global] Declare Instance know_timeless : Timeless2 know.
    #[global] Declare Instance know_knowledge : Knowledge2 know.
    #[global] Declare Instance know_agree g : Agree1 (know g).

    #[global] Declare Instance know_own_agree g q x1 x2 :
      Observe2 [| x1 = x2 |] (know g x1) (own g q x2).

    (** Allocation *)

    Axiom alloc_strong_dep : ∀ (f : gname A -> A) (P : gname A -> Prop),
      pred_infinite P ->
      |-- |==> Exists g, [| P g |] ** own g 1 (f g).

    Axiom alloc_cofinite_dep : ∀ (f : gname A -> A) (G : gset (gname A)),
      |-- |==> Exists g, [| g ∉ G |] ** own g 1 (f g).

    Axiom alloc_dep : ∀ (f : gname A -> A),
      |-- |==> Exists g, own g 1 (f g).

    Axiom alloc_strong : ∀ (P : gname A -> Prop) x,
      pred_infinite P ->
      |-- |==> Exists g, [| P g |] ** own g 1 x.

    Axiom alloc_cofinite : ∀ (G : gset (gname A)) x,
      |-- |==> Exists g, [| g ∉ G |] ** own g 1 x.

    Axiom alloc : ∀ x, |-- |==> Exists g, own g 1 x.

    (** Updates *)

    Axiom update : ∀ x g y, own g 1 y |-- |==> own g 1 x.

    Axiom discard : ∀ g q x, own g q x |-- |==> know g x.

  End properties.

End DFRAC_AGREE.

Module dfrac_agree : DFRAC_AGREE.

  (** CMRA *)

  #[local] Notation RA A := (dfrac_agreeR (leibnizO A)).
  Class G (A : Type) (Σ : gFunctors) : Set := G_inG : inG Σ (RA A).
  #[global] Existing Instance G_inG.
  Definition Σ (A : Type) : gFunctors := #[ GFunctor (RA A) ].
  Lemma subG {A Σ} : subG (dfrac_agree.Σ A) Σ -> G A Σ.
  Proof. solve_inG. Qed.

  (** Ghosts *)

  Definition gname (A : Type) : Set := iprop.gname.
  Definition gname_inhabited A : Inhabited (gname A) := _.
  Definition gname_eq_dec A : EqDecision (gname A) := _.
  Definition gname_countable A : Countable (gname A) := _.

  (** Predicates *)

  Section defs.
    Context {A} {thread_info : biIndex} {Σ} `{!dfrac_agree.G A Σ}.

    Definition know (g : gname A) (x : A) : mpred :=
      own g (to_dfrac_agree (A:=leibnizO A) DfracDiscarded x).
    Definition own (g : gname A) (q : Qp) (x : A) : mpred :=
      own g (to_dfrac_agree (A:=leibnizO A) (DfracOwn q) x).

    Definition own_objective : Objective3 own := _.
    Lemma own_frac g : FracSplittable_1 (own g).
    Proof.
      split.
      - intros x q1 q2. by rewrite -own_op -dfrac_agree_op.
      - apply _.
      - intros. iIntros "O".
        iDestruct (own_valid with "O") as %?%to_dfrac_agree_valid.
        auto.
    Qed.

    #[local] Ltac solve_agree :=
      intros; iIntros "O1 O2";
      iDestruct (own_valid_2 with "O1 O2") as %[_ ?]%dfrac_agree_op_valid_L;
      solve [ auto ].

    Lemma own_agree g : AgreeF1 (own g).
    Proof. solve_agree. Qed.

    Definition know_objective : Objective2 know := _.
    Definition know_timeless : Timeless2 know := _.
    Definition know_knowledge : Knowledge2 know.
    Proof. solve_knowledge. Qed.
    Lemma know_agree g : Agree1 (know g).
    Proof. solve_agree. Qed.

    Lemma know_own_agree g q x1 x2 :
      Observe2 [| x1 = x2 |] (know g x1) (own g q x2).
    Proof. solve_agree. Qed.

    Lemma alloc_strong_dep : ∀ (f : gname A -> A) (P : gname A -> Prop),
      pred_infinite P ->
      |-- |==> Exists g, [| P g |] ** own g 1 (f g).
    Proof. intros. by apply: own_alloc_strong_dep'. Qed.

    Lemma alloc_cofinite_dep : ∀ (f : gname A -> A) (G : gset (gname A)),
      |-- |==> Exists g, [| g ∉ G |] ** own g 1 (f g).
    Proof. intros. by apply: own_alloc_cofinite_dep'. Qed.

    Lemma alloc_dep : ∀ (f : gname A -> A),
      |-- |==> Exists g, own g 1 (f g).
    Proof. intros. by apply: own_alloc_dep. Qed.

    Lemma alloc_strong : ∀ (P : gname A -> Prop) x,
      pred_infinite P ->
      |-- |==> Exists g, [| P g |] ** own g 1 x.
    Proof. intros. by apply: own_alloc_strong'. Qed.

    Lemma alloc_cofinite : ∀ (G : gset (gname A)) x,
      |-- |==> Exists g, [| g ∉ G |] ** own g 1 x.
    Proof. intros. by apply: own_alloc_cofinite'. Qed.

    Lemma alloc x : |-- |==> Exists g, own g 1 x.
    Proof. by apply own_alloc. Qed.

    Lemma update x g y : own g 1 y |-- |==> own g 1 x.
    Proof. by apply own_update, cmra_update_exclusive. Qed.

    Lemma discard g q x : own g q x |-- |==> know g x.
    Proof. apply own_update, dfrac_agree_persist. Qed.
  End defs.

End dfrac_agree.
