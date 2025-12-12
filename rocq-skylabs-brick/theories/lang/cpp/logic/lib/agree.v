(**
 * Copyright (C) 2022 BlueRock Security, Inc.
 * All rights reserved.
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)

Require Import iris.algebra.agree.
Require Import bluerock.iris.extra.bi.spec.knowledge.
Require Import bluerock.lang.cpp.logic.pred.
Require Import bluerock.iris.extra.base_logic.own_instances.
Require Import bluerock.iris.extra.proofmode.own_obs.

Set Printing Coercions.

(**
Well-typed ghost resources:

- [agree.own (g : agree.gname A) (x : A) : mpred]
represents knowledge of ghost cell [g] currently containing [x]

*)
Module Type AGREE.

  (** CMRA *)

  Parameter G : ∀ (A : Type) (Σ : gFunctors), Set.
  Existing Class G.
  Parameter Σ : ∀ (A : Type), gFunctors.
  #[global] Declare Instance subG {A Σ} : subG (AGREE.Σ A) Σ -> G A Σ.

  (** Ghosts *)

  Parameter gname : ∀ (A : Type), Set.

  #[global] Declare Instance gname_inhabited A : Inhabited (gname A).
  #[global] Declare Instance gname_eq_dec A : EqDecision (gname A).
  #[global] Declare Instance gname_countable A : Countable (gname A).

  (** Predicates *)

  Parameter own : ∀ {A} {thread_info : biIndex} {Σ} `{!AGREE.G A Σ}
    (g : gname A) (x : A), mpred.

  Section properties.
    Context {A} {thread_info : biIndex} {Σ} `{!AGREE.G A Σ}.

    (** Structure *)

    #[global] Declare Instance own_objective : Objective2 own.
    #[global] Declare Instance own_timeless : Timeless2 own.
    #[global] Declare Instance own_knowledge : Knowledge2 own.
    #[global] Declare Instance own_agree g : Agree1 (own g).

    (** Allocation *)

    Axiom alloc_strong_dep : ∀ (f : gname A -> A) (P : gname A -> Prop),
      pred_infinite P ->
      |-- |==> Exists g, [| P g |] ** own g (f g).

    Axiom alloc_cofinite_dep : ∀ (f : gname A -> A) (G : gset (gname A)),
      |-- |==> Exists g, [| g ∉ G |] ** own g (f g).

    Axiom alloc_dep : ∀ (f : gname A -> A),
      |-- |==> Exists g, own g (f g).

    Axiom alloc_strong : ∀ (P : gname A -> Prop) x,
      pred_infinite P ->
      |-- |==> Exists g, [| P g |] ** own g x.

    Axiom alloc_cofinite : ∀ (G : gset (gname A)) x,
      |-- |==> Exists g, [| g ∉ G |] ** own g x.

    Axiom alloc : ∀ x, |-- |==> Exists g, own g x.

    (** TODO: Automation (generically derivable) *)

  End properties.

End AGREE.

Module agree : AGREE.

  (** CMRA *)

  #[local] Notation RA A := (agreeR (leibnizO A)).
  Class G (A : Type) (Σ : gFunctors) : Set := G_inG : inG Σ (RA A).
  #[global] Existing Instance G_inG.
  Definition Σ (A : Type) : gFunctors := #[ GFunctor (RA A) ].
  Lemma subG {A Σ} : subG (agree.Σ A) Σ -> G A Σ.
  Proof. solve_inG. Qed.

  (** Ghosts *)

  Definition gname (A : Type) : Set := iprop.gname.
  #[local] Instance gname_inhabited A : Inhabited (gname A) := _.
  #[local] Instance gname_eq_dec A : EqDecision (gname A) := _.
  #[local] Instance gname_countable A : Countable (gname A) := _.

  (** Predicates *)

  Section defs.
    Context {A} {thread_info : biIndex} {Σ} `{!agree.G A Σ}.

    #[local] Notation to_agree := (to_agree (A:=leibnizO A)).

    Definition own (g : gname A) (x : A) : mpred :=
      own g (to_agree x).

    #[local] Instance own_objective : Objective2 own := _.
    #[local] Instance own_timeless : Timeless2 own := _.
    #[local] Instance own_knowledge : Knowledge2 own.
    Proof. solve_knowledge. Qed.
    #[local] Instance own_agree g : Agree1 (own g).
    Proof.
      (**
      TODO (PDS): Shouldn't need to expose [to_agree].
      *)
      intros. rewrite -(inj_iff to_agree). apply _.
    Qed.

    Lemma alloc_strong_dep : ∀ (f : gname A -> A) (P : gname A -> Prop),
      pred_infinite P ->
      |-- |==> Exists g, [| P g |] ** own g (f g).
    Proof. intros. by apply: own_alloc_strong_dep'. Qed.

    Lemma alloc_cofinite_dep : ∀ (f : gname A -> A) (G : gset (gname A)),
      |-- |==> Exists g, [| g ∉ G |] ** own g (f g).
    Proof. intros. by apply: own_alloc_cofinite_dep'. Qed.

    Lemma alloc_dep : ∀ (f : gname A -> A),
      |-- |==> Exists g, own g (f g).
    Proof. intros. by apply: own_alloc_dep. Qed.

    Lemma alloc_strong : ∀ (P : gname A -> Prop) x,
      pred_infinite P ->
      |-- |==> Exists g, [| P g |] ** own g x.
    Proof. intros. by apply: own_alloc_strong'. Qed.

    Lemma alloc_cofinite : ∀ (G : gset (gname A)) x,
      |-- |==> Exists g, [| g ∉ G |] ** own g x.
    Proof. intros. by apply: own_alloc_cofinite'. Qed.

    Lemma alloc x : |-- |==> Exists g, own g x.
    Proof. by apply own_alloc. Qed.
  End defs.

End agree.
