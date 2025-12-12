(*
 * Copyright (C) 2021 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import iris.bi.embedding.
Require Import bluerock.iris.extra.bi.prelude.
Require Import bluerock.iris.extra.proofmode.proofmode.
Set Printing Coercions.

(** * Internal inclusion

Iris lacks the notion of inclusion within the logic: it only has Coq-level
inclusion [included] and [includedN], where the former holds at all
step indices and the latter holds at a specific step index.

TODO: upstream to Iris.
*)
Definition includedI `{!BiInternalEq PROP} {A : cmra} (a b : A) : PROP :=
  (∃ c : A, b ≡ a ⋅ c)%I.
#[global] Instance: Params (@includedI) 3 := {}.

Infix "≼" := includedI : bi_scope.
Notation "(≼)" := includedI (only parsing) : bi_scope.

Infix "≼@{ PROP }" := (includedI (PROP:=PROP)) (only parsing, at level 70) : bi_scope.
Notation "(≼@{ PROP } )" := (includedI (PROP:=PROP)) (only parsing) : bi_scope.

Section cmra.
  Context `{!BiInternalEq PROP} {A : cmra}.
  Implicit Types P : PROP.
  Implicit Types a b : A.
  Notation "P ⊣⊢ Q" := (P ⊣⊢@{PROP} Q).
  Notation "P ⊢ Q" := (P ⊢@{PROP} Q).
  Notation "a ≼ b" := (a ≼@{PROP} b)%I : bi_scope.
  Notation includedI := (includedI (PROP:=PROP) (A:=A)) (only parsing).

  #[global] Instance includedI_ne : NonExpansive2 includedI.
  Proof. solve_proper. Qed.
  #[global] Instance includedI_proper : Proper ((≡) ==> (≡) ==> (⊣⊢)) includedI.
  Proof. solve_proper. Qed.
  #[global] Instance includedI_mono : Proper ((≡) ==> (≡) ==> (⊢)) includedI.
  Proof. intros ?? HA ?? HB. rewrite /includedI. f_equiv=>c. by rewrite HA HB. Qed.
  #[global] Instance includedI_flip_mono : Proper ((≡) ==> (≡) --> (⊢)) includedI.
  Proof. repeat intro. exact: includedI_mono. Qed.

  (** Note: If this winds up being heavily used, it might be nice to
      switch to [includedI a b := <affine> ...], dropping this
      absorbing instance, adding an affine instance, and weakening the
      timeless instance to affine BIs. The point is that [work]
      doesn't know about aborbing, persistent things. (The definition
      as it stands is most likely to match upstream theory.) *)
  #[global] Instance includedI_absorbing a b : Absorbing (a ≼ b).
  Proof. apply _. Qed.
  #[global] Instance includedI_persistent a b : Persistent (a ≼ b).
  Proof. apply _. Qed.
  #[global] Instance includedI_timeless a b : Discrete b → Timeless (a ≼ b).
  Proof. apply _. Qed.

  Lemma includedI_unfold a b : a ≼ b ⊣⊢ ∃ c : A, b ≡ a ⋅ c.
  Proof. done. Qed.

  Lemma includedI_trans a b c : a ≼ b ⊢ b ≼ c -∗ a ≼ c.
  Proof.
    iDestruct 1 as (b') "B". iDestruct 1 as (c') "C". iExists (b' ⋅ c').
    rewrite assoc. iRewrite "C". by iRewrite "B".
  Qed.

  (** See also [discrete_includedI_r]. *)
  Lemma discrete_includedI a b : Discrete b → a ≼ b ⊣⊢ [! a ≼ b !].
  Proof.
    split'; iDestruct 1 as (c) "%".
    - iPureIntro. by exists c.
    - by iExists c.
  Qed.

  (** Proof mode --- it's going to become TC opaque *)
  #[global] Instance into_exist_includedI a b :
    IntoExist (a ≼ b) (λ c, b ≡ a ⋅ c)%I (λ x, x) := _.
  #[global] Instance from_exist_includedI a b :
    FromExist (a ≼ b) (λ c, b ≡ a ⋅ c)%I := _.

  #[global] Instance into_pure_includedI a b :
    Discrete b → IntoPure (a ≼ b) (a ≼ b) := _.
  #[global] Instance from_pure_includedI a b :
    FromPure false (a ≼ b) (a ≼ b) := _.

End cmra.

Section ucmra.
  Context `{!BiInternalEq PROP} {A : ucmra}.
  Implicit Types P : PROP.
  Implicit Types a : A.

  Lemma includedI_refl P a : P ⊢ a ≼ a.
  Proof.
    rewrite (internal_eq_refl P a) /includedI.
    by rewrite -(bi.exist_intro ε) right_id.
  Qed.

  Lemma includedI_True a : a ≼ a ⊣⊢@{PROP} True.
  Proof. split'; auto using includedI_refl. Qed.
End ucmra.

#[global] Instance includedI_plain `{!BiInternalEq PROP, !BiPlainly PROP} {A : cmra}
    (a b : A) :
  Plain (a ≼@{PROP} b).
Proof. apply _. Qed.

Lemma embed_includedI `{BiEmbedInternalEq PROP1 PROP2} {A : cmra} (a b : A) :
  embed (a ≼ b) ⊣⊢@{PROP2} a ≼ b.
Proof. rewrite embed_exist. by setoid_rewrite embed_internal_eq. Qed.

#[global] Hint Opaque includedI : br_opacity typeclass_instances.

(** Help out IPM proofs. *)
#[global] Hint Extern 0 (environments.envs_entails _ (_ ≼ _)) =>
  rewrite environments.envs_entails_unseal; apply includedI_refl : core.
