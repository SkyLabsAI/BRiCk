(*
 * Copyright (C) 2021 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import iris.bi.embedding.
Require Import skylabs.iris.extra.bi.prelude.
Require Import skylabs.iris.extra.proofmode.proofmode.
Set Printing Coercions.

(** * Internal inclusion

Iris lacks the notion of inclusion within the logic: it only has Coq-level
inclusion [included] and [includedN], where the former holds at all
step indices and the latter holds at a specific step index.

TODO: upstream to Iris.
*)
Notation includedI := internal_included (only parsing).

Infix "≼@{ PROP }" := (includedI (PROP:=PROP)) (only parsing, at level 70) : bi_scope.
Notation "(≼@{ PROP } )" := (includedI (PROP:=PROP)) (only parsing) : bi_scope.

Section cmra.
  Context `{!Sbi PROP} {A : cmra}.
  Implicit Types P : PROP.
  Implicit Types a b : A.
  Notation "P ⊣⊢ Q" := (P ⊣⊢@{PROP} Q).
  Notation "P ⊢ Q" := (P ⊢@{PROP} Q).
  Notation "a ≼ b" := (a ≼@{PROP} b)%I : bi_scope.
  Notation includedI := (includedI (PROP:=PROP) (A:=A)) (only parsing).

  (** Note: If this winds up being heavily used, it might be nice to
      switch to [includedI a b := <affine> ...], dropping this
      absorbing instance, adding an affine instance, and weakening the
      timeless instance to affine BIs. The point is that [work]
      doesn't know about aborbing, persistent things. (The definition
      as it stands is most likely to match upstream theory.) *)

  Lemma includedI_unfold a b : a ≼ b ⊣⊢ ∃ c : A, b ≡ a ⋅ c.
  Proof. done. Qed.

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
  Context `{!Sbi PROP} {A : ucmra}.
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

#[global] Instance includedI_plain `{!Sbi PROP} {A : cmra}
    (a b : A) :
  Plain (a ≼@{PROP} b).
Proof. apply _. Qed.

Lemma si_pure_internal_included `{!Sbi PROP} {A : cmra} (a b : A) :
  <si_pure> (a ≼ b) ⊣⊢@{PROP} a ≼ b.
Proof. by rewrite /internal_included si_pure_exist. Qed.

Lemma embed_includedI `{!BiEmbed PROP1 PROP2, !Sbi PROP1, !Sbi PROP2,
    !BiEmbedSbi PROP1 PROP2} {A : cmra} (a b : A) :
  embed (a ≼ b) ⊣⊢@{PROP2} a ≼ b.
Proof. rewrite embed_exist. by setoid_rewrite embed_internal_eq. Qed.

#[global] Hint Opaque includedI : sl_opacity typeclass_instances.

(** Help out IPM proofs. *)
#[global] Hint Extern 0 (environments.envs_entails _ (_ ≼ _)) =>
  rewrite environments.envs_entails_unseal; apply includedI_refl : core.
