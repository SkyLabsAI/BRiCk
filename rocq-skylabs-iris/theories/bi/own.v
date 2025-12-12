(*
 * Copyright (c) 2020 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *
 * This file is derived from code original to the Iris project. That
 * original code is
 *
 *	Copyright Iris developers and contributors
 *
 * and used according to the following license.
 *
 *	SPDX-License-Identifier: BSD-3-Clause
 *
 * Original Code:
 * https://gitlab.mpi-sws.org/iris/iris/-/blob/5bb93f57729a8cc7d0ffeaab769cd24728e51a38/iris/base_logic/lib/own.v
 *
 * Original Iris License:
 * https://gitlab.mpi-sws.org/iris/iris/-/blob/5bb93f57729a8cc7d0ffeaab769cd24728e51a38/LICENSE-CODE
 *)

(** Extraction of own that doesn't depend on iProp.
  Most proofs in this file generalize those of Iris (see the link above).
  In many cases, the proofs are unchanged and are exact duplicates of those in
  Iris. But their types do change and become more general.

  TODO: These should be upstreamed to Iris's code base. **)

Require bluerock.prelude.tactics.base_dbs.
Require Export bluerock.iris.extra.si_logic.bi.

Require Import iris.algebra.proofmode_classes.
Require Import iris.proofmode.classes.

Require Import iris.base_logic.lib.iprop. (* << for [gname] only *)

#[local] Set Default Proof Using "Type*".

(* Step-indexed Validity *)
Program Definition si_cmra_valid_def {A : cmra} (a : A) : siProp :=
  {| siProp_holds n := ✓{n} a |}.
Solve Obligations with naive_solver eauto using cmra_validN_le.
#[local] Definition si_cmra_valid_aux : seal (@si_cmra_valid_def). Proof. by eexists. Qed.
Definition si_cmra_valid {A} := si_cmra_valid_aux.(unseal) A.
Definition si_cmra_valid_eq :
  @si_cmra_valid = @si_cmra_valid_def := si_cmra_valid_aux.(seal_eq).

(* Validity for arbitrary PROP, assuming an embedding of siProp.
  This subsumes uPred_cmra_valid. *)
Definition bi_cmra_valid
  {PROP : bi} `{!BiEmbed siPropI PROP} {A : cmra} (a : A) : PROP :=
  embed (si_cmra_valid a).

(* TODO: figure out if overwriting Iris's notation for [uPred_cmra_valid] works robustly, until this is upstreamed. *)
Notation "✓ x" := (bi_cmra_valid x) (at level 20) : bi_scope.

#[global] Instance prop_valid_plain
  {PROP : bi} `{!BiEmbed siPropI PROP} `{BiPlainly PROP}
  {BEP : BiEmbedPlainly siPropI PROP} {A : cmra} (a : A) :
  Plain (✓ a) := _.

#[global] Instance prop_valid_persistent
  {PROP : bi} `{!BiEmbed siPropI PROP} {A : cmra} (a : A) :
  Persistent (✓ a) := _.

Lemma validI_unfold `{BiEmbed siPropI PROP} {A : cmra} (a : A) :
  ✓ a ⊣⊢ embed (si_cmra_valid a).
Proof. done. Qed.

#[global] Hint Opaque bi_cmra_valid : typeclass_instances.
(** Mark it TC opaque; otherwise, TC resolution can prove anew, e.g.,
[Persistent (✓ a)] and tactics like [iDestruct (own_valid_2 with "A
B") as "#Hv"] produce [embed (si_cmra_valid (a ⋅ b))] rather than [✓
(a ⋅ b)]. (We might also wind up wanting "simpl never".) *)

(* own *)
Class HasOwn {PROP : bi} {A : cmra} : Type := {
  own           : gname → A → PROP ;
  own_op        : ∀ γ (a b : A), own γ (a ⋅ b) ⊣⊢ own γ a ∗ own γ b ;
  #[global]
  own_mono      :: ∀ γ, Proper (flip (≼) ==> (⊢)) (own γ) ;
  #[global]
  own_ne        :: ∀ γ, NonExpansive (own γ) ;
  #[global]
  own_timeless  :: ∀ γ (a : A), Discrete a → Timeless (own γ a) ;
  #[global]
  own_core_persistent :: ∀ γ a, CoreId a → Persistent (own γ a)
}.

Arguments HasOwn : clear implicits.
Arguments own {_ _ _} _ _.
#[global] Hint Opaque own : br_opacity.

#[global] Instance : Params (@own) 4 := {}.

#[global] Instance own_proper `{!HasOwn PROP A} γ :
  Proper ((≡) ==> (⊣⊢)) (@own PROP A _ γ) := ne_proper _.

(* own_valid *)
Class HasOwnValid `{!BiEmbed siPropI PROP} `{!HasOwn PROP A} : Prop := {
  own_valid : ∀ γ (a : A), own γ a ⊢ ✓ a
}.
Arguments HasOwnValid _ {_} _{_}.

(* own_update and own_alloc *)
Class HasOwnUpd `{!BiBUpd PROP} `{!HasOwn PROP A} : Prop := {
  own_updateP P γ (a : A) : a ~~>: P → own γ a ⊢ |==> ∃ a', <affine> ⌜P a'⌝ ∗ own γ a';
  own_alloc_strong_dep (f : gname → A) (P : gname → Prop) :
    pred_infinite P → (∀ γ, P γ → ✓ (f γ)) → ⊢ |==> ∃ γ, <affine> ⌜P γ⌝ ∗ own γ (f γ)
}.
Arguments HasOwnUpd _ {_} _ {_}.

Class HasOwnUnit `{!BiBUpd PROP} {A : ucmra} `{!HasOwn PROP A} : Prop := {
  own_unit γ : ⊢ |==> own γ (ε:A)
}.
Arguments HasOwnUnit _ {_} _ {_}.

Section valid.
  Context `{BE: !BiEmbed siPropI PROP} {A : cmra}.
  Implicit Type (a : A) (P : PROP).

  Local Arguments siProp_holds !_ _ /.

  Local Ltac unseal :=
    constructor => n /=;
      rewrite /bi_pure /bi_and /bi_forall /= si_cmra_valid_eq
              ?siprop.siProp_pure_unseal ?siprop.siProp_and_unseal
              ?siprop.siProp_forall_unseal /=.

  (* Duplicates from Iris's base_logic.upred, but more general. *)
  (* TODO: need more lemmas for valid *)
  Lemma cmra_valid_intro P (a : A) : ✓ a → P ⊢ ✓ a.
  Proof.
    intros VL.
    (* stupid proof that relies on embedding *)
    rewrite (bi.True_intro P) -embed_pure. apply embed_mono.
    unseal => ?. by apply cmra_valid_validN.
  Qed.
  Lemma cmra_valid_elim (a : A) : ¬ ✓{0} a → ✓ a ⊢ False.
  Proof.
    intros NVL. rewrite -embed_pure. apply embed_mono.
    unseal => ?. apply NVL. apply cmra_validN_le with n; auto. cbn; lia.
  Qed.
  Lemma plainly_cmra_valid_1 `{!BiPlainly PROP} `{!@BiEmbedPlainly siPropI PROP BE _ _}
    (a : A) : ✓ a ⊢ ■ ✓ a.
  Proof. by rewrite -embed_plainly. Qed.
  Lemma cmra_valid_weaken (a b : A) : ✓ (a ⋅ b) ⊢ ✓ a.
  Proof. apply embed_mono. unseal. apply cmra_validN_op_l. Qed.

  Lemma prod_validI {B : cmra} (x : A * B) : ✓ x ⊣⊢ ✓ x.1 ∧ ✓ x.2.
  Proof. rewrite -embed_and. apply embed_proper. by unseal. Qed.
  Lemma option_validI (mx : option A) :
    ✓ mx ⊣⊢ match mx with Some x => ✓ x | None => True end.
  Proof. destruct mx; [|rewrite -embed_pure]; apply embed_proper; by unseal. Qed.

  Lemma discrete_valid `{!CmraDiscrete A} (a : A) : ✓ a ⊣⊢ ⌜✓ a⌝.
  Proof.
    rewrite -embed_pure. apply embed_proper. unseal.
    by rewrite -cmra_discrete_valid_iff.
  Qed.

  Lemma discrete_fun_validI {B : A → ucmra} (g : discrete_fun B) : ✓ g ⊣⊢ ∀ i, ✓ g i.
  Proof. rewrite -embed_forall. apply embed_proper. by unseal. Qed.

  (* Duplicates from base_logic.proofmode *)
  Global Instance into_pure_cmra_valid `{!CmraDiscrete A} (a : A) :
    IntoPure (✓ a) (✓ a).
  Proof. by rewrite /IntoPure discrete_valid. Qed.

  Global Instance from_pure_cmra_valid (a : A) :
    FromPure false (✓ a) (✓ a).
  Proof.
    rewrite /FromPure /=. eapply bi.pure_elim=> // ?.
    rewrite -cmra_valid_intro //.
  Qed.
End valid.

Import bi.

Section own_valid.
  Context `{!BiEmbed siPropI PROP} `{!HasOwn PROP A} `{!HasOwnValid PROP A}.
  Implicit Type (a : A) (P : PROP).

  (* Duplicates from base_logic.lib.own *)
  Lemma own_valid_2 γ a1 a2 : own γ a1 ⊢ own γ a2 -∗ ✓ (a1 ⋅ a2).
  Proof. apply wand_intro_r. by rewrite -own_op own_valid. Qed.
  Lemma own_valid_3 γ a1 a2 a3 :
    own γ a1 ⊢ own γ a2 -∗ own γ a3 -∗ ✓ (a1 ⋅ a2 ⋅ a3).
  Proof. do 2 apply wand_intro_r. by rewrite -!own_op own_valid. Qed.
  Lemma own_valid_r γ a : own γ a ⊢ own γ a ∗ ✓ a.
  Proof. apply: bi.persistent_entails_r. apply own_valid. Qed.
  Lemma own_valid_l γ a : own γ a ⊢ ✓ a ∗ own γ a.
  Proof. by rewrite comm -own_valid_r. Qed.

End own_valid.

Import iris.bi.derived_laws.bi.
Require Import bluerock.iris.extra.proofmode.proofmode.

Section update.
  Context `{!BiBUpd PROP} `{!HasOwn PROP A} `{!HasOwnUpd PROP A}.
  Implicit Type (a : A).

  (* Duplicates from base_logic.lib.own. *)
  Lemma own_update γ a a' : a ~~> a' → own γ a ⊢ |==> own γ a'.
  Proof.
    intros. iIntros "?".
    iMod (own_updateP (a' =.) with "[$]") as (a'') "[-> $]".
    { by apply cmra_update_updateP. }
    done.
  Qed.

  Lemma own_alloc_cofinite_dep (f : gname → A) (G : gset gname) :
    (∀ γ, γ ∉ G → ✓ (f γ)) → ⊢ |==> ∃ γ, <affine> ⌜γ ∉ G⌝ ∗ own γ (f γ).
  Proof.
    intros Ha.
    apply (own_alloc_strong_dep f (λ γ, γ ∉ G))=> //.
    apply (pred_infinite_set (C:=gset gname)).
    intros E. set (i := fresh (G ∪ E)).
    exists i. apply not_elem_of_union, is_fresh.
  Qed.
  Lemma own_alloc_dep (f : gname → A) :
    (∀ γ, ✓ (f γ)) → ⊢ |==> ∃ γ, own γ (f γ).
  Proof.
    intros Ha. rewrite /bi_emp_valid (own_alloc_cofinite_dep f ∅) //; [].
    apply bupd_mono, exist_mono=>?. apply: sep_elim_r.
  Qed.

  Lemma own_alloc_strong a (P : gname → Prop) :
    pred_infinite P →
    ✓ a → ⊢ |==> ∃ γ, <affine> ⌜P γ⌝ ∗ own γ a.
  Proof. intros HP Ha. eapply own_alloc_strong_dep with (f := λ _, a); eauto. Qed.
  Lemma own_alloc_cofinite a (G : gset gname) :
    ✓ a → ⊢ |==> ∃ γ, <affine> ⌜γ ∉ G⌝ ∗ own γ a.
  Proof. intros Ha. eapply own_alloc_cofinite_dep with (f := λ _, a); eauto. Qed.
  Lemma own_alloc a : ✓ a → ⊢ |==> ∃ γ, own γ a.
  Proof. intros Ha. eapply own_alloc_dep with (f := λ _, a); eauto. Qed.

  Lemma own_update_2 γ a1 a2 a' :
    a1 ⋅ a2 ~~> a' → own γ a1 ⊢ own γ a2 ==∗ own γ a'.
  Proof. intros. apply wand_intro_r. rewrite -own_op. by apply own_update. Qed.
  Lemma own_update_3 γ a1 a2 a3 a' :
    a1 ⋅ a2 ⋅ a3 ~~> a' → own γ a1 ⊢ own γ a2 -∗ own γ a3 ==∗ own γ a'.
  Proof. intros. do 2 apply wand_intro_r. rewrite -!own_op. by apply own_update. Qed.
End update.

(** Big op class instances *)
Section big_op_instances.
  Context `{!BiBUpd PROP} {A : ucmra}.
  Context `{!HasOwn PROP A} `{!HasOwnUnit PROP A}.

  Global Instance own_cmra_sep_homomorphism γ :
    WeakMonoidHomomorphism op bi_sep (≡) (own γ).
  Proof. split; try apply _. apply own_op. Qed.

  Lemma big_opL_own {B} γ (f : nat → B → A) (l : list B) :
    l ≠ [] →
    own γ ([^op list] k↦x ∈ l, f k x) ⊣⊢ [∗ list] k↦x ∈ l, own γ (f k x).
  Proof. apply (big_opL_commute1 _). Qed.
  Lemma big_opM_own `{Countable K} {B} γ (g : K → B → A) (m : gmap K B) :
    m ≠ ∅ →
    own γ ([^op map] k↦x ∈ m, g k x) ⊣⊢ [∗ map] k↦x ∈ m, own γ (g k x).
  Proof. apply (big_opM_commute1 _). Qed.
  Lemma big_opS_own `{Countable B} γ (g : B → A) (X : gset B) :
    X ≠ ∅ →
    own γ ([^op set] x ∈ X, g x) ⊣⊢ [∗ set] x ∈ X, own γ (g x).
  Proof. apply (big_opS_commute1 _). Qed.
  Lemma big_opMS_own `{Countable B} γ (g : B → A) (X : gmultiset B) :
    X ≠ ∅ →
    own γ ([^op mset] x ∈ X, g x) ⊣⊢ [∗ mset] x ∈ X, own γ (g x).
  Proof. apply (big_opMS_commute1 _). Qed.

  Section affine.
    Context `{!∀ γ, Affine (own γ ε)}.
    Global Instance own_cmra_sep_entails_homomorphism γ :
      MonoidHomomorphism op bi_sep (⊢) (own γ).
    Proof.
      split; [split|]; try apply _.
      - intros. by rewrite own_op.
      - apply (affine _).
    Qed.

    Lemma big_opL_own_1 {B} γ (f : nat → B → A) (l : list B) :
      own γ ([^op list] k↦x ∈ l, f k x) ⊢ [∗ list] k↦x ∈ l, own γ (f k x).
    Proof. apply (big_opL_commute _). Qed.
    Lemma big_opM_own_1 `{Countable K, B} γ (g : K → B → A) (m : gmap K B) :
      own γ ([^op map] k↦x ∈ m, g k x) ⊢ [∗ map] k↦x ∈ m, own γ (g k x).
    Proof. apply (big_opM_commute _). Qed.
    Lemma big_opS_own_1 `{Countable B} γ (g : B → A) (X : gset B) :
      own γ ([^op set] x ∈ X, g x) ⊢ [∗ set] x ∈ X, own γ (g x).
    Proof. apply (big_opS_commute _). Qed.
    Lemma big_opMS_own_1 `{Countable B} γ (g : B → A) (X : gmultiset B) :
      own γ ([^op mset] x ∈ X, g x) ⊢ [∗ mset] x ∈ X, own γ (g x).
    Proof. apply (big_opMS_commute _). Qed.
  End affine.
End big_op_instances.

(** Proofmode class instances *)
Section proofmode_instances.
  Context `{!HasOwn PROP A}.
  Implicit Types a b : A.

  Global Instance into_sep_own γ a b1 b2 :
    IsOp a b1 b2 → IntoSep (own γ a) (own γ b1) (own γ b2).
  Proof. intros. by rewrite /IntoSep (is_op a) own_op. Qed.
  Global Instance into_and_own `{!BiAffine PROP} p γ a b1 b2 :
    IsOp a b1 b2 → IntoAnd p (own γ a) (own γ b1) (own γ b2).
  Proof. intros. by rewrite /IntoAnd (is_op a) own_op sep_and. Qed.

  Global Instance from_sep_own γ a b1 b2 :
    IsOp a b1 b2 → FromSep (own γ a) (own γ b1) (own γ b2).
  Proof. intros. by rewrite /FromSep -own_op -is_op. Qed.
  Global Instance combine_sep_own γ a b1 b2 :
    IsOp a b1 b2 → CombineSepAs (own γ b1) (own γ b2) (own γ a).
  Proof. intros. by rewrite /CombineSepAs -own_op -is_op. Qed.
  Global Instance from_and_own_persistent `{!BiAffine PROP} γ a b1 b2 :
    IsOp a b1 b2 → TCOr (CoreId b1) (CoreId b2) →
    FromAnd (own γ a) (own γ b1) (own γ b2).
  Proof.
    intros ? Hb. rewrite /FromAnd (is_op a) own_op.
    destruct Hb; by rewrite persistent_and_sep.
  Qed.
End proofmode_instances.

Require Import bluerock.iris.extra.bi.only_provable.

Section update_only_provable.
  Context `{!BiBUpd PROP} `{!HasOwn PROP A} `{!HasOwnUpd PROP A}.
  Implicit Type (a : A).

  Lemma own_alloc_strong_dep' (f : gname → A) (P : gname → Prop) :
    pred_infinite P → (∀ γ, P γ → ✓ (f γ)) → ⊢ |==> ∃ γ, [| P γ |] ∗ own γ (f γ).
  Proof. rewrite only_provable.unlock. apply own_alloc_strong_dep. Qed.

  Lemma own_alloc_cofinite_dep' (f : gname → A) (G : gset gname) :
    (∀ γ, γ ∉ G → ✓ (f γ)) → ⊢ |==> ∃ γ, [| γ ∉ G |] ∗ own γ (f γ).
  Proof. rewrite only_provable.unlock. apply own_alloc_cofinite_dep. Qed.

  Lemma own_alloc_strong' a (P : gname → Prop) :
    pred_infinite P →
    ✓ a → ⊢ |==> ∃ γ, [| P γ |] ∗ own γ a.
  Proof. rewrite only_provable.unlock. apply own_alloc_strong. Qed.
  Lemma own_alloc_cofinite' a (G : gset gname) :
    ✓ a → ⊢ |==> ∃ γ, [| γ ∉ G |] ∗ own γ a.
  Proof. rewrite only_provable.unlock. apply own_alloc_cofinite. Qed.
End update_only_provable.
