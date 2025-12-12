(*
 * Copyright (c) 2020 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import elpi.apps.locker.locker.
Require Import bluerock.prelude.base.
Require Import iris.bi.bi.
Require Import iris.bi.monpred.
Require Import iris.bi.embedding.
Require Import iris.bi.lib.fractional.
Require Import bluerock.iris.extra.proofmode.proofmode.

(**
[only_provable P], written [ [| P |] ], is a variant of [⌜ P ⌝] that, in a
linear logic, cannot "absorb" any resources.

Hence, if [A ⊢ B ∗ [| P |] ], all resources owned by [A] are owned by [B],
and none are owned by [ [| P |] ].

See also [only_provable_equiv].

For an academic reference on the [<affine>] derived modality and the concept
of "absorbing" propositions, see
"MoSeL: A general, extensible modal framework for interactive proofs in separation logic"
(http://doi.acm.org/10.1145/3236772).
*)
mlock Definition only_provable {PROP : bi} (P : Prop) : PROP :=
  (<affine> ⌜P⌝)%I.
#[global] Arguments only_provable {_} _%_type_scope : simpl never, rename.
#[global] Instance: Params (@only_provable) 1 := {}.

Notation "[ | P | ]" := (only_provable P) (format "[ |  P  | ]").
(* TODO Fix scopes. *)
(* Notation "[ | P | ]" := (only_provable P%type%stdpp) (format "[ |  P  | ]"). *)

(* This class carries the assumptions of [only_provable_forall_2], but is very ad-hoc. *)
Class BiEmpForallOnlyProvable (PROP : bi) :=
  emp_forall_only_provable A φ : (∀ x : A, [| φ x |]) ⊢@{PROP} <affine> (∀ x : A, [| φ x |]).
#[global] Hint Mode BiEmpForallOnlyProvable + : typeclass_instances.

(** * Properties of [only_provable]. *)
Section bi.
  Context {PROP : bi} `{PF : BiPureForall PROP}.

  Implicit Types P Q : Prop.
  Implicit Types p q r : PROP.
  #[local] Notation "p ⊢ q" := (p ⊢@{PROP} q) (only parsing).
  #[local] Notation "p ⊣⊢ q" := (p ⊣⊢@{PROP} q) (only parsing).

  Lemma only_provable_unfold P : [| P |] ⊣⊢ <affine> ⌜ P ⌝.
  Proof. by rewrite only_provable.unlock. Qed.
  (** [ [| P |] ] indeed holds no resources. This is also an unfolding lemma, since [only_provable] is [Opaque]. *)
  Lemma only_provable_equiv P : [| P |] ⊣⊢ emp ∧ ⌜ P ⌝.
  Proof. apply only_provable_unfold. Qed.

  Lemma pure_absorb_only_provable (φ : Prop) : ⌜ φ ⌝ ⊣⊢@{PROP} <absorb> [| φ |].
  Proof. by rewrite only_provable_unfold bi.persistent_absorbingly_affinely. Qed.

  Lemma pure_True_only_provable (φ : Prop) : ⌜ φ ⌝ ⊣⊢@{PROP} True ∗ [| φ |].
  Proof. apply pure_absorb_only_provable. Qed.

  Lemma only_provable_pure φ : [| φ |] ⊢@{PROP} ⌜φ⌝.
  Proof. rewrite only_provable_unfold. by rewrite bi.affinely_elim. Qed.

  #[global] Instance only_provable_ne n :
    Proper (iff ==> dist n) (@only_provable PROP).
  Proof. rewrite only_provable.unlock. solve_proper. Qed.
  #[global] Instance only_provable_proper :
    Proper (iff ==> (⊣⊢)) (@only_provable PROP).
  Proof. rewrite only_provable.unlock. solve_proper. Qed.
  #[global] Instance only_provable_mono' :
    Proper (impl ==> (⊢)) (@only_provable PROP).
  Proof. rewrite only_provable.unlock. solve_proper. Qed.
  #[global] Instance only_provable_flip_mono :
    Proper (flip impl ==> flip (⊢)) (@only_provable PROP).
  Proof. solve_proper. Qed.

  #[global] Instance only_provable_persistent P : Persistent (PROP:=PROP) [| P |].
  Proof. rewrite only_provable_unfold. apply _. Qed.
  #[global] Instance only_provable_affine P : Affine (PROP:=PROP) [| P |].
  Proof. rewrite only_provable_unfold. apply _. Qed.
  #[global] Instance only_provable_timeless `{Timeless PROP emp} P :
    Timeless (PROP:=PROP) [| P |].
  Proof. rewrite only_provable_unfold. apply _. Qed.
  #[global] Instance only_provable_plain `{BiPlainly PROP} P :
    Plain (PROP:=PROP) [| P |].
  Proof. rewrite only_provable_unfold. apply _. Qed.

  (* This is provable, but only usable under `BiAffine`, hence misleading. *)
  Lemma only_provable_absorbing `{BiAffine PROP} P :
    Absorbing (PROP:=PROP) [| P |].
  Proof. apply _. Qed.

  Lemma only_provable_mono P Q : (P → Q) → [| P |] ⊢ [| Q |].
  Proof. apply only_provable_mono'. Qed.
  Lemma only_provable_iff P Q : (P ↔ Q) → [| P |] ⊣⊢ [| Q |].
  Proof. apply only_provable_proper. Qed.
  Lemma only_provable_intro P p `{!Affine p} : P → p ⊢ [| P |].
  Proof. rewrite only_provable_unfold. intros ?. apply: bi.affinely_intro. exact: bi.pure_intro. Qed.
  Lemma only_provable_elim' P p : (P → True ⊢ p) → [| P |] ⊢ p.
  Proof. rewrite only_provable_pure. apply bi.pure_elim'. Qed.
  Lemma only_provable_elim_l P q r : (P → q ⊢ r) → [| P |] ∧ q ⊢ r.
  Proof. rewrite only_provable_pure. apply bi.pure_elim_l. Qed.
  Lemma only_provable_elim_r P q r : (P → q ⊢ r) → q ∧ [| P |] ⊢ r.
  Proof. rewrite comm. apply only_provable_elim_l. Qed.
  Lemma only_provable_emp : [| True |] ⊣⊢ emp.
  Proof. by rewrite only_provable_unfold bi.affinely_True_emp. Qed.
  Lemma only_provable_True P : P → [| P |] ⊣⊢ emp.
  Proof. intros. by rewrite -only_provable_emp !only_provable_unfold bi.pure_True. Qed.
  Lemma only_provable_False P : ¬P → [| P |] ⊣⊢ False.
  Proof.
    intros. by rewrite only_provable_unfold bi.pure_False// bi.affinely_False.
  Qed.
  Lemma only_provable_True' : [| True |] ⊣⊢@{PROP} emp.
  Proof. by rewrite only_provable_True. Qed.
  Lemma only_provable_False' : [| False |] ⊣⊢@{PROP} False.
  Proof. rewrite only_provable_False; naive_solver. Qed.
  Lemma only_provable_sep P Q : [|P ∧ Q|] ⊣⊢ [| P |] ∗ [| Q |].
  Proof. rewrite !only_provable_unfold. apply (anti_symm _); auto. Qed.
  Lemma only_provable_and P Q : [|P ∧ Q|] ⊣⊢ [| P |] ∧ [| Q |].
  Proof. by rewrite !only_provable_unfold -bi.affinely_and -bi.pure_and. Qed.
  Lemma only_provable_or P Q : [|P ∨ Q|] ⊣⊢ [| P |] ∨ [| Q |].
  Proof. by rewrite !only_provable_unfold -bi.affinely_or -bi.pure_or. Qed.
  Lemma only_provable_impl P Q : [|P → Q|] ⊢ ([| P |] → [| Q |]).
  Proof. rewrite !only_provable_unfold. auto. Qed.
  Lemma only_provable_forall_1 {A} (φ : A → Prop) : [|∀ x, φ x|] ⊢ ∀ x, [|φ x|].
  Proof. setoid_rewrite only_provable_unfold. auto. Qed.

  (** Not very useful, but the best we can do in general:
  it's unclear how to commute [emp ∧ ∀ x : A, P] into [∀ x : A, emp ∧ P]. *)
  Lemma only_provable_forall_2_gen {A} (φ : A → Prop)
    `{Hswap : BiEmpForallOnlyProvable PROP} :
    (∀ x, [|φ x|]) ⊢@{PROP} [|∀ x, φ x|].
  Proof using PF.
    rewrite emp_forall_only_provable. setoid_rewrite only_provable_unfold.
    iIntros "!% /=". done.
  Qed.

  Lemma only_provable_forall_2_inhabited `{Inhabited A} (φ : A → Prop) :
    (∀ x, [|φ x|]) ⊢ [|∀ x, φ x|].
  Proof using PF.
    setoid_rewrite only_provable_unfold. rewrite /bi_affinely. iIntros "Hφ". iSplit; first done.
    rewrite bi.pure_forall. iIntros (x). iDestruct ("Hφ" $! x) as "[_ $]".
  Qed.
  Lemma only_provable_forall_2 {A} (φ : A → Prop)
    `{HTC : TCOrT (BiEmpForallOnlyProvable PROP) (Inhabited A)} :
    (∀ x, [|φ x|]) ⊢ [|∀ x, φ x|].
  Proof using PF. destruct HTC. apply: only_provable_forall_2_gen. apply: only_provable_forall_2_inhabited. Qed.
  Lemma only_provable_forall {A} (φ : A → Prop)
    `{HTC : TCOrT (BiEmpForallOnlyProvable PROP) (Inhabited A)} :
    [|∀ x, φ x|] ⊣⊢ ∀ x, [|φ x|].
  Proof using PF. apply: anti_symm. apply only_provable_forall_1. apply: only_provable_forall_2. Qed.

  #[global] Instance bi_affine_emp_forall_only_provable (HBA : BiAffine PROP) :
    BiEmpForallOnlyProvable PROP.
  Proof. iIntros (??) "$". Qed.

  Lemma only_provable_exist {A} (φ : A → Prop) : [|∃ x, φ x|] ⊣⊢ ∃ x, [|φ x|].
  Proof. setoid_rewrite only_provable_unfold. by rewrite bi.pure_exist bi.affinely_exist. Qed.
  Lemma only_provable_impl_forall P q : ([| P |] → q) ⊢ (∀ _ : P, emp → q).
  Proof. apply bi.forall_intro=>?. by rewrite only_provable_True. Qed.
  Lemma only_provable_alt P : [| P |] ⊣⊢ ∃ _ : P, emp.
  Proof.
    rewrite !only_provable_unfold bi.pure_alt bi.affinely_exist.
    do 2!f_equiv. exact: bi.affinely_True_emp.
  Qed.
  Lemma only_provable_wand_forall_1 P q : ([| P |] -∗ q) ⊢ (∀ _ : P, q).
  Proof.
    apply bi.forall_intro=>?. by rewrite only_provable_True// left_id.
  Qed.
  Lemma only_provable_wand_forall_2 P q :
    (∀ _ : P, q) ⊢ ([| P |] -∗ q).
  Proof. rewrite !only_provable_unfold. iIntros "W %HP". iApply ("W" $! HP). Qed.
  Lemma only_provable_wand_forall P q :
    ([| P |] -∗ q) ⊣⊢ (∀ _ : P, q).
  Proof.
    apply: anti_symm; auto using
      only_provable_wand_forall_1, only_provable_wand_forall_2.
  Qed.

  Lemma persistently_only_provable P : <pers> [| P |] ⊣⊢@{PROP} ⌜ P ⌝.
  Proof. by rewrite only_provable_unfold bi.persistently_affinely_elim bi.persistently_pure. Qed.
  Lemma affinely_only_provable P : <affine> [| P |] ⊣⊢@{PROP} [| P |].
  Proof. by rewrite only_provable_unfold bi.affinely_idemp. Qed.
  Lemma absorbingly_only_provable P : <absorb> [| P |] ⊣⊢@{PROP} ⌜ P ⌝.
  Proof. by rewrite only_provable_unfold bi.persistent_absorbingly_affinely. Qed.

  Lemma intuitionistically_only_provable P : □ [| P |] ⊣⊢@{PROP} [| P |].
  Proof. by rewrite /bi_intuitionistically !persistently_only_provable only_provable_unfold. Qed.

  Lemma intuitionistically_if_only_provable b P : □?b [| P |] ⊣⊢@{PROP} [| P |].
  Proof. destruct b => //=. apply intuitionistically_only_provable. Qed.

  Lemma pure_impl_only_provable_wand (φ : Prop) (Q : PROP) :
    (⌜ φ ⌝ → Q) ⊣⊢ ([| φ |] -∗ Q).
  Proof.
    rewrite -(bi.intuitionistic_intuitionistically [| φ |]).
    by rewrite -bi.impl_wand_intuitionistically persistently_only_provable.
  Qed.

  #[global] Instance only_provable_True_left_id :
    LeftId (≡@{PROP}) [| True |] bi_sep.
  Proof. intros P. by rewrite only_provable_emp left_id. Qed.
  #[global] Instance only_provable_True_right_id :
    RightId (≡@{PROP}) [| True |] bi_sep.
  Proof. intros P. by rewrite only_provable_emp right_id. Qed.
End bi.
#[global] Hint Resolve only_provable_intro : core.

(* TODO deduplicate *)
#[local] Instance Objective_proper {I PROP} :
  Proper ((≡) ==> (↔)) (@Objective I PROP).
Proof. intros ?? E; repeat (apply forall_proper; intro); by rewrite E. Qed.

Section monpred.
  Context {I : biIndex} {PROP : bi}.

  #[global] Instance only_provable_objective P : @Objective I PROP [| P |].
  Proof. rewrite only_provable_unfold. apply _. Qed.

  Lemma monPred_at_only_provable (i : I) P :
    monPred_at [| P |] i ⊣⊢@{PROP} [| P |].
  Proof. by rewrite !only_provable_unfold monPred_at_affinely monPred_at_pure. Qed.

  #[global] Instance monpred_bi_emp_forall_only_provable :
    BiEmpForallOnlyProvable PROP ->
    BiEmpForallOnlyProvable (monPredI I PROP).
  Proof.
    rewrite /BiEmpForallOnlyProvable => HPROP A φ. constructor=> i.
    rewrite monPred_at_and monPred_at_emp monPred_at_forall.
    setoid_rewrite monPred_at_only_provable.
    apply HPROP.
  Qed.
End monpred.

Lemma embed_only_provable `{BiEmbedEmp PROP1 PROP2} (P : Prop) :
  embed [| P |] ⊣⊢@{PROP2} [| P |].
Proof. by rewrite !only_provable_unfold embed_affinely embed_pure. Qed.

Section proofmode.
  Context {PROP : bi} {PF: BiPureForall PROP}.

  (**
   * We don't register instances
   *
   * - [@FromAffinely PROP [| P |] ⌜P⌝]
   *
   * - [@IntoAbsorbingly PROP ⌜P⌝ [| P |]]
   *
   * as they would interact poorly with, e.g., [iSplit], changing
   * goals like [[| P |] ** Q] into subgoals involving [bi_pure]
   * rather than [only_provable].
   *)
  #[global] Instance into_pure_only_provable P : @IntoPure PROP [| P |] P.
  Proof. apply only_provable_pure. Qed.
  #[global] Instance from_pure_only_provable P : @FromPure PROP true [| P |] P.
  Proof. by rewrite/FromPure only_provable_unfold. Qed.
  #[global] Instance into_wand_only_provable p q (P : Prop) Q :
    @IntoWand PROP p q (∀ _ : P, Q) [| P |] Q.
  Proof.
    rewrite /IntoWand.
    by rewrite !bi.intuitionistically_if_elim -only_provable_wand_forall_2.
  Qed.
  #[global] Instance from_and_only_provable P Q :
    @FromAnd PROP [| P ∧ Q |] [| P |] [| Q |].
  Proof. by rewrite/FromAnd only_provable_and. Qed.
  #[global] Instance into_and_only_provable p P Q :
    @IntoAnd PROP p [| P ∧ Q |] [| P |] [| Q |].
  Proof. by rewrite/IntoAnd only_provable_and. Qed.
  #[global] Instance from_sep_only_provable P Q :
    @FromSep PROP [| P ∧ Q |] [| P |] [| Q |].
  Proof. by rewrite/FromSep only_provable_sep. Qed.
  #[global] Instance into_sep_only_provable P Q :
    @IntoSep PROP [| P ∧ Q |] [| P |] [| Q |].
  Proof. by rewrite/IntoSep only_provable_sep. Qed.
  #[global] Instance from_or_only_provable P Q :
    @FromOr PROP [| P ∨ Q |] [| P |] [| Q |].
  Proof. by rewrite/FromOr only_provable_or. Qed.
  #[global] Instance into_or_only_provable P Q :
    @IntoOr PROP [| P ∨ Q |] [| P |] [| Q |].
  Proof. by rewrite/IntoOr only_provable_or. Qed.
  #[global] Instance from_exist_only_provable {A} (P : A → Prop) :
    @FromExist PROP A [| ∃ x, P x |] (λ a, [| P a |]).
  Proof. by rewrite/FromExist only_provable_exist. Qed.
  #[global] Instance into_exist_only_provable {A} (P : A → Prop) name :
    AsIdentName P name ->
    @IntoExist PROP A [| ∃ x, P x |] (λ a, [| P a |]) name.
  Proof. by rewrite/IntoExist only_provable_exist. Qed.

  (* TODO: avoid backtracking between these two instances by adding a TCOrT;
  TCOr does not work because it only takes Props but Inhabited is in Type. *)
  #[global] Instance from_forall_only_provable
      `{HTC : TCOrT (BiEmpForallOnlyProvable PROP) (Inhabited A)} (P : A → Prop) name :
    AsIdentName P name ->
    @FromForall PROP A [| ∀ x, P x |] (λ a, [| P a |]) name.
  Proof using PF.
    by rewrite/FromForall only_provable_forall_2.
  Qed.

  #[global] Instance into_forall_only_provable {A} (P : A → Prop) :
    @IntoForall PROP A [| ∀ x, P x |] (λ a, [| P a |]).
  Proof. by rewrite/IntoForall only_provable_forall_1. Qed.
End proofmode.
