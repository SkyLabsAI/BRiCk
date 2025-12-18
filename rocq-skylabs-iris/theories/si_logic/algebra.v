(*
 * Copyright (C) 2021 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import stdpp.finite.
Require Import iris.algebra.dfrac.
Require Import iris.algebra.lib.gmap_view.
Require Import skylabs.prelude.base.
Require Import skylabs.iris.extra.algebra.excl_auth.
Require Import skylabs.iris.extra.algebra.frac_auth.
Require Import skylabs.iris.extra.algebra.dfrac_agree.
Require Import skylabs.iris.extra.bi.prelude.
Require Import skylabs.iris.extra.si_logic.bi.
Require Import skylabs.iris.extra.bi.own.
Require Import skylabs.iris.extra.bi.includedI.
Require Import skylabs.iris.extra.bi.embedding.
Require Import skylabs.iris.extra.proofmode.proofmode.
Set Printing Coercions.

Implicit Types (p q : Qp) (dp dq : dfrac).

(** * Internal properties of CMRAs *)
(** We generalize [iris.base_logic.algebra] from [uPred] to arbitrary
BIs that embed [siProp], lifting properties of CMRA validity,
equality, and inclusion into the logic.

We don't attempt to cover all CMRAs, but we aim to be exhaustive for
those we do cover.

As Hai's work lands upstream, most lemmas here will be superseded by
upstream versions, and can then be dropped.

Upstream issue: https://gitlab.mpi-sws.org/iris/iris/-/issues/420 *)

(** Helpers to ease the lifting of meta-level implications. *)
Section plain_wand.
  Context `{BiPlainly PROP}.
  Implicit Types P Q : PROP.

  #[local] Lemma plain_wand_intro_r P Q R `{!Plain P, !Plain Q} :
    (P ∧ Q ⊢ R) → (P ⊢ Q -∗ <pers> R).
  Proof.
    intros HR. rewrite (plain P) (plain Q). apply bi.wand_intro_r.
    rewrite -and_sep_plainly -plainly_and. rewrite HR.
    by rewrite plainly_elim_persistently.
  Qed.
  #[local] Lemma plain_wand_intro_pure_r P Q R `{!Plain P, !Plain Q} :
    (P ∧ Q ⊢ [! R !]) → (P ⊢ Q -∗ [! R !]).
  Proof. rewrite -{2}bi.persistently_pure. exact: plain_wand_intro_r. Qed.
End plain_wand.

Section theory.
  #[local] Set Default Proof Using "Type*".
  Context `{!BiEmbed siPropI PROP}.
  Context `{!BiInternalEq PROP, !BiEmbedInternalEq siPropI PROP}.
  Context `{!BiPlainly PROP, !BiEmbedPlainly siPropI PROP}.
  Notation "P ⊣⊢ Q" := (P ⊣⊢@{PROP} Q).
  Notation "P ⊢ Q" := (P ⊢@{PROP} Q).
  #[local] Arguments siProp_holds !_ _ / : assert.

  #[local] Definition unseal_eqs := (si_cmra_valid_eq, siprop.siProp_primitive.siProp_unseal).
  #[local] Ltac unseal' :=
    unfold bi_pure, bi_and, bi_or, bi_forall, bi_exist, internal_eq; simpl;
    unfold bi_internal_eq_internal_eq; simpl;
    rewrite ?unseal_eqs /=.
  #[local] Ltac unseal := let n := fresh "n" in constructor => n /=; unseal'.

  #[local] Tactic Notation "solve_entails'" tactic1(tac) :=
    apply embed_mono; unseal; by tac.
  #[local] Tactic Notation "solve_equiv'" tactic1(tac) :=
    apply embed_proper; unseal; by tac.
  #[local] Tactic Notation "solve_entails" uconstr(lem) :=
    solve_entails' (apply lem).
  #[local] Tactic Notation "solve_equiv" uconstr(lem) :=
    solve_equiv' (apply lem).

  (** iris.algebra.ofe *)
  Section ofe.
    Context {A : ofe}.
    Implicit Types a b : A.

    Lemma discrete_eq_L `{!LeibnizEquiv A} a b : Discrete a → a ≡ b ⊣⊢ [! a = b !].
    Proof. unfold_leibniz. exact: discrete_eq. Qed.
  End ofe.

  (** iris.algebra.cmra *)
  Section cmra.
    Context {A : cmra}.
    Implicit Types x y : A.

    Lemma validI_op_l x y : ✓ (x ⋅ y) ⊢ ✓ x.
    Proof. solve_entails cmra_validN_op_l. Qed.
    Lemma validI_op_r x y : ✓ (x ⋅ y) ⊢ ✓ y.
    Proof. solve_entails cmra_validN_op_r. Qed.

    Lemma exclusive_includedI x y `{!Exclusive x} : x ≼ y ⊢ ✓ y -∗ False.
    Proof.
      apply: plain_wand_intro_pure_r.
      rewrite -embed_includedI -embed_and -embed_pure.
      solve_entails' (intros []; eapply exclusive_includedN).
    Qed.

    Lemma validI_includedI x y : ✓ y ⊢ x ≼ y -∗ <pers> ✓ x.
    Proof.
      apply: plain_wand_intro_r. rewrite -embed_includedI -embed_and.
      solve_entails' (intros []; eapply cmra_validN_includedN).
    Qed.

    Lemma cmra_discrete_includedN_l n x y : Discrete x → ✓{n} y → x ≼{n} y → x ≼ y.
    Proof.
      intros ? Hv Hinc. apply cmra_discrete_included_l; first done.
      - apply (cmra_validN_le n); first done. cbn; lia.
      - apply (cmra_includedN_le n); first done. cbn; lia.
    Qed.
    Lemma discrete_includedI_l x y : Discrete x → ✓ y ⊢ x ≼ y -∗ [! x ≼ y !].
    Proof.
      intros. apply: plain_wand_intro_pure_r.
      rewrite -embed_includedI -embed_pure -embed_and.
      solve_entails' (intros []; eapply cmra_discrete_includedN_l).
    Qed.
    Lemma discrete_includedI_r x y : Discrete y → x ≼ y ⊢ [! x ≼ y !].
    Proof. intros. by rewrite discrete_includedI. Qed.

    Lemma discrete_validI `{!CmraDiscrete A} x : ✓ x ⊣⊢ [! ✓ x !].
    Proof. rewrite -embed_pure. symmetry. solve_equiv cmra_discrete_valid_iff. Qed.

  End cmra.

  Section prod.
    Context {A B : cmra}.
    Implicit Types a : A.
    Implicit Types b : B.
    Implicit Types x y : A * B.

    Lemma prod_validI x : ✓ x ⊣⊢ (✓ x.1 ∧ ✓ x.2).
    Proof. rewrite -embed_and. apply embed_proper. by unseal. Qed.

    Lemma prod_includedI x y : x ≼ y ⊣⊢ x.1 ≼ y.1 ∧ x.2 ≼ y.2.
    Proof. rewrite -!embed_includedI -embed_and. solve_equiv prod_includedN. Qed.

    Lemma pair_validI a b : ✓ (a, b) ⊣⊢ ✓ a ∧ ✓ b.
    Proof. by rewrite prod_validI. Qed.

    Lemma pair_includedI a a' b b' : (a, b) ≼ (a', b') ⊣⊢ a ≼ a' ∧ b ≼ b'.
    Proof. by rewrite prod_includedI. Qed.
  End prod.

  Section option.
    Context {A : cmra}.
    Implicit Types a : A.
    Implicit Types ma mb : option A.

    Lemma None_validI : ✓ (@None A) ⊣⊢ True.
    Proof. split'; auto. Qed.
    Lemma Some_validI a : ✓ Some a ⊣⊢ ✓ a.
    Proof. solve_equiv Some_validN. Qed.
    Lemma option_validI ma : ✓ ma ⊣⊢ if ma is Some a then ✓ a else True.
    Proof. destruct ma; by rewrite ?Some_validI ?None_validI. Qed.

    Lemma option_includedI ma mb :
      ma ≼ mb ⊣⊢
      [! ma = None !] ∨ ∃ a b, [! ma = Some a ∧ mb = Some b !] ∧ (a ≡ b ∨ a ≼ b).
    Proof.
      setoid_rewrite bi.pure_and. setoid_rewrite <-(assoc bi_and).
      setoid_rewrite <-embed_includedI. setoid_rewrite <-embed_internal_eq.
      setoid_rewrite <-embed_or. setoid_rewrite <-embed_pure.
      repeat setoid_rewrite <-embed_and.
      repeat setoid_rewrite <-embed_exist. rewrite -embed_or.
      solve_equiv option_includedN.
    Qed.
    Lemma option_includedI_total `{!CmraTotal A} ma mb :
      ma ≼ mb ⊣⊢ [! ma = None !] ∨ ∃ a b, [! ma = Some a ∧ mb = Some b !] ∧ a ≼ b.
    Proof.
      setoid_rewrite bi.pure_and. setoid_rewrite <-(assoc bi_and).
      setoid_rewrite <-embed_includedI.
      setoid_rewrite <-embed_pure. repeat setoid_rewrite <-embed_and.
      repeat setoid_rewrite <-embed_exist. rewrite -embed_or.
      solve_equiv option_includedN_total.
    Qed.

    Lemma None_includedI mb : None ≼ mb ⊣⊢ True.
    Proof. split'; first by auto. iIntros "?". iExists mb. by rewrite left_id. Qed.

    Lemma exclusiveI_Some_l a `{!Exclusive a} mb : ✓ (Some a ⋅ mb) ⊢ [! mb = None !].
    Proof. rewrite -embed_pure. solve_entails exclusiveN_Some_l. Qed.
    Lemma exclusiveI_Some_r a `{!Exclusive a} mb : ✓ (mb ⋅ Some a) ⊢ [! mb = None !].
    Proof. rewrite -embed_pure. solve_entails exclusiveN_Some_r. Qed.

    Lemma Some_includedI a b : Some a ≼ Some b ⊣⊢ a ≡ b ∨ a ≼ b.
    Proof.
      rewrite -!embed_includedI -embed_internal_eq -embed_or.
      solve_equiv Some_includedN.
    Qed.
    Lemma Some_includedI_total `{!CmraTotal A} a b : Some a ≼ Some b ⊣⊢ a ≼ b.
    Proof. rewrite -!embed_includedI. solve_equiv Some_includedN_total. Qed.

    Lemma Some_includedI_exclusive a `{!Exclusive a} b :
      Some a ≼ Some b ⊢ ✓ b -∗ <pers> (a ≡ b).
    Proof.
      apply: plain_wand_intro_r.
      rewrite -embed_includedI -embed_and -embed_internal_eq.
      solve_entails' (intros []; apply Some_includedN_exclusive).
    Qed.

    Lemma is_Some_includedI ma mb : ma ≼ mb ⊢ [! is_Some ma → is_Some mb !].
    Proof. rewrite -embed_includedI -embed_pure. solve_entails is_Some_includedN. Qed.
  End option.

  Section discrete_fun.
    Context `{B : A → ucmra}.
    Implicit Types f g : discrete_fun B.
    Implicit Types x : A.

    Lemma discrete_fun_validI f : ✓ f ⊣⊢ (∀ i, ✓ (f i)).
    Proof. rewrite -embed_forall. solve_equiv' done. Qed.

    Lemma discrete_fun_includedN_spec_1 n f g x : f ≼{n} g → f x ≼{n} g x.
    Proof. intros [g' Hg]. exists (g' x). apply Hg. Qed.
    Lemma discrete_fun_includedN_spec `{Finite A} n f g : f ≼{n} g ↔ ∀ x, f x ≼{n} g x.
    Proof.
      split.
      - by move/discrete_fun_includedN_spec_1.
      - intros [g' ?]%finite_choice. by exists g'.
    Qed.

    Lemma discrete_fun_includedI_spec_1 f g x : f ≼ g ⊢ f x ≼ g x.
    Proof. rewrite -!embed_includedI. solve_entails discrete_fun_includedN_spec_1. Qed.
    Lemma discrete_fun_includedI_spec `{Finite A} f g : f ≼ g ⊣⊢ (∀ x, f x ≼ g x).
    Proof.
      repeat setoid_rewrite <- embed_includedI. rewrite -embed_forall.
      solve_equiv discrete_fun_includedN_spec.
    Qed.
  End discrete_fun.

  (** iris.algebra.excl *)
  Section excl.
    Context {A : ofe}.
    Implicit Types x : excl A.
    Implicit Types mx : option (excl A).
    Implicit Types a : A.

    Lemma excl_validI x : ✓ x ⊣⊢ if x is ExclInvalid then False else True.
    Proof. destruct x; split'; auto using cmra_valid_elim. Qed.
    Lemma excl_validI_inv_l mx a : ✓ (Excl' a ⋅ mx) ⊢ [! mx = None !].
    Proof. rewrite -embed_pure. solve_entails excl_validN_inv_l. Qed.
    Lemma excl_validI_inv_r mx a : ✓ (mx ⋅ Excl' a) ⊢ [! mx = None !].
    Proof. rewrite -embed_pure. solve_entails excl_validN_inv_r. Qed.

    Lemma excl_op_validI a1 a2 : ✓ (Excl a1 ⋅ Excl a2) ⊣⊢ False.
    Proof. by rewrite excl_validI. Qed.

    Lemma Excl_includedI a b : Excl' a ≼ Excl' b ⊣⊢ a ≡ b.
    Proof. rewrite -embed_includedI -embed_internal_eq. solve_equiv Excl_includedN. Qed.
  End excl.

  (** iris.algebra.agree *)
  Section agree.
    Context {A : ofe}.
    Implicit Types x y : agree A.
    Implicit Types a b : A.

    Lemma agree_includedI x y : x ≼ y ⊢ y ≡ x ⋅ y.
    Proof. iDestruct 1 as (z) "Hy". iRewrite "Hy". by rewrite assoc agree_idemp. Qed.

    Lemma agree_valid_includedI x y : ✓ y ⊢ x ≼ y -∗ <pers> (x ≡ y).
    Proof.
      apply: plain_wand_intro_r.
      rewrite -embed_includedI -embed_and -embed_internal_eq.
      solve_entails' (intros []; apply agree_valid_includedN).
    Qed.

    Lemma to_agree_includedI a b : to_agree a ≼ to_agree b ⊣⊢ a ≡ b.
    Proof.
      rewrite -embed_includedI -embed_internal_eq.
      solve_equiv to_agree_includedN.
    Qed.

    Lemma agree_validI x y : ✓ (x ⋅ y) ⊢ x ≡ y.
    Proof. rewrite -embed_internal_eq. solve_entails agree_op_invN. Qed.

    Lemma to_agree_uninjI x : ✓ x ⊢ ∃ a, to_agree a ≡ x.
    Proof.
      setoid_rewrite <- embed_internal_eq. rewrite -embed_exist.
      solve_entails to_agree_uninjN.
    Qed.

    Lemma agree_equivI a b : to_agree a ≡ to_agree b ⊣⊢ a ≡ b.
    Proof. rewrite -!embed_internal_eq. solve_equiv' (rewrite (inj_iff to_agree)). Qed.
  End agree.

  (** iris.algebra.view *)
  Section view.
    Context {A B} (rel : view_rel A B).
    Implicit Types relI : siProp.
    Implicit Types a : A.
    Implicit Types b : B.

    Notation "●V dq a" := (view_auth (rel:=rel) dq a)
      (at level 20, dq custom dfrac at level 1, format "●V dq  a").
    Notation "◯V a" := (view_frag (rel:=rel) a) (at level 20).

    Tactic Notation "lift" uconstr(lem) :=
      solve_entails' (rewrite lem; naive_solver).
    Tactic Notation "combine" uconstr(lem1) "," uconstr(lem2) :=
      split'; naive_solver eauto using lem1, lem2.

    Lemma view_auth_dfrac_validI_frac dq a : ✓ (●V{dq} a) ⊢ [! ✓ dq !]%Qp.
    Proof.
      rewrite -embed_pure.
      solve_entails' (rewrite view_auth_dfrac_validN; destruct 1).
    Qed.

    Lemma view_auth_frac_validI_frac q a : ✓ (●V{# q} a) ⊢ [! q ≤ 1 !]%Qp.
    Proof. apply view_auth_dfrac_validI_frac. Qed.

    Lemma view_auth_dfrac_validI_frac_2 dq1 dq2 a1 a2 :
      ✓ (●V{dq1} a1 ⋅ ●V{dq2} a2) ⊢ [! ✓ (dq1 ⋅ dq2) !].
    Proof.
      rewrite -embed_pure.
      solve_entails' (rewrite view_auth_dfrac_op_validN; destruct 1).
    Qed.

    Lemma view_auth_frac_validI_frac_2 q1 q2 a1 a2 :
      ✓ (●V{# q1} a1 ⋅ ●V{# q2} a2) ⊢ [! q1 + q2 ≤ 1 !]%Qp.
    Proof. apply view_auth_dfrac_validI_frac_2. Qed.

    Lemma view_auth_dfrac_op_invI dp1 a1 dp2 a2 : ✓ (●V{dp1} a1 ⋅ ●V{dp2} a2) ⊢ a1 ≡ a2.
    Proof. rewrite -embed_internal_eq. solve_entails view_auth_dfrac_op_invN. Qed.
    Lemma view_auth_dfrac_op_invI_L `{!OfeDiscrete A, !LeibnizEquiv A} dp1 a1 dp2 a2 :
      ✓ (●V{dp1} a1 ⋅ ●V{dp2} a2) ⊢ [! a1 = a2 !].
    Proof. unfold_leibniz. by rewrite view_auth_dfrac_op_invI discrete_eq. Qed.

    Lemma view_auth_frac_validI_1 relI q a :
      (∀ n, rel n a ε → siProp_holds relI n) → ✓ (●V{# q} a) ⊢ [! q ≤ 1 !]%Qp ∧ embed relI.
    Proof. intros. rewrite -embed_pure -embed_and. lift view_auth_dfrac_validN. Qed.
    Lemma view_auth_frac_validI_2 relI q a :
      (∀ n, siProp_holds relI n → rel n a ε) → [! q ≤ 1 !]%Qp ∧ embed relI ⊢ ✓ (●V{# q} a).
    Proof. intros. rewrite -embed_pure -embed_and. lift view_auth_dfrac_validN. Qed.
    Lemma view_auth_frac_validI relI q a :
      (∀ n, rel n a ε ↔ siProp_holds relI n) → ✓ (●V{# q} a) ⊣⊢ [! q ≤ 1 !]%Qp ∧ embed relI.
    Proof. combine view_auth_frac_validI_1, view_auth_frac_validI_2. Qed.

    Lemma view_auth_validI_1 relI a :
      (∀ n, rel n a ε → siProp_holds relI n) → ✓ (●V a) ⊢ embed relI.
    Proof. intros. lift view_auth_validN. Qed.
    Lemma view_auth_validI_2 relI a :
      (∀ n, siProp_holds relI n → rel n a ε) → embed relI ⊢ ✓ (●V a).
    Proof. intros. lift view_auth_validN. Qed.
    Lemma view_auth_validI relI a :
      (∀ n, rel n a ε ↔ siProp_holds relI n) → ✓ (●V a) ⊣⊢ embed relI.
    Proof. combine view_auth_validI_1, view_auth_validI_2. Qed.

    Lemma view_auth_frac_op_validI_1 relI q1 q2 a1 a2 :
      (∀ n, rel n a1 ε → siProp_holds relI n) →
      ✓ (●V{# q1} a1 ⋅ ●V{# q2} a2) ⊢ [! q1 + q2 ≤ 1 !]%Qp ∧ a1 ≡ a2 ∧ embed relI.
    Proof.
      intros. rewrite -embed_pure -embed_internal_eq -!embed_and.
      lift view_auth_dfrac_op_validN.
    Qed.
    Lemma view_auth_frac_op_validI_2 relI q1 q2 a1 a2 :
      (∀ n, siProp_holds relI n → rel n a1 ε) →
      [! q1 + q2 ≤ 1 !]%Qp ∧ a1 ≡ a2 ∧ embed relI ⊢ ✓ (●V{# q1} a1 ⋅ ●V{# q2} a2).
    Proof.
      intros. rewrite -embed_pure -embed_internal_eq -!embed_and.
      lift view_auth_dfrac_op_validN.
    Qed.
    Lemma view_auth_frac_op_validI relI q1 q2 a1 a2 :
      (∀ n, rel n a1 ε ↔ siProp_holds relI n) →
      ✓ (●V{# q1} a1 ⋅ ●V{# q2} a2) ⊣⊢ [! q1 + q2 ≤ 1 !]%Qp ∧ a1 ≡ a2 ∧ embed relI.
    Proof. combine view_auth_frac_op_validI_1, view_auth_frac_op_validI_2. Qed.

    Lemma view_auth_op_validI a1 a2 : ✓ (●V a1 ⋅ ●V a2) ⊣⊢ False.
    Proof. rewrite -embed_pure. solve_equiv view_auth_op_validN. Qed.

    Lemma view_frag_validI_1 relI b :
      (∀ n a, rel n a b → siProp_holds relI n) → ✓ (◯V b) ⊢ embed relI.
    Proof. intros. lift view_frag_validN. Qed.
    Lemma view_frag_validI_2 relI b :
      (∀ n, siProp_holds relI n → ∃ a, rel n a b) → embed relI ⊢ ✓ (◯V b).
    Proof. intros. lift view_frag_validN. Qed.
    Lemma view_frag_validI relI b :
      (∀ n, siProp_holds relI n ↔ ∃ a, rel n a b) → ✓ (◯V b) ⊣⊢ embed relI.
    Proof. combine view_frag_validI_1, view_frag_validI_2. Qed.

    Lemma view_both_frac_validI_1 relI q a b :
      (∀ n, rel n a b → siProp_holds relI n) → ✓ (●V{# q} a ⋅ ◯V b) ⊢ [! q ≤ 1 !]%Qp ∧ embed relI.
    Proof. intros. rewrite -embed_pure -embed_and. lift view_both_dfrac_validN. Qed.
    Lemma view_both_frac_validI_2 relI q a b :
      (∀ n, siProp_holds relI n → rel n a b) → [! q ≤ 1 !]%Qp ∧ embed relI ⊢ ✓ (●V{# q} a ⋅ ◯V b).
    Proof. intros. rewrite -embed_pure -embed_and. lift view_both_dfrac_validN. Qed.
    Lemma view_both_frac_validI relI q a b :
      (∀ n, rel n a b ↔ siProp_holds relI n) → ✓ (●V{# q} a ⋅ ◯V b) ⊣⊢ [! q ≤ 1 !]%Qp ∧ embed relI.
    Proof. combine view_both_frac_validI_1, view_both_frac_validI_2. Qed.

    Lemma view_both_validI_1 relI a b :
      (∀ n, rel n a b → siProp_holds relI n) → ✓ (●V a ⋅ ◯V b) ⊢ embed relI.
    Proof. intros. lift view_both_validN. Qed.
    Lemma view_both_validI_2 relI a b :
      (∀ n, siProp_holds relI n → rel n a b) → embed relI ⊢ ✓ (●V a ⋅ ◯V b).
    Proof. intros. lift view_both_validN. Qed.
    Lemma view_both_validI relI a b :
      (∀ n, rel n a b ↔ siProp_holds relI n) → ✓ (●V a ⋅ ◯V b) ⊣⊢ embed relI.
    Proof. combine view_both_validI_1, view_both_validI_2. Qed.

    Lemma view_auth_dfrac_includedI dq1 dq2 a1 a2 b :
      ●V{dq1} a1 ≼ ●V{dq2} a2 ⋅ ◯V b ⊣⊢ [! dq1 ≼ dq2 ∨ dq1 = dq2 !] ∧ a1 ≡ a2.
    Proof.
      rewrite -embed_includedI -embed_pure -embed_internal_eq -embed_and.
      solve_equiv view_auth_dfrac_includedN.
    Qed.

    Lemma view_auth_frac_includedI q1 q2 a1 a2 b :
      ●V{# q1} a1 ≼ ●V{# q2} a2 ⋅ ◯V b ⊣⊢ [! q1 ≤ q2 !]%Qp ∧ a1 ≡ a2.
    Proof.
      by rewrite view_auth_dfrac_includedI qple_dfrac_own_incl.
    Qed.

    Lemma view_auth_includedI a1 a2 b : ●V a1 ≼ ●V a2 ⋅ ◯V b ⊣⊢ a1 ≡ a2.
    Proof.
      rewrite -embed_includedI -embed_internal_eq.
      solve_equiv view_auth_includedN.
    Qed.

    Lemma view_frag_includedI dq a b1 b2 : ◯V b1 ≼ ●V{dq} a ⋅ ◯V b2 ⊣⊢ b1 ≼ b2.
    Proof. rewrite -!embed_includedI. solve_equiv view_frag_includedN. Qed.

    Lemma view_both_dfrac_includedI dq1 dq2 a1 a2 b1 b2 :
      ●V{dq1} a1 ⋅ ◯V b1 ≼ ●V{dq2} a2 ⋅ ◯V b2 ⊣⊢ [! dq1 ≼ dq2 ∨ dq1 = dq2 !]%Qp ∧ a1 ≡ a2 ∧ b1 ≼ b2.
    Proof.
      rewrite -!embed_includedI -embed_pure -embed_internal_eq -!embed_and.
      solve_equiv view_both_dfrac_includedN.
    Qed.

    Lemma view_both_frac_includedI q1 q2 a1 a2 b1 b2 :
      ●V{# q1} a1 ⋅ ◯V b1 ≼ ●V{# q2} a2 ⋅ ◯V b2 ⊣⊢ [! q1 ≤ q2 !]%Qp ∧ a1 ≡ a2 ∧ b1 ≼ b2.
    Proof.
      by rewrite view_both_dfrac_includedI qple_dfrac_own_incl.
    Qed.

    Lemma view_both_includedI a1 a2 b1 b2 :
      ●V a1 ⋅ ◯V b1 ≼ ●V a2 ⋅ ◯V b2 ⊣⊢ a1 ≡ a2 ∧ b1 ≼ b2.
    Proof.
      rewrite -!embed_includedI -embed_internal_eq -embed_and.
      solve_equiv view_both_includedN.
    Qed.
  End view.

  (** iris.algebra.auth *)
  Section auth.
    Context {A : ucmra}.
    Implicit Types relI : siProp.
    Implicit Types a b : A.
    Implicit Types x y : auth A.

    #[local] Lemma auth_view_rel_auth n a :
      view_rel_holds auth_view_rel n a ε ↔ siProp_holds (si_cmra_valid a) n.
    Proof.
      unseal'. split.
      - by destruct 1.
      - split. by apply ucmra_unit_leastN. done.
    Qed.

    Lemma auth_auth_frac_validI q a : ✓ (●{#q} a) ⊣⊢ [! q ≤ 1 !]%Qp ∧ ✓ a.
    Proof. apply view_auth_frac_validI=>n. apply auth_view_rel_auth. Qed.

    Lemma auth_auth_validI a : ✓ (● a) ⊣⊢ ✓ a.
    Proof. by rewrite auth_auth_frac_validI refl_True left_id. Qed.

    Lemma auth_auth_frac_op_validI_1 q1 q2 a1 a2 :
      ✓ (●{#q1} a1 ⋅ ●{#q2} a2) ⊢ [! q1 + q2 ≤ 1 !]%Qp ∧ a1 ≡ a2 ∧ ✓ a1.
    Proof. apply view_auth_frac_op_validI_1=>n. apply auth_view_rel_auth. Qed.
    Lemma auth_auth_frac_op_validI_2 q1 q2 a1 a2 :
      [! q1 + q2 ≤ 1 !]%Qp ∧ a1 ≡ a2 ∧ ✓ a1 ⊢ ✓ (●{#q1} a1 ⋅ ●{#q2} a2).
    Proof. apply view_auth_frac_op_validI_2=>n. apply auth_view_rel_auth. Qed.
    Lemma auth_auth_frac_op_validI q1 q2 a1 a2 :
      ✓ (●{#q1} a1 ⋅ ●{#q2} a2) ⊣⊢ [! q1 + q2 ≤ 1 !]%Qp ∧ a1 ≡ a2 ∧ ✓ a1.
    Proof. apply view_auth_frac_op_validI=>n. apply auth_view_rel_auth. Qed.

    Lemma auth_auth_op_validI a1 a2 : ✓ (● a1 ⋅ ● a2) ⊣⊢ False.
    Proof. by rewrite view_auth_op_validI. Qed.

    Lemma auth_frag_validI b : ✓ (◯ b) ⊣⊢ ✓ b.
    Proof.
      apply view_frag_validI=>n. unseal'. split.
      - by exists b.
      - intros [a []]. exact: (cmra_validN_includedN _ _ a).
    Qed.

    Lemma auth_frag_op_validI b1 b2 : ✓ (◯ b1 ⋅ ◯ b2) ⊣⊢ ✓ (b1 ⋅ b2).
    Proof. apply auth_frag_validI. Qed.

    Lemma auth_both_frac_validI q a b :
      ✓ (●{#q} a ⋅ ◯ b) ⊣⊢ [! q ≤ 1 !]%Qp ∧ b ≼ a ∧ ✓ a.
    Proof.
      rewrite -embed_includedI -!embed_and.
      apply view_both_frac_validI=>n. unseal'. split.
      - intros [[c ?] ?]. split. by exists c. done.
      - intros ((c & ?) & ?). split. by exists c. done.
    Qed.

    Lemma auth_both_validI a b : ✓ (● a ⋅ ◯ b) ⊣⊢ b ≼ a ∧ ✓ a.
    Proof. by rewrite auth_both_frac_validI refl_True left_id. Qed.

    Lemma auth_both_frac_validI_2 q a b :
      (q ≤ 1)%Qp → ✓ a ⊢ b ≼ a -∗ <pers> ✓ (●{#q} a ⋅ ◯ b).
    Proof.
      intros. apply: plain_wand_intro_r. rewrite auth_both_frac_validI.
      iIntros "H". repeat iSplit; first done.
      - by iDestruct "H" as "[_ ?]".
      - by iDestruct "H" as "[? _]".
    Qed.
    Lemma auth_both_validI_2 a b : ✓ a ⊢ b ≼ a -∗ <pers> ✓ (● a ⋅ ◯ b).
    Proof. by apply auth_both_frac_validI_2. Qed.

    Lemma auth_both_frac_validI_discrete `{!CmraDiscrete A} q a b :
      ✓ (●{#q} a ⋅ ◯ b) ⊣⊢ [! (q ≤ 1)%Qp ∧ b ≼ a ∧ ✓ a !].
    Proof.
      rewrite auth_both_frac_validI discrete_includedI discrete_validI.
      by rewrite !bi.pure_and.
    Qed.
    Lemma auth_both_validI_discrete `{!CmraDiscrete A} a b :
      ✓ (● a ⋅ ◯ b) ⊣⊢ [! b ≼ a ∧ ✓ a !].
    Proof.
      rewrite auth_both_frac_validI_discrete. by rewrite refl_True left_id.
    Qed.

    Lemma auth_auth_frac_includedI p1 p2 a1 a2 b :
      ●{#p1} a1 ≼ ●{#p2} a2 ⋅ ◯ b ⊣⊢ [! p1 ≤ p2 !]%Qp ∧ a1 ≡ a2.
    Proof. apply view_auth_frac_includedI. Qed.
    Lemma auth_auth_includedI a1 a2 b : ● a1 ≼ ● a2 ⋅ ◯ b ⊣⊢ a1 ≡ a2.
    Proof. apply view_auth_includedI. Qed.

    Lemma auth_frag_includedN p a b1 b2 : ◯ b1 ≼ ●{#p} a ⋅ ◯ b2 ⊣⊢ b1 ≼ b2.
    Proof. apply view_frag_includedI. Qed.

    Lemma auth_both_frac_includedI p1 p2 a1 a2 b1 b2 :
      ●{#p1} a1 ⋅ ◯ b1 ≼ ●{#p2} a2 ⋅ ◯ b2 ⊣⊢ [! p1 ≤ p2 !]%Qp ∧ a1 ≡ a2 ∧ b1 ≼ b2.
    Proof. apply view_both_frac_includedI. Qed.
    Lemma auth_both_includedI a1 a2 b1 b2 :
      ● a1 ⋅ ◯ b1 ≼ ● a2 ⋅ ◯ b2 ⊣⊢ a1 ≡ a2 ∧ b1 ≼ b2.
    Proof. apply view_both_includedI. Qed.

  End auth.

  (** iris.algebra.lib.excl_auth *)
  Section excl_auth.
    Context {A : ofe}.
    Implicit Types a b : A.

    Lemma excl_auth_frac_validI q a : ✓ (●E{q} a) ⊣⊢ [! q ≤ 1 !]%Qp.
    Proof. rewrite -embed_pure. solve_equiv excl_auth_frac_validN. Qed.

    Lemma excl_auth_auth_frac_op_validI q1 q2 a1 a2 :
      ✓ (●E{q1} a1 ⋅ ●E{q2} a2) ⊣⊢ [! q1 + q2 ≤ 1 !]%Qp ∧ a1 ≡ a2.
    Proof.
      rewrite -embed_pure -embed_internal_eq -embed_and.
      solve_equiv excl_auth_auth_frac_op_validN.
    Qed.

    Lemma excl_auth_frac_op_invI p a q b : ✓ (●E{p} a ⋅ ●E{q} b) ⊢ a ≡ b.
    Proof. rewrite -embed_internal_eq. solve_entails excl_auth_frac_op_invN. Qed.

    Lemma excl_auth_frac_agreeI q a b : ✓ (●E{q} a ⋅ ◯E b) ⊢ a ≡ b.
    Proof. rewrite -embed_internal_eq. solve_entails excl_auth_frac_agreeN. Qed.

    Lemma excl_auth_validI a : ✓ (●E a ⋅ ◯E a) ⊣⊢ True.
    Proof.
      rewrite auth_both_validI includedI_True left_id.
      by rewrite Some_validI excl_validI.
    Qed.

    Lemma excl_auth_agreeI a b : ✓ (●E a ⋅ ◯E b) ⊢ a ≡ b.
    Proof. rewrite -embed_internal_eq. solve_entails excl_auth_agreeN. Qed.

    Lemma excl_auth_frag_validI_op_1_l a b : ✓ (◯E a ⋅ ◯E b) ⊢ False.
    Proof.
      rewrite -auth_frag_op -Some_op.
      by rewrite auth_frag_validI Some_validI excl_op_validI.
    Qed.

  End excl_auth.

  (** iris.algebra.lib.frac_auth, skylabs.algebra.frac_auth *)
  Section frac_auth.
    Context {A : cmra}.
    Implicit Types a b : A.

    Lemma frac_auth_auth_frac_validI q a : ✓ (●F{q} a) ⊣⊢ [! q ≤ 1 !]%Qp ∧ ✓ a.
    Proof.
      rewrite -embed_pure -embed_and.
      solve_equiv frac_auth_auth_frac_validN.
    Qed.

    Lemma frac_auth_auth_frac_op_validI q1 q2 a1 a2 :
      ✓ (●F{q1} a1 ⋅ ●F{q2} a2) ⊣⊢ [! q1 + q2 ≤ 1 !]%Qp ∧ a1 ≡ a2 ∧ ✓ a1.
    Proof.
      rewrite -embed_pure -embed_internal_eq -embed_and -embed_and.
      solve_equiv frac_auth_auth_frac_op_validN.
    Qed.

    Lemma frac_auth_auth_frac_op_invI p a q b : ✓ (●F{p} a ⋅ ●F{q} b) ⊢ a ≡ b.
    Proof.
      rewrite -embed_internal_eq.
      solve_entails frac_auth_auth_frac_op_invN.
    Qed.

    Lemma frac_auth_auth_frag_includedI q1 q2 a b :
      ✓ (●F{q1} a ⋅ ◯F{q2} b) ⊢ Some b ≼ Some a.
    Proof.
      rewrite -embed_includedI.
      solve_entails frac_auth_auth_frag_includedN.
    Qed.
    Lemma frac_auth_auth_frag_includedI_discrete `{!CmraDiscrete A} q1 q2 a b :
      ✓ (●F{q1} a ⋅ ◯F{q2} b) ⊢ [! Some b ≼ Some a !].
    Proof.
      rewrite -embed_pure.
      solve_entails' (rewrite -cmra_discrete_valid_iff;
        apply frac_auth_auth_frag_included).
    Qed.
    Lemma frac_auth_auth_frag_includedI_total `{!CmraTotal A} q1 q2 a b :
      ✓ (●F{q1} a ⋅ ◯F{q2} b) ⊢ b ≼ a.
    Proof.
      rewrite -embed_includedI.
      solve_entails frac_auth_auth_frag_includedN_total.
    Qed.
    Lemma frac_auth_auth_frag_includedI_total_discrete `{!CmraDiscrete A,
        !CmraTotal A} q1 q2 a b :
      ✓ (●F{q1} a ⋅ ◯F{q2} b) ⊢ [! b ≼ a !].
    Proof.
      rewrite -embed_pure.
      solve_entails' (rewrite -cmra_discrete_valid_iff;
        apply frac_auth_auth_frag_included_total).
    Qed.

    Lemma frac_auth_auth_frac_agreeI q a b : ✓ (●F{q} a ⋅ ◯F b) ⊢ a ≡ b.
    Proof.
      rewrite -embed_internal_eq.
      solve_entails frac_auth_auth_frac_agreeN.
    Qed.

    Lemma frac_auth_frag_validI q a : ✓ (◯F{q} a) ⊣⊢ [! q ≤ 1 !]%Qp ∧ ✓ a.
    Proof. rewrite -embed_pure -embed_and. solve_equiv frac_auth_frag_validN. Qed.

  End frac_auth.

  Section gmap_view.
    Context `{Countable K} {V : ofe}.
    Implicit Types (k : K) (v : V).
    Implicit Types (m : gmap K (agreeR V)).

    Lemma gmap_view_auth_validN n m q : ✓{n} gmap_view_auth (DfracOwn q) m ↔ (q ≤ 1)%Qp.
    Proof.
      rewrite view_auth_dfrac_validN.
      intuition eauto using gmap_view.gmap_view_rel_unit.
    Qed.

    Lemma gmap_view_auth_validI m q : ✓ gmap_view_auth (DfracOwn q) m ⊣⊢ [! q ≤ 1 !]%Qp.
    Proof. rewrite -embed_pure. solve_equiv gmap_view_auth_validN. Qed.

    Lemma gmap_view_auth_op_validI q1 q2 m1 m2 :
      ✓ (gmap_view_auth (DfracOwn q1) m1 ⋅ gmap_view_auth (DfracOwn q2) m2) ⊣⊢
        [! q1 + q2 ≤ 1 !]%Qp ∧ m1 ≡ m2.
    Proof.
      rewrite -embed_pure -embed_internal_eq -embed_and.
      solve_equiv gmap_view_auth_dfrac_op_validN.
    Qed.

    Lemma gmap_view_frag_validI k dq v : ✓ gmap_view_frag k dq (to_agree v) ⊣⊢ [! ✓ dq !].
    Proof.
      rewrite -embed_pure.
      apply embed_proper; unseal.
      rewrite gmap_view_frag_validN; naive_solver.
    Qed.

    Lemma gmap_view_frag_op_validI k dq1 dq2 v1 v2 :
      ✓ (gmap_view_frag k dq1 (to_agree v1) ⋅ gmap_view_frag k dq2 (to_agree v2)) ⊣⊢
        [! ✓ (dq1 ⋅ dq2) !] ∧ v1 ≡ v2.
    Proof.
      rewrite -embed_pure -embed_internal_eq -embed_and.
      apply embed_proper; unseal.
      rewrite gmap_view_frag_op_validN.
      rewrite to_agree_op_validN.
      done.
    Qed.

  End gmap_view.

End theory.
