(*
 * Copyright (C) 2021 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import iris.algebra.lib.gmap_view.
Require Import bluerock.iris.extra.algebra.gset_bij.
Require Import bluerock.iris.extra.algebra.coGset.
Require Import bluerock.iris.extra.si_logic.algebra.
Require Import bluerock.iris.extra.bi.prelude.
Require Import bluerock.iris.extra.bi.observe.
Require Import bluerock.iris.extra.bi.includedI.
Require Import bluerock.iris.extra.bi.own.
Require Import bluerock.iris.extra.proofmode.proofmode.

Set Printing Coercions.

Implicit Types (p q : Qp) (dp dq : dfrac).

(** * Observations from ownership *)
(** We prove basic observations from [own g] for various CMRAs. We
don't attempt to cover all CMRAs, but we aim to cover goals of the
following forms for those CMRAs we do cover.

Validity (internal and discrete)

- [✓ a], [✓ (a ⋅ b)] from [own g a], [own g a ** own g b]

Absurdity

- [False] from [own g a ** own g b] when either is [Exclusive], with
  variations for [exclR], [auth_exclR], [fracR 1], [excl_authR], etc.

- [False] from [own g a] for [Empty_set], [ExclBot], etc.

Agreement (internal, discrete, and Leibniz)

- [a ≡ b] from [own g a ** own g b] for [agreeR], [viewR], [authR],
  [excl_authR], etc.

Note: There's a general problem with using [iDestruct] to make
observations. When we let typeclass resolution fill in the type of an
observation, we cannot combine making the observation with
introduction patterns that depend on the inferred type. Consider, for
example, the on-the-fly application of "view lemmas". Given ["Ai" :
pureR (own g (●E{qi} si))] for [i = 1, 2] we'd like to obtain [Hv : s1
= s2] in one step via [iDestruct (observe_2 [| ✓ _ |] with "A1 A2") as
%Hv%excl_auth_frac_op_inv_L] but we instead have to first [iDestruct]
with just [%Hv] and then manually [apply excl_auth_frac_op_inv_L in
Hv]. We know how to fix [iDestruct], and will report the bug upstream.
*)

Section observe.
  #[local] Set Default Proof Using "Type*".
  Context `{!BiEmbed siPropI PROP}.
  Context `{!BiInternalEq PROP, !BiEmbedInternalEq siPropI PROP}.
  Context `{!BiPlainly PROP, !BiEmbedPlainly siPropI PROP}.
  Notation HasOwn RA := (HasOwn PROP RA).
  Notation HasOwnValid RA := (HasOwnValid PROP RA).
  Notation Observe := (@Observe PROP).
  Notation Observe2 := (@Observe2 PROP).

  (** Ensure that none of the following instances are already derivable. *)
  #[local] Ltac GUARD := assert_fails (intros; by apply _).

  Section equivI.
    Context {A : ofe}.
    Implicit Types a b : A.

    #[global] Instance observe_discrete_eq a b P `{!Discrete a} :
      Observe (a ≡ b) P → Observe [| a ≡ b |] P.
    Proof. GUARD. rewrite/Observe=>->. iIntros (?). auto. Qed.
    #[global] Instance observe_discrete_eq_L `{!LeibnizEquiv A} a b P
        `{!Discrete a} :
      Observe (a ≡ b) P → Observe [| a = b |] P.
    Proof. GUARD. unfold_leibniz. apply _. Qed.
  End equivI.

  (** iris.algebra.ofe, iris.algebra.cmra *)
  Section cmra.
    Context {A : cmra}.
    Implicit Types a b : A.

    (** Discrete elements *)
    #[global] Instance observe_discrete_includedI a b P `{!Discrete b} :
      Observe (a ≼ b) P → Observe [| a ≼ b |] P.
    Proof. GUARD. rewrite /Observe=>->. iIntros "%". auto. Qed.

    #[global] Instance observe_discrete_validI `{!CmraDiscrete A} a P :
      Observe (✓ a) P → Observe [| ✓ a |] P.
    Proof. GUARD. rewrite /Observe=>->. iIntros "%". auto. Qed.

    Section own.
      Context `{!HasOwn A, !HasOwnValid A}.

      #[local] Lemma own_obs Q g a : (✓ a ⊢ Q) → Observe Q (own g a).
      Proof.
        iIntros (HQ) "A". iDestruct (own_valid with "A") as "#V".
        rewrite HQ. auto.
      Qed.
      #[local] Lemma own_2_obs Q g a b :
        (✓ (a ⋅ b) ⊢ Q) → Observe2 Q (own g a) (own g b).
      Proof.
        iIntros (HQ) "A B". iDestruct (own_valid_2 with "A B") as "#V".
        rewrite HQ. auto.
      Qed.

      (** Validity from ownership *)
      #[global] Instance own_validI g a : Observe (✓ a) (own g a).
      Proof. GUARD. by apply own_obs. Qed.
      Lemma test `{!CmraDiscrete A} g a : Observe [| ✓ a |] (own g a).
      Proof. by apply _. Abort.

      #[global] Instance own_2_validI g a b :
        Observe2 (✓ (a ⋅ b)) (own g a) (own g b).
      Proof. GUARD. by apply own_2_obs. Qed.
      #[global] Instance own_2_valid `{!CmraDiscrete A} g a b :
        Observe2 [| ✓ (a ⋅ b) |] (own g a) (own g b).
      Proof. GUARD. apply observe_2_pure, own_2_obs. auto. Qed.

      (** Exclusive elements *)
      #[global] Instance own_exclusive_l g a b `{!Exclusive a} :
        Observe2 False (own g a) (own g b).
      Proof.
        GUARD. apply own_2_obs.
        iApply (exclusive_includedI a). by iExists b.
      Qed.
      #[global] Instance own_exclusive_r g a b `{!Exclusive b} :
        Observe2 False (own g a) (own g b).
      Proof. GUARD. symmetry. apply _. Qed.
    End own.
  End cmra.

  Section empty.
    Notation RA := Empty_setR.
    Context `{!HasOwn RA, !HasOwnValid RA}.

    #[global] Instance own_Empty_set g x : Observe False (own g x).
    Proof. GUARD. by apply own_obs. Qed.
  End empty.

  (** iris.algebra.excl *)
  Section excl.
    Import iris.algebra.excl.
    Context {A : ofe}. Notation RA := (exclR A).
    Context `{!HasOwn RA, !HasOwnValid RA}.

    #[global] Instance own_excl_bot g : Observe False (own g ExclInvalid).
    Proof. GUARD. apply own_obs. by rewrite excl_validI. Qed.
    Lemma own_excl_l g a x : Observe2 False (own g (Excl a)) (own g x).
    Proof. by apply _. Abort.
    Lemma own_excl_r g a x : Observe2 False (own g x) (own g (Excl a)).
    Proof. by apply _. Abort.
  End excl.

  Section option_excl.
    Import iris.algebra.excl.
    Context {A : ofe}. Notation RA := (optionR (exclR A)).
    Context `{!HasOwn RA, !HasOwnValid RA}.

    #[global] Instance own_excl_inv_l g mx a :
      Observe2 [| mx = None |] (own g (Excl' a)) (own g mx).
    Proof. GUARD. apply observe_2_pure, own_2_obs, excl_validI_inv_l. Qed.
    #[global] Instance own_excl_inv_r g mx a :
      Observe2 [| mx = None |] (own g mx) (own g (Excl' a)).
    Proof. GUARD. symmetry. apply _. Qed.
  End option_excl.

  (** iris.algebra.frac *)
  Section frac.
    Import iris.algebra.frac.
    Notation RA := fracR.
    Context `{!HasOwn RA, !HasOwnValid RA}.

    #[global] Instance own_frac_valid g q : Observe [| (q ≤ 1)%Qp |] (own g q).
    Proof. GUARD. apply observe_pure, own_obs. by iIntros (?). Qed.

    #[global] Instance own_2_frac_valid g q p :
      Observe2 [| (q + p ≤ 1)%Qp |] (own g q) (own g p).
    Proof. GUARD. apply observe_2_pure, own_2_obs. by iIntros (?). Qed.
    Lemma own_2_frac_1_exclusive_l g q : Observe2 False (own g 1%Qp) (own g q).
    Proof. by apply _. Abort.
    Lemma own_2_frac_1_exclusive_r g q : Observe2 False (own g q) (own g 1%Qp).
    Proof. by apply _. Abort.
  End frac.

  (** iris.algebra.agree *)
  Section agree.
    Import iris.algebra.agree.
    Context {A : ofe}. Notation RA := (agreeR A).
    Context `{!HasOwn RA, !HasOwnValid RA}.

    (** Higher cost than the following [to_agree] variants.  *)
    #[global] Instance own_agreeI' g x y :
      Observe2 (x ≡ y) (own g x) (own g y) | 100.
    Proof. GUARD. apply own_2_obs, agree_validI. Qed.
    #[global] Instance own_agree' g x y `{!Discrete x} :
      Observe2 [| x ≡ y |] (own g x) (own g y) | 100.
    Proof.
      GUARD. apply observe_2_pure, own_2_obs.
      by rewrite agree_validI discrete_eq.
    Qed.

    #[global] Instance own_agreeI g a b :
      Observe2 (a ≡ b) (own g (to_agree a)) (own g (to_agree b)).
    Proof. GUARD. apply own_2_obs. by rewrite agree_validI agree_equivI. Qed.
    #[global] Instance own_agree g a b `{!Discrete a} :
      Observe2 [| a ≡ b |] (own g (to_agree a)) (own g (to_agree b)).
    Proof.
      GUARD. apply observe_2_pure, own_2_obs.
      by rewrite agree_validI agree_equivI discrete_eq.
    Qed.
    #[global] Instance own_agree_L `{!LeibnizEquiv A} g a b `{!Discrete a} :
      Observe2 [| a = b |] (own g (to_agree a)) (own g (to_agree b)).
    Proof. GUARD. unfold_leibniz. rewrite -(inj_iff to_agree). apply _. Qed.
  End agree.

  Section view.
    Import iris.algebra.view.
    Context {A B} (rel : view_rel A B). Notation RA := (viewR rel).
    Context `{!HasOwn RA, !HasOwnValid RA}.

    #[global] Instance own_view_auth_frac_valid g q a :
      Observe [| q ≤ 1 |]%Qp (own g (●V{#q} a)).
    Proof.
      GUARD. apply observe_pure, own_obs, view_auth_frac_validI_frac.
    Qed.
    #[global] Instance own_view_auth_frac_valid_2 g q1 q2 a1 a2 :
      Observe2 [| q1 + q2 ≤ 1 |]%Qp (own g (●V{#q1} a1)) (own g (●V{#q2} a2)).
    Proof.
      GUARD. apply observe_2_pure, own_2_obs, view_auth_frac_validI_frac_2.
    Qed.
    #[global] Instance own_view_auth_frac_valid_exclusive_l g q a1 a2 :
      Observe2 False (own g (●V a1)) (own g (●V{#q} a2)).
    Proof.
      GUARD. iIntros "A1 A2".
      by iDestruct (own_view_auth_frac_valid_2 with "A1 A2") as %?%Qp.not_add_le_l.
    Qed.
    #[global] Instance own_view_auth_frac_valid_exclusive_r g q a1 a2 :
      Observe2 False (own g (●V{#q} a1)) (own g (●V a2)).
    Proof. GUARD. symmetry. apply _. Qed.

    #[global] Instance own_view_auth_agreeI g q1 q2 a1 a2 :
      Observe2 (a1 ≡ a2) (own g (●V{#q1} a1)) (own g (●V{#q2} a2)).
    Proof. GUARD. apply own_2_obs, view_auth_dfrac_op_invI. Qed.
    #[global] Instance own_view_auth_agree g q1 q2 a1 a2 `{!Discrete a1} :
      Observe2 [| a1 ≡ a2 |] (own g (●V{#q1} a1)) (own g (●V{#q2} a2)).
    Proof.
      GUARD. apply observe_2_pure, own_2_obs.
      by rewrite view_auth_dfrac_op_invI discrete_eq.
    Qed.
    #[global] Instance own_view_auth_agree_L `{!LeibnizEquiv A} g q1 q2 a1 a2
        `{!Discrete a1} :
      Observe2 [| a1 = a2 |] (own g (●V{#q1} a1)) (own g (●V{#q2} a2)).
    Proof. GUARD. unfold_leibniz. apply _. Qed.
    Import fractional.
    #[global] Instance view_auth_frac g a :
      Fractional (fun q => own g (●V{#q} a)).
    Proof.
      GUARD. intros q1 q2. split'.
      - by iIntros "[$ $]".
      - iIntros "[A1 A2]". by iCombine "A1 A2" as "$".
    Qed.
  End view.

  (** iris.algebra.auth *)
  Section auth.
    Import iris.algebra.auth.
    Context {A : ucmra}. Notation RA := (authR A).
    Context `{!HasOwn RA, !HasOwnValid RA}.

    #[global] Instance own_auth_frac_valid g q a :
      Observe [| q ≤ 1 |]%Qp (own g (●{#q} a)).
    Proof.
      GUARD. apply observe_pure, own_obs.
      by rewrite auth_auth_frac_validI bi.and_elim_l.
    Qed.
    #[global] Instance own_auth_frac_valid_2 g q1 q2 a1 a2 :
      Observe2 [| q1 + q2 ≤ 1 |]%Qp (own g (●{#q1} a1)) (own g (●{#q2} a2)).
    Proof.
      GUARD. apply observe_2_pure, own_2_obs.
      by rewrite auth_auth_frac_op_validI bi.and_elim_l.
    Qed.
    Lemma test g q a1 a2 :
      Observe2 [| 1 + q ≤ 1 |]%Qp (own g (● a1)) (own g (●{#q} a2)).
    Proof. by apply _. Abort.

    #[global] Instance own_auth_frac_valid_exclusive_l g q a1 a2 :
      Observe2 False (own g (● a1)) (own g (●{#q} a2)).
    Proof.
      GUARD. iIntros "A1 A2".
      by iDestruct (own_auth_frac_valid_2 with "A1 A2") as %?%Qp.not_add_le_l.
    Qed.
    Lemma test g q a1 a2 : Observe2 False (own g (●{#1} a1)) (own g (●{#q} a2)).
    Proof. by apply _. Abort.

    #[global] Instance own_auth_frac_valid_exclusive_r g q a1 a2 :
      Observe2 False (own g (●{#q} a1)) (own g (● a2)).
    Proof. GUARD. symmetry. apply _. Qed.
    Lemma test g q a1 a2 : Observe2 False (own g (●{#q} a1)) (own g (● a2)).
    Proof. by apply _. Abort.

    #[global] Instance own_auth_agreeI g q1 q2 a1 a2 :
      Observe2 (a1 ≡ a2) (own g (●{#q1} a1)) (own g (●{#q2} a2)).
    Proof.
      GUARD. apply own_2_obs.
      by rewrite auth_auth_frac_op_validI bi.and_elim_r bi.and_elim_l.
    Qed.
    Lemma test g q a1 a2 : Observe2 (a1 ≡ a2) (own g (● a1)) (own g (●{#q} a2)).
    Proof. by apply _. Abort.

    #[global] Instance own_auth_agree g q1 q2 a1 a2 `{!Discrete a1} :
      Observe2 [| a1 ≡ a2 |] (own g (●{#q1} a1)) (own g (●{#q2} a2)).
    Proof.
      GUARD. apply observe_2_pure, own_2_obs.
      by rewrite auth_auth_frac_op_validI bi.and_elim_r bi.and_elim_l discrete_eq.
    Qed.
    #[global] Instance own_auth_agree_L `{!LeibnizEquiv A} g q1 q2 a1 a2
        `{!Discrete a1} :
      Observe2 [| a1 = a2 |] (own g (●{#q1} a1)) (own g (●{#q2} a2)).
    Proof. GUARD. unfold_leibniz. apply _. Qed.

    #[global] Instance auth_both_includedI' g q a b :
      Observe2 (b ≼ a) (own g (●{#q} a)) (own g (◯ b)).
    Proof.
      GUARD. apply own_2_obs.
      by rewrite auth_both_frac_validI bi.and_elim_r bi.and_elim_l.
    Qed.
    #[global] Instance auth_both_included' `{!CmraDiscrete A} g q a b :
      Observe2 [| b ≼ a |] (own g (●{#q} a)) (own g (◯ b)).
    Proof.
      GUARD. apply observe_2_pure, own_2_obs.
      rewrite auth_both_frac_validI_discrete. f_equiv=>?. tauto.
    Qed.

    Import fractional.
    #[global] Instance auth_auth_frac g a :
      Fractional (fun q => own g (●{#q} a)).
    Proof. GUARD. rewrite /auth_auth. apply _. Qed.
  End auth.

  (** bluerock.iris.extra.algebra.excl_auth, iris.algebra.lib.excl_auth *)
  Section excl_auth.
    Import bluerock.iris.extra.algebra.excl_auth.
    Context {A : ofe}. Notation RA := (excl_authR A).
    Context `{!HasOwn RA, !HasOwnValid RA}.

    (** Deal with the fact that [●E a] is TC opaque. *)
    #[global] Instance observe_own_excl_auth Q g a :
      Observe Q (own g (●E{1} a)) → Observe Q (own g (●E a)).
    Proof. GUARD. by rewrite excl_auth_auth_frac. Qed.
    #[global] Instance observe_2_own_excl_auth_l Q g a P :
      Observe2 Q (own g (●E{1} a)) P → Observe2 Q (own g (●E a)) P.
    Proof. GUARD. by rewrite excl_auth_auth_frac. Qed.
    #[global] Instance observe_2_own_excl_auth_r Q g a P :
      Observe2 Q P (own g (●E{1} a)) → Observe2 Q P (own g (●E a)).
    Proof. GUARD. by rewrite excl_auth_auth_frac. Qed.

    #[global] Instance own_excl_auth_frac_valid g q a :
      Observe [| q ≤ 1 |]%Qp (own g (●E{q} a)).
    Proof.
      GUARD. apply observe_pure, own_obs.
      by rewrite excl_auth_frac_validI.
    Qed.
    #[global] Instance own_excl_auth_frac_valid_2 g q1 q2 a1 a2 :
      Observe2 [| q1 + q2 ≤ 1 |]%Qp (own g (●E{q1} a1)) (own g (●E{q2} a2)).
    Proof.
      GUARD. apply observe_2_pure, own_2_obs.
      by rewrite excl_auth_auth_frac_op_validI bi.and_elim_l.
    Qed.
    Lemma test g q a1 a2 :
      Observe2 [| 1 + q ≤ 1 |]%Qp (own g (●E a1)) (own g (●E{q} a2)).
    Proof. by apply _. Abort.
    Lemma test g q a1 a2 :
      Observe2 [| q + 1 ≤ 1 |]%Qp (own g (●E{q} a1)) (own g (●E a2)).
    Proof. by apply _. Abort.

    #[global] Instance own_excl_auth_frac_valid_exclusive_l g q a1 a2 :
      Observe2 False (own g (●E{1} a1)) (own g (●E{q} a2)).
    Proof.
      GUARD. iIntros "A1 A2".
      by iDestruct (own_excl_auth_frac_valid_2 with "A1 A2") as %?%Qp.not_add_le_l.
    Qed.
    Lemma test g q a1 a2 : Observe2 False (own g (●E a1)) (own g (●E{q} a2)).
    Proof. by apply _. Abort.

    #[global] Instance own_excl_auth_frac_valid_exclusive_r g q a1 a2 :
      Observe2 False (own g (●E{q} a1)) (own g (●E{1} a2)).
    Proof. GUARD. symmetry. apply _. Qed.
    Lemma test g q a1 a2 : Observe2 False (own g (●E{q} a1)) (own g (●E a2)).
    Proof. by apply _. Abort.

    Lemma test g a1 a2 : Observe2 False (own g (●E a1)) (own g (●E a2)).
    Proof. by apply _. Abort.

    #[global] Instance own_excl_auth_frac_agreeI g q1 q2 a1 a2 :
      Observe2 (a1 ≡ a2) (own g (●E{q1} a1)) (own g (●E{q2} a2)).
    Proof. GUARD. apply own_2_obs, excl_auth_frac_op_invI. Qed.
    Lemma test g q a1 a2 : Observe2 (a1 ≡ a2) (own g (●E a1)) (own g (●E{q} a2)).
    Proof. by apply _. Abort.

    #[global] Instance own_excl_auth_frac_agree g q1 q2 a1 a2 `{!Discrete a1} :
      Observe2 [| a1 ≡ a2 |] (own g (●E{q1} a1)) (own g (●E{q2} a2)).
    Proof.
      GUARD. apply observe_2_pure, own_2_obs.
      by rewrite excl_auth_frac_op_invI discrete_eq.
    Qed.
    #[global] Instance own_excl_auth_frac_agree_L `{!LeibnizEquiv A} g q1 q2 a1 a2
        `{!Discrete a1} :
      Observe2 [| a1 = a2 |] (own g (●E{q1} a1)) (own g (●E{q2} a2)).
    Proof. GUARD. unfold_leibniz. apply _. Qed.

    #[global] Instance own_excl_auth_agreeI g q a b :
      Observe2 (a ≡ b) (own g (●E{q} a)) (own g (◯E b)).
    Proof. GUARD. apply own_2_obs, excl_auth_frac_agreeI. Qed.
    Lemma test g a b : Observe2 (a ≡ b) (own g (●E a)) (own g (◯E b)).
    Proof. by apply _. Abort.

    #[global] Instance own_excl_auth_agree g q a b `{!Discrete a} :
      Observe2 [| a ≡ b |] (own g (●E{q} a)) (own g (◯E b)).
    Proof.
      GUARD. apply observe_2_pure, own_2_obs.
      by rewrite excl_auth_frac_agreeI discrete_eq.
    Qed.
    #[global] Instance own_excl_auth_agree_L `{!LeibnizEquiv A} g q a b
        `{!Discrete a} :
      Observe2 [| a = b |] (own g (●E{q} a)) (own g (◯E b)).
    Proof. GUARD. unfold_leibniz. apply _. Qed.

    #[global] Instance own_excl_auth_frag_exclusive g b1 b2 :
      Observe2 False (own g (◯E b1)) (own g (◯E b2)).
    Proof. GUARD. apply own_2_obs, excl_auth_frag_validI_op_1_l. Qed.

    (** [Fractional] *)
    Import fractional.
    #[global] Instance own_excl_auth_auth_frac g a :
      Fractional (fun q => own g (●E{q} a)).
    Proof.
      GUARD. intros q1 q2. split'.
      - by iIntros "[$ $]".
      - iIntros "[A1 A2]". by iCombine "A1 A2" as "$".
    Qed.

  End excl_auth.

  (** bluerock.iris.extra.algebra.frac_auth, iris.algebra.lib.frac_auth *)
  Section frac_auth.
    Import bluerock.iris.extra.algebra.frac_auth.
    Context {A : cmra}. Notation RA := (frac_authR A).
    Context `{!HasOwn RA, !HasOwnValid RA}.

    (** Deal with the fact that [●F a] is TC opaque. *)
    #[global] Instance observe_own_frac_auth Q g a :
      Observe Q (own g (●F{1} a)) → Observe Q (own g (●F a)).
    Proof. GUARD. by rewrite frac_auth_auth_auth_frac. Qed.
    #[global] Instance observe_2_own_frac_auth_l Q g a P :
      Observe2 Q (own g (●F{1} a)) P → Observe2 Q (own g (●F a)) P.
    Proof. GUARD. by rewrite frac_auth_auth_auth_frac. Qed.
    #[global] Instance observe_2_own_frac_auth_r Q g a P :
      Observe2 Q P (own g (●F{1} a)) → Observe2 Q P (own g (●F a)).
    Proof. GUARD. by rewrite frac_auth_auth_auth_frac. Qed.

    (** Fractions are valid. *)
    #[global] Instance own_frac_auth_auth_frac_valid g q a :
      Observe [| q ≤ 1 |]%Qp (own g (●F{q} a)).
    Proof.
      GUARD. apply observe_pure, own_obs.
      rewrite frac_auth_auth_frac_validI. by iIntros "[$ _]".
    Qed.
    #[global] Instance own_frac_auth_auth_frac_valid_2 g q1 q2 a1 a2 :
      Observe2 [| q1 + q2 ≤ 1 |]%Qp (own g (●F{q1} a1)) (own g (●F{q2} a2)).
    Proof.
      GUARD. apply observe_2_pure, own_2_obs.
      rewrite frac_auth_auth_frac_op_validI. by iIntros "[$ _]".
    Qed.
    Lemma test g q a1 a2 :
      Observe2 [| 1 + q ≤ 1 |]%Qp (own g (●F a1)) (own g (●F{q} a2)).
    Proof. by apply _. Abort.
    Lemma test g q a1 a2 :
      Observe2 [| q + 1 ≤ 1 |]%Qp (own g (●F{q} a1)) (own g (●F a2)).
    Proof. by apply _. Abort.

    #[global] Instance own_frac_auth_auth_frac_exclusive_l g q a1 a2 :
      Observe2 False (own g (●F{1} a1)) (own g (●F{q} a2)).
    Proof.
      GUARD. iIntros "A1 A2".
      by iDestruct (own_frac_auth_auth_frac_valid_2 with "A1 A2")
        as %?%Qp.not_add_le_l.
    Qed.
    Lemma test g q a1 a2 : Observe2 False (own g (●F a1)) (own g (●F{q} a2)).
    Proof. by apply _. Abort.

    #[global] Instance own_frac_auth_auth_frac_exclusive_r g q a1 a2 :
      Observe2 False (own g (●F{q} a1)) (own g (●F{1} a2)).
    Proof. GUARD. symmetry. apply _. Qed.
    Lemma test g q a1 a2 : Observe2 False (own g (●F{q} a1)) (own g (●F a2)).
    Proof. by apply _. Abort.

    Lemma test g a1 a2 : Observe2 False (own g (●F a1)) (own g (●F a2)).
    Proof. by apply _. Abort.

    #[global] Instance own_frac_auth_frag_frac_valid g q a :
      Observe [| q ≤ 1 |]%Qp (own g (◯F{q} a)).
    Proof.
      GUARD. apply observe_pure, own_obs.
      rewrite frac_auth_frag_validI. by iIntros "[$ _]".
    Qed.
    #[global] Instance own_frac_auth_frag_frac_valid_2 g q1 q2 a1 a2 :
      Observe2 [| q1 + q2 ≤ 1 |]%Qp (own g (◯F{q1} a1)) (own g (◯F{q2} a2)).
    Proof.
      GUARD. apply observe_2_pure, own_2_obs.
      rewrite frac_auth_frag_validI. by iIntros "[$ _]".
    Qed.

    Lemma test g q a1 a2 :
      Observe2 [| 1 + q ≤ 1 |]%Qp (own g (◯F a1)) (own g (◯F{q} a2)).
    Proof. by apply _. Abort.
    Lemma test g q a1 a2 :
      Observe2 [| q + 1 ≤ 1 |]%Qp (own g (◯F{q} a1)) (own g (◯F a2)).
    Proof. by apply _. Abort.

    #[global] Instance own_frac_auth_frag_frac_exclusive_l g q a1 a2 :
      Observe2 False (own g (◯F{1} a1)) (own g (◯F{q} a2)).
    Proof.
      GUARD. iIntros "A1 A2".
      by iDestruct (own_frac_auth_frag_frac_valid_2 with "A1 A2")
        as %?%Qp.not_add_le_l.
    Qed.
    Lemma test g q a1 a2 : Observe2 False (own g (◯F a1)) (own g (◯F{q} a2)).
    Proof. by apply _. Abort.

    #[global] Instance own_frac_auth_frag_frac_exclusive_r g q a1 a2 :
      Observe2 False (own g (◯F{q} a1)) (own g (◯F{1} a2)).
    Proof. GUARD. symmetry. apply _. Qed.
    Lemma test g q a1 a2 : Observe2 False (own g (◯F{q} a1)) (own g (◯F a2)).
    Proof. by apply _. Abort.

    Lemma test g a1 a2 : Observe2 False (own g (◯F a1)) (own g (◯F a2)).
    Proof. by apply _. Abort.

    (** Element is valid *)
    #[global] Instance own_frac_auth_auth_valid g q a :
      Observe (✓ a) (own g (●F{q} a)).
    Proof.
      GUARD. apply own_obs.
      rewrite frac_auth_auth_frac_validI. by iIntros "[_ $]".
    Qed.
    Lemma test g a : Observe (✓ a) (own g (●F a)).
    Proof. by apply _. Abort.

    #[global] Instance own_frac_auth_frag_valid g q a :
      Observe (✓ a) (own g (◯F{q} a)).
    Proof.
      GUARD. apply own_obs.
      rewrite frac_auth_frag_validI. by iIntros "[_ $]".
    Qed.
    Lemma test g a : Observe (✓ a) (own g (◯F a)).
    Proof. by apply _. Abort.

    (** Agreement *)
    #[global] Instance own_frac_auth_frac_agreeI g q1 q2 a1 a2 :
      Observe2 (a1 ≡ a2) (own g (●F{q1} a1)) (own g (●F{q2} a2)).
    Proof. GUARD. apply own_2_obs, frac_auth_auth_frac_op_invI. Qed.
    Lemma test g q a1 a2 : Observe2 (a1 ≡ a2) (own g (●F a1)) (own g (●F{q} a2)).
    Proof. by apply _. Abort.

    #[global] Instance own_frac_auth_frac_agree g q1 q2 a1 a2 `{!Discrete a1} :
      Observe2 [| a1 ≡ a2 |] (own g (●F{q1} a1)) (own g (●F{q2} a2)).
    Proof.
      GUARD. apply observe_2_pure, own_2_obs.
      by rewrite frac_auth_auth_frac_op_invI discrete_eq.
    Qed.
    #[global] Instance own_frac_auth_frac_agree_L `{!LeibnizEquiv A} g q1 q2 a1 a2
       `{!Discrete a1} :
      Observe2 [| a1 = a2 |] (own g (●F{q1} a1)) (own g (●F{q2} a2)).
    Proof. GUARD. unfold_leibniz. apply _. Qed.

    #[global] Instance own_frac_auth_agreeI g q a b :
      Observe2 (a ≡ b) (own g (●F{q} a)) (own g (◯F b)).
    Proof. GUARD. apply own_2_obs, frac_auth_auth_frac_agreeI. Qed.
    Lemma test g a b : Observe2 (a ≡ b) (own g (●F a)) (own g (◯F b)).
    Proof. by apply _. Abort.

    #[global] Instance own_frac_auth_agree g q a b `{!Discrete a} :
      Observe2 [| a ≡ b |] (own g (●F{q} a)) (own g (◯F b)).
    Proof.
      GUARD. apply observe_2_pure, own_2_obs.
      by rewrite frac_auth_auth_frac_agreeI discrete_eq.
    Qed.
    #[global] Instance own_frac_auth_agree_L `{!LeibnizEquiv A} g q a b
        `{!Discrete a} :
      Observe2 [| a = b |] (own g (●F{q} a)) (own g (◯F b)).
    Proof. GUARD. unfold_leibniz. apply _. Qed.

    (** Inclusion *)
    #[global] Instance own_frac_auth_both_includedI g q1 q2 a b :
      (** High cost to prefer [Some]-free variant below. *)
      Observe2 (Some b ≼ Some a) (own g (●F{q1} a)) (own g (◯F{q2} b)) | 100.
    Proof.
      GUARD. apply own_2_obs.
      by rewrite frac_auth_auth_frag_includedI.
    Qed.
    #[global] Instance own_frac_auth_both_includedI_discrete `{!CmraDiscrete A}
        g q1 q2 a b :
      (** High cost to prefer [Some]-free variant below. *)
      Observe2 [| Some b ≼ Some a |] (own g (●F{q1} a)) (own g (◯F{q2} b)) | 100.
    Proof.
      GUARD. apply observe_2_pure, own_2_obs.
      by rewrite frac_auth_auth_frag_includedI_discrete.
    Qed.
    #[global] Instance own_frac_auth_both_includedI_total `{!CmraTotal A} g q1 q2 a b :
      Observe2 (b ≼ a) (own g (●F{q1} a)) (own g (◯F{q2} b)).
    Proof.
      GUARD. apply own_2_obs.
      by rewrite frac_auth_auth_frag_includedI_total.
    Qed.
    #[global] Instance own_frac_auth_both_includedI_total_discrete `{!CmraDiscrete A,
        !CmraTotal A} g q1 q2 a b :
      Observe2 [| b ≼ a |] (own g (●F{q1} a)) (own g (◯F{q2} b)).
    Proof.
      GUARD. apply observe_2_pure, own_2_obs.
      by rewrite frac_auth_auth_frag_includedI_total_discrete.
    Qed.

    (** [Fractional] *)
    Import fractional.
    #[global] Instance own_frac_auth_auth_frac g a :
      Fractional (fun q => own g (●F{q} a)).
    Proof.
      GUARD. intros q1 q2. split'.
      - by iIntros "[$ $]".
      - iIntros "[A1 A2]". by iCombine "A1 A2" as "$".
    Qed.
    #[global] Instance own_frac_auth_frag_frac g a `{!CoreId a} :
      Fractional (fun q => own g (◯F{q} a)).
    Proof.
      GUARD. intros q1 q2. split'.
      - by iIntros "[$ $]".
      - iIntros "[A1 A2]". by iCombine "A1 A2" as "$".
    Qed.

  End frac_auth.

  (** iris.algebra.lib.gmap_view *)
  Section gmap_view.
    Context `{Countable K} {V : ofe}. Notation RA := (gmap_viewR K (agreeR V)).
    Context `{!HasOwn RA, !HasOwnValid RA}.
    Implicit Types (k : K) (v : V).
    Implicit Types (m : gmap K (agreeR V)).

    #[global] Instance own_gmap_view_auth_valid g q m :
      Observe [| q ≤ 1 |]%Qp (own g (gmap_view_auth (DfracOwn q) m)).
    Proof.
      GUARD. apply observe_pure, own_obs.
      by rewrite gmap_view_auth_validI.
    Qed.
    #[global] Instance own_gmap_view_auth_valid_2 g q1 q2 m1 m2 :
      Observe2 [| q1 + q2 ≤ 1 |]%Qp
        (own g (gmap_view_auth (DfracOwn q1) m1))
        (own g (gmap_view_auth (DfracOwn q2) m2)).
    Proof.
      GUARD. apply observe_2_pure, own_2_obs.
      rewrite gmap_view_auth_op_validI. by iIntros "[% _]".
    Qed.
    #[global] Instance own_gmap_view_auth_exclusive_l g q m1 m2 :
      Observe2 False (own g (gmap_view_auth (DfracOwn 1) m1)) (own g (gmap_view_auth (DfracOwn q) m2)).
    Proof.
      GUARD. iIntros "M1 M2".
      by iDestruct (own_gmap_view_auth_valid_2 with "M1 M2") as
        %?%Qp.not_add_le_l.
    Qed.
    #[global] Instance own_gmap_view_auth_exclusive_r g q m1 m2 :
      Observe2 False (own g (gmap_view_auth (DfracOwn q) m1)) (own g (gmap_view_auth (DfracOwn 1) m2)).
    Proof.
      GUARD. iIntros "M1 M2".
      by iDestruct (own_gmap_view_auth_valid_2 with "M1 M2") as
        %?%Qp.not_add_le_r.
    Qed.

    #[global] Instance own_gmap_view_frag_valid g k q v :
      Observe [| q ≤ 1 |]%Qp (own g (gmap_view_frag k (DfracOwn q) (to_agree v))).
    Proof.
      GUARD. apply observe_pure, own_obs.
      by rewrite gmap_view_frag_validI.
    Qed.
    #[global] Instance own_gmap_view_frag_valid_2 g k q1 q2 v1 v2 :
      Observe2 [| q1 + q2 ≤ 1 |]%Qp
        (own g (gmap_view_frag k (DfracOwn q1) (to_agree v1)))
        (own g (gmap_view_frag k (DfracOwn q2) (to_agree v1))).
    Proof.
      GUARD. apply observe_2_pure, own_2_obs.
      rewrite gmap_view_frag_op_validI. by iIntros "[% _]".
    Qed.
    #[global] Instance own_gmap_view_frag_exclusive_l g k dq v1 v2 :
      Observe2 False
        (own g (gmap_view_frag k (DfracOwn 1) (to_agree v1)))
        (own g (gmap_view_frag k dq (to_agree v2))).
    Proof.
      GUARD. apply observe_2_pure, own_2_obs.
      rewrite gmap_view_frag_op_validI.
      apply bi.pure_elim_l. by move/exclusive_l.
    Qed.
    #[global] Instance own_gmap_view_frag_exclusive_r g k dq v1 v2 :
      Observe2 False
        (own g (gmap_view_frag k dq (to_agree v1)))
        (own g (gmap_view_frag k (DfracOwn 1) (to_agree v2))).
    Proof.
      GUARD. apply observe_2_pure, own_2_obs.
      rewrite gmap_view_frag_op_validI.
      apply bi.pure_elim_l. by move/exclusive_r.
    Qed.

    Import fractional.
    #[global] Instance own_gmap_view_auth_fractional g m :
      Fractional (fun q => own g (gmap_view_auth (DfracOwn q) m)).
    Proof.
      GUARD. intros q1 q2.
      by rewrite -dfrac_op_own gmap_view_auth_dfrac_op own_op.
    Qed.
    #[global] Instance own_gmap_view_frag_fractional g k v :
      Fractional (fun q => own g (gmap_view_frag k (DfracOwn q) (to_agree v))).
    Proof.
      GUARD. intros q1 q2.
      by rewrite -own_op -gmap_view_frag_op dfrac_op_own agree_idemp.
    Qed.

  End gmap_view.

  (** bluerock.iris.extra.algebra.gset_bij, iris.algebra.lib.gset_bij *)
  Section gset_bij.
    Context `{Countable A, Countable B}. Notation RA := (gset_bijR A B).
    Context `{!HasOwn RA, !HasOwnValid RA}.
    Implicit Types (a : A) (b : B) (L : gset (A * B)).

    #[global] Instance own_gset_bij_auth_bijective g dq L :
      Observe [| gset_bijective L |]%Qp (own g (gset_bij_auth dq L)).
    Proof.
      GUARD. apply observe_pure, own_obs.
      by iIntros ([_ ?]%gset_bij_auth_dfrac_valid).
    Qed.

    #[global] Instance own_gset_bij_auth_frac_valid g q L :
      Observe [| q ≤ 1 |]%Qp (own g (gset_bij_auth (DfracOwn q) L)).
    Proof.
      GUARD. apply observe_pure, own_obs.
      by iIntros ([? _]%gset_bij_auth_dfrac_valid).
    Qed.
    #[global] Instance own_gset_bij_auth_valid_2 g q1 q2 L1 L2 :
      Observe2 [| q1 + q2 ≤ 1 |]%Qp
        (own g (gset_bij_auth (DfracOwn q1) L1))
        (own g (gset_bij_auth (DfracOwn q2) L2)).
    Proof.
      GUARD. apply observe_2_pure, own_2_obs.
      by iIntros ([? _]%gset_bij_auth_dfrac_op_valid).
    Qed.
    #[global] Instance own_gset_bij_auth_exclusive_l g q L1 L2 :
      Observe2 False (own g (gset_bij_auth (DfracOwn 1) L1)) (own g (gset_bij_auth (DfracOwn q) L2)).
    Proof.
      GUARD. iIntros "A1 A2".
      by iDestruct (own_gset_bij_auth_valid_2 with "A1 A2")
        as %?%Qp.not_add_le_l.
    Qed.
    #[global] Instance own_gset_bij_auth_exclusive_r g q L1 L2 :
      Observe2 False (own g (gset_bij_auth (DfracOwn q) L1)) (own g (gset_bij_auth (DfracOwn 1) L2)).
    Proof. GUARD. symmetry. apply _. Qed.

    #[global] Instance own_gset_bij_auth_agree g dq1 dq2 L1 L2 :
      Observe2 [| L1 = L2 |]
        (own g (gset_bij_auth dq1 L1))
        (own g (gset_bij_auth dq2 L2)).
    Proof.
      GUARD. apply observe_2_pure, own_2_obs.
      by iIntros ((_ & ? & _)%gset_bij_auth_dfrac_op_valid).
    Qed.

    Import fractional.
    #[global] Instance own_gset_bij_auth_frac g L :
      Fractional (fun q => own g (gset_bij_auth (DfracOwn q) L)).
    Proof.
      GUARD. intros q1 q2. split'.
      - by iIntros "[$$]".
      - iIntros "[A1 A2]". by iCombine "A1 A2" as "$".
    Qed.

    #[global] Instance own_gset_bij_both_elem_of g dq L a b :
      Observe2 [| (a, b) ∈ L |]
        (own g (gset_bij_auth dq L))
        (own g (gset_bij_elem a b)).
    Proof.
      GUARD. apply observe_2_pure, own_2_obs.
      by iIntros ((_ &_  & ?)%bij_both_dfrac_valid).
    Qed.

    #[global] Instance own_gset_bij_elem_agree g a1 a2 b1 b2 :
      Observe2 [| a1 = a2 <-> b1 = b2 |]
        (own g (gset_bij_elem a1 b1))
        (own g (gset_bij_elem a2 b2)).
    Proof.
      GUARD. apply observe_2_pure, own_2_obs.
      by iIntros (?%gset_bij_elem_agree).
    Qed.
    #[global] Instance own_gset_bij_elem_agree_1 g a b1 b2 :
      Observe2 [| b1 = b2 |]
        (own g (gset_bij_elem a b1))
        (own g (gset_bij_elem a b2)).
    Proof.
      GUARD. iIntros "E1 E2".
      iDestruct (own_gset_bij_elem_agree with "E1 E2") as %[-> _]; auto.
    Qed.
    #[global] Instance own_gset_bij_elem_agree_2 g a1 a2 b :
      Observe2 [| a1 = a2 |]
        (own g (gset_bij_elem a1 b))
        (own g (gset_bij_elem a2 b)).
    Proof.
      GUARD. iIntros "E1 E2".
      iDestruct (own_gset_bij_elem_agree with "E1 E2") as %[_ ->]; auto.
    Qed.
  End gset_bij.

  (** bluerock.iris.extra.algebra.coGset *)
  Section coGset.
    Context `{Countable A, Infinite A}. Notation RA := (coGset_disjR A).
    Context `{!HasOwn RA, !HasOwnValid RA}.
    Implicit Types (X Y : coGset A).

    #[global] Instance own_CoGSet_disjoint g X Y :
      Observe2 [| X ## Y |] (own g (CoGSet X)) (own g (CoGSet Y)).
    Proof. GUARD. rewrite -coGset_disj_valid_op. apply _. Qed.
  End coGset.

End observe.

(** * Planning *)
(** It's unfortunate that all of the preceding observations have the
form "observe something from [own g x]". That's a lot of boilerplate,
especially if we scale up to all observations we want in practice from
the RAs we use. We _can_ eliminate that boilerplate. Perhaps we want:

- For external validity (discrete CMRAs), [ObserveValid {A : cmra} (Q
  : Prop) (x : A) : Prop := ✓ x → Q x], [ObserveValid2 := ... ✓ (x ⋅
  y) → Q x y] with a single instance lifting these to [Observe],
  [Observe2] instances in terms of [own g].

  This lets us cut down the boilerplate for: exclusivity properties,
  agreement properties, and side-conditions on CMRAs with
  restrictions. Also, [ObserveValid] has nothing to do with BIs, so
  its instances can live alongside the algebras themselves without
  seeming "off".

- We should be able to marry the preceding with the algebraic
  typeclasses [Exclusive], [IdFree] to get, once and for all, a large
  class of observations of [False] from ownership.

  We'd need no custom instances for owning [Excl x] or [1 : Qp], for
  example, nor any for exclusivity that follows from the various
  [auth] wrappers.

- (Optional) For internal validity (general CMRAs), analogs
  [ObserveValidI], [ObserveValidI2]. Step-indexed ghost state is rare,
  so this may not be as big a deal.

- For external inclusions (discrete CMRAs), [ObserveIncluded {A} (Q :
  Prop) (x y : A) : Prop := ✓ (x ⋅ y) → x ≼ y → Q x y], again with a
  single [Observe2] instance.

  This gives us agreement axioms from [auth] and the various algebraic
  libraries that bake it in. Audit the various [XXX_included]
  lemmas---there may be other juicy targets.

The observation framework sketched above seems pretty useful, but it
accounts for neither updates nor local updates. Updates require a lot
of manual steps: get your goal into the form [own g x |-- |={E}=> P]
and then [iMod] and then apply a lot of (say) local update rules.

- (Low-hanging fruit) I suspect we can lift the first stage (exposing
  ownership) past [_at], [_offsetR], [pureR] and friends with a few
  proofmode instances. Maybe we already have those and I missed them.

- (Unclear) Could [local_update] usefully be wrapped into a typeclass,
  letting TC resolution take care of some of the boilerplate in the
  third stage? I suspect the answer is "no" because updates can
  involve interesting side-conditions, but that's just a guess based
  on past experience with manual proofs. *)
