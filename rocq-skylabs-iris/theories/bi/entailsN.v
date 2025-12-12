(*
 * Copyright (c) 2021 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import iris.bi.bi.
Require Import iris.bi.extensions.
Require Export bluerock.iris.extra.bi.prelude.

(** * Step-indexed entailment *)
(** We axiomatize a generalization [P ⊢{n} Q] of Iris entailment that
satisfies

- [(P ⊢ Q) ↔ ∀ n, P ⊢{n} Q]

- [P ≡{n}≡ Q ↔ (P ⊢{n} Q) ∧ (Q ⊢{n} P)]

This generalization gives us a proof technique for lemmas of the form
[∃ x : A, P x ≡{n}≡ ∃ y : B, Q y] where the two sides quantify over
different types.

The cost of this generalization is that, at least for the particular
[P]s and [Q]s we care about, we have to restate the usual introduction
and elimination rules of the BI connectives in terms of [⊢{n}], prove
such connectives monotone, et cetera.

Another cost derives from the fact that the IPM is based on [⊢], so
proofs about [⊢{n}] involve more manual reasoning than IPM-based
proofs.

Note: We're defining the interface lazily. It covers only those
connectives we've needed. It could easily be fleshed out to cover
everything in Iris. *)

Reserved Notation "P '⊢{' n } Q"
  (at level 99, n at next level, Q at level 200, right associativity,
   format "'[' P  '/' '⊢{' n '}'  Q ']'").
Reserved Notation "P '⊢@{' PROP , n } Q"
  (at level 99, PROP, n at next level, Q at level 200,
   right associativity).
Reserved Notation "'(⊢{' n } )".
Reserved Notation "'(⊢@{' PROP , n } )".
Reserved Notation "P '⊣⊢{' n } Q"
  (at level 95, n at next level, no associativity,
   format "'[' P  '/' '⊣⊢{' n '}'  Q ']'").
Reserved Notation "P '⊣⊢@{' PROP , n } Q"
  (at level 95, PROP, n at next level, no associativity).

Reserved Notation "'⊢{' n } Q"
  (at level 20, n at next level, Q at level 200, format "'⊢{' n }  Q").
Reserved Notation "'⊢@{' PROP , n } Q"
  (at level 20, PROP, n at next level, Q at level 200).
(** Force left-factoring. See iris.bi.notation. *)
Reserved Notation "'(⊢@{' PROP , n } Q )".

Class EntailsN (PROP : Type) : Type := entailsN (n : nat) : relation PROP.
#[global] Instance : Params (@entailsN) 3 := {}.
#[global] Hint Mode EntailsN ! : typeclass_instances.
#[global] Arguments entailsN {_}%_type_scope {_} _%_nat_scope (_ _)%_bi_scope : assert.

Notation "P '⊢{' n } Q" := (entailsN n P Q) : stdpp_scope.
Notation "P '⊢@{' PROP , n } Q" :=
  (@entailsN PROP _ n P Q) (only parsing) : stdpp_scope.
Notation "'(⊢{' n } )" := (entailsN n) (only parsing) : stdpp_scope.
Notation "'(⊢@{' PROP , n } )" :=
  (@entailsN PROP _ n) (only parsing) : stdpp_scope.
Notation "P '⊣⊢{' n } Q" := ((P ⊢{n} Q) ∧ (Q ⊢{n} P)) : stdpp_scope.
Notation "P '⊣⊢@{' PROP , n } Q" :=
  ((P ⊢@{PROP,n} Q) ∧ (Q ⊢@{PROP,n} P)) (only parsing) : stdpp_scope.

(** Incomplete mixin. Extend as needed, but please use additional
mixins for things like, e.g., [bi_later] and [fupd] in order to follow
the Iris mixin structure.

Notice that many primitive laws in [iris.bi.interface] follow from
[entails_entailsN], [dist_entailsN] and do not need to be axiomatized.
*)
Section mixin.
  Context (PROP : bi) `{EntailsN PROP}.
  Implicit Types P Q : PROP.

  Record BiEntailsNMixin : Prop := {
    bi_entailsN_mixin_entailsN_trans P Q R n : (P ⊢{n} Q) → (Q ⊢{n} R) → (P ⊢{n} R);
    bi_entailsN_mixin_entails_entailsN P Q : (P ⊢ Q) ↔ ∀ n, P ⊢{n} Q;
    bi_entailsN_mixin_dist_entailsN P Q n : P ≡{n}≡ Q ↔ (P ⊣⊢{n} Q);

    (** HOL: [bi_pure], [bi_and], [bi_or], [bi_impl], [bi_forall], [bi_exist] *)
    bi_entailsN_mixin_pure_elimN' (P : Prop) Q n : (P → True ⊢{n} Q) → ⌜P⌝ ⊢{n} Q;
    bi_entailsN_mixin_and_introN P Q R n : (P ⊢{n} Q) → (P ⊢{n} R) → P ⊢{n} Q ∧ R;
    bi_entailsN_mixin_impl_introN_r P Q R n : (P ∧ Q ⊢{n} R) → P ⊢{n} Q → R;
    bi_entailsN_mixin_forall_introN {A} P (Q : A → PROP) n :
      (∀ a, P ⊢{n} Q a) → (P ⊢{n} ∀ a, Q a);
    bi_entailsN_mixin_exist_elimN {A} (P : A → PROP) Q n :
      (∀ a, P a ⊢{n} Q) → (∃ a, P a) ⊢{n} Q;

    (** BI: [bi_sep], [bi_emp], [bi_wand] *)
    bi_entailsN_mixin_sep_monoN P P' Q Q' n :
      (P ⊢{n} Q) → (P' ⊢{n} Q') → (P ∗ P' ⊢{n} Q ∗ Q');
    bi_entailsN_mixin_wand_introN_r P Q R n : (P ∗ Q ⊢{n} R) → P ⊢{n} Q -∗ R;

    (** Modalities: [bi_persistently] *)
  }.
End mixin.

Class BiEntailsN (PROP : bi) : Type := {
  #[global] bi_entailsN_entailsN :: EntailsN PROP;
  bi_entailsN_mixin : BiEntailsNMixin PROP;
}.
#[global] Hint Mode BiEntailsN ! : typeclass_instances.
#[global] Arguments bi_entailsN_entailsN : simpl never.

(** Projecting properties from the mixin. *)
Section properties.
  Context `{BiEntailsN PROP}.
  Implicit Types P Q : PROP.

  Lemma entailsN_trans P Q R n : (P ⊢{n} Q) → (Q ⊢{n} R) → (P ⊢{n} R).
  Proof. apply bi_entailsN_mixin_entailsN_trans, bi_entailsN_mixin. Qed.
  Lemma entails_entailsN P Q : (P ⊢ Q) ↔ ∀ n, P ⊢{n} Q.
  Proof. apply bi_entailsN_mixin_entails_entailsN, bi_entailsN_mixin. Qed.
  Lemma dist_entailsN P Q n : P ≡{n}≡ Q ↔ (P ⊣⊢{n} Q).
  Proof. apply bi_entailsN_mixin_dist_entailsN, bi_entailsN_mixin. Qed.

  Lemma pure_elimN' (P : Prop) Q n : (P → True ⊢{n} Q) → ⌜P⌝ ⊢{n} Q.
  Proof. apply bi_entailsN_mixin_pure_elimN', bi_entailsN_mixin. Qed.
  Lemma and_introN P Q R n : (P ⊢{n} Q) → (P ⊢{n} R) → P ⊢{n} Q ∧ R.
  Proof. apply bi_entailsN_mixin_and_introN, bi_entailsN_mixin. Qed.
  Lemma impl_introN_r P Q R n : (P ∧ Q ⊢{n} R) → P ⊢{n} Q → R.
  Proof. apply bi_entailsN_mixin_impl_introN_r, bi_entailsN_mixin. Qed.
  Lemma forall_introN {A} P (Q : A → PROP) n : (∀ a, P ⊢{n} Q a) → (P ⊢{n} ∀ a, Q a).
  Proof. apply bi_entailsN_mixin_forall_introN, bi_entailsN_mixin. Qed.
  Lemma exist_elimN {A} (P : A → PROP) Q n : (∀ a, P a ⊢{n} Q) → (∃ a, P a) ⊢{n} Q.
  Proof. apply bi_entailsN_mixin_exist_elimN, bi_entailsN_mixin. Qed.

  Lemma sep_monoN P P' Q Q' n : (P ⊢{n} Q) → (P' ⊢{n} Q') → (P ∗ P' ⊢{n} Q ∗ Q').
  Proof. apply bi_entailsN_mixin_sep_monoN, bi_entailsN_mixin. Qed.
  Lemma wand_introN_r P Q R n : (P ∗ Q ⊢{n} R) → P ⊢{n} Q -∗ R.
  Proof. apply bi_entailsN_mixin_wand_introN_r, bi_entailsN_mixin. Qed.
End properties.

Definition emp_validN `{BiEntailsN PROP} (n : nat) (P : PROP) : Prop :=
  emp ⊢{n} P.
#[global] Arguments emp_validN {_ _} _%_nat_scope _%_I : simpl never, assert.
#[global] Hint Opaque emp_validN : typeclass_instances.

Notation "'⊢{' n } Q" := (emp_validN n Q) : stdpp_scope.
Notation "'⊢@{' PROP , n } Q" := (@emp_validN PROP _ n Q)
  (only parsing) : stdpp_scope.
Notation "'(⊢@{' PROP , n } Q )" := (@emp_validN PROP _ n Q)
  (only parsing) : stdpp_scope.

#[global] Instance entailsN_rewrite_relation `{BiEntailsN PROP} n :
  RewriteRelation (⊢@{PROP,n}) := {}.

(** The following theory is incomplete. Extend as needed. To use a
connective under [⊢{n}], you generally need its introduction rules,
elimination rules, and monotonicity properties. *)
Section theory.
  Context `{BiEntailsN PROP}.
  Implicit Types P Q : PROP.
  Notation "'(⊢{' n } )" := (⊢@{PROP,n}) (only parsing).

  #[global] Instance entailsN_po n : PreOrder (⊢@{PROP,n}).
  Proof.
    split.
    - intros P. by apply entails_entailsN.
    - repeat intro. by eapply entailsN_trans.
  Qed.

  (** Rewriting *)
  #[global] Instance: Params (@entailsN) 3 := {}.
  Lemma entailsN_ne n : Proper (dist n ==> dist n ==> iff) (⊢{n}).
  Proof.
    intros P1 P2 [HP1 HP2]%dist_entailsN.
    intros Q1 Q2 [HQ1 HQ2]%dist_entailsN.
    split=>?. by rewrite HP2 -HQ1. by rewrite HP1 -HQ2.
  Qed.
  #[global] Instance entailsN_proper n : Proper (equiv ==> equiv ==> iff) (⊢{n}).
  Proof. repeat intro. apply entailsN_ne; by apply equiv_dist. Qed.

  #[global] Instance: Params (@emp_validN) 3 := {}.
  #[global] Instance emp_validN_proper n :
    Proper (equiv ==> iff) (@emp_validN PROP _ n).
  Proof. exact: entailsN_proper. Qed.

  (** [bi_pure] *)
  Lemma True_introN P n : P ⊢{n} True.
  Proof. apply entails_entailsN, bi.True_intro. Qed.
  Lemma False_elimN P n : False ⊢{n} P.
  Proof. apply entails_entailsN, bi.False_elim. Qed.
  Lemma pure_introN (P : Prop) Q n : P → Q ⊢{n} ⌜P⌝.
  Proof. intros. by apply entails_entailsN, bi.pure_intro. Qed.
  Lemma pure_monoN (P Q : Prop) n : (P → Q) → (⌜P⌝ ⊢@{PROP,n} ⌜Q⌝).
  Proof. intros. by apply entails_entailsN, bi.pure_mono. Qed.
  #[global] Instance pure_monoN' n : Proper (impl ==> (⊢{n})) bi_pure.
  Proof. repeat intro. by apply pure_monoN. Qed.
  #[global] Instance pure_flip_monoN n : Proper (impl --> flip (⊢{n})) bi_pure.
  Proof. repeat intro. by apply pure_monoN. Qed.

  (** [bi_and] *)
  Lemma and_elimN_r P Q n : P ∧ Q ⊢{n} Q.
  Proof. apply entails_entailsN, bi.and_elim_r. Qed.
  Lemma and_elimN_l P Q n : P ∧ Q ⊢{n} P.
  Proof. apply entails_entailsN, bi.and_elim_l. Qed.
  Lemma and_mono P P' Q Q' n : (P ⊢{n} Q) → (P' ⊢{n} Q') → P ∧ P' ⊢{n} Q ∧ Q'.
  Proof.
    intros. apply and_introN.
    - by etrans; first apply and_elimN_l.
    - by etrans; first apply and_elimN_r.
  Qed.
  Lemma and_monoN_r P P' Q' n : (P' ⊢{n} Q') → (P ∧ P' ⊢{n} P ∧ Q').
  Proof. intros. by apply and_mono. Qed.
  Lemma and_monoN_l P P' Q n : (P ⊢{n} Q) → (P ∧ P' ⊢{n} Q ∧ P').
  Proof. intros. by apply and_mono. Qed.
  #[global] Instance and_monoN n : Proper ((⊢{n}) ==> (⊢{n}) ==> (⊢{n})) bi_and.
  Proof. repeat intro. by apply and_mono. Qed.
  #[global] Instance uPred_and_flip_monoN n :
    Proper ((⊢{n}) --> (⊢{n}) --> flip (⊢{n})) bi_and.
  Proof. repeat intro. by apply and_mono. Qed.

  (** [bi_impl] *)
  Lemma impl_introN_l P Q R n : (Q ∧ P ⊢{n} R) → (P ⊢{n} Q → R).
  Proof. rewrite comm. apply impl_introN_r. Qed.
  Lemma impl_elimN_r P Q n : (P ∧ (P → Q)) ⊢{n} Q.
  Proof. apply entails_entailsN, bi.impl_elim_r. Qed.
  Lemma impl_elimN_r' P Q R n : (Q ⊢{n} P → R) → (P ∧ Q ⊢{n} R).
  Proof. intros ->. apply impl_elimN_r. Qed.
  Lemma impl_elimN_l P Q n : ((P → Q) ∧ P) ⊢{n} Q.
  Proof. apply entails_entailsN, bi.impl_elim_l. Qed.
  Lemma impl_elimN_l' P Q R n : (P ⊢{n} Q → R) → (P ∧ Q ⊢{n} R).
  Proof. intros ->. apply impl_elimN_l. Qed.
  Lemma impl_elimN P Q R n : (P ⊢{n} Q → R) → (P ⊢{n} Q) → (P ⊢{n} R).
  Proof.
    intros HR HQ. trans (P ∧ P)%I; first by apply and_introN.
    rewrite {1}HQ HR. apply impl_elimN_r.
  Qed.
  Lemma impl_monoN P P' Q Q' n : (Q ⊢{n} P) → (P' ⊢{n} Q') → (P → P') ⊢{n} (Q → Q').
  Proof. intros HQ HP. apply impl_introN_l. rewrite HQ -HP. apply impl_elimN_r. Qed.
  #[global] Instance impl_monoN' n : Proper ((⊢{n}) --> (⊢{n}) ==> (⊢{n})) bi_impl.
  Proof. repeat intro. by apply impl_monoN. Qed.
  #[global] Instance impl_flip_monoN' n :
    Proper ((⊢{n}) ==> (⊢{n}) --> flip (⊢{n})) bi_impl.
  Proof. repeat intro. by apply impl_monoN. Qed.
  Lemma pure_implN_1 (P Q : Prop) n : ⌜P → Q⌝ ⊢@{PROP,n} ⌜P⌝ → ⌜Q⌝.
  Proof. apply entails_entailsN, bi.pure_impl_1. Qed.
  Lemma pure_implN_2 `{!BiPureForall PROP} (P Q : Prop) n :
    (⌜P⌝ → ⌜Q⌝) ⊢@{PROP,n} ⌜P → Q⌝.
  Proof. apply entails_entailsN, bi.pure_impl_2. Qed.
  Lemma entailsN_impl P Q n : (P ⊢{n} Q) → ⊢{n} P → Q.
  Proof. intros HP. apply impl_introN_r. rewrite HP. apply and_elimN_r. Qed.
  Lemma impl_entailsN P Q n `{!Affine P} : ( ⊢{n} P → Q ) → P ⊢{n} Q.
  Proof. intros. rewrite -(bi.emp_and P). by apply impl_elimN_l'. Qed.
  Lemma entailsN_impl_True P Q n : (P ⊢{n} Q) ↔ (True ⊢{n} P → Q).
  Proof.
    split.
    - intros <-. apply entails_entailsN. by rewrite -bi.entails_impl_True.
    - intros. rewrite -[P](left_id True%I bi_and). by apply impl_elimN_l'.
  Qed.
  Lemma entailsN_eq_True P Q n : (P ⊢{n} Q) ↔ ((P → Q) ⊣⊢{n} True).
  Abort.

  (** [bi_forall] *)
  Lemma forall_elimN {A} (P : A → PROP) a n : (∀ a, P a) ⊢{n} P a.
  Proof. apply entails_entailsN, bi.forall_elim. Qed.
  Lemma forall_elim {A} P (Q : A → PROP) n : (P ⊢{n} ∀ a, Q a) → ∀ a, P ⊢{n} Q a.
  Proof. intros HP a. rewrite HP. apply forall_elimN. Qed.
  Lemma forall_monoN {A} (P Q : A → PROP) n :
    (∀ a, P a ⊢{n} Q a) → (∀ a, P a) ⊢{n} (∀ a, Q a).
  Proof.
    intros HP. apply forall_introN=>a. rewrite -(HP a). apply forall_elimN.
  Qed.
  #[global] Instance forall_monoN' {A} n :
    Proper (pointwise_relation A (⊢{n}) ==> (⊢{n})) bi_forall.
  Proof. repeat intro. by apply forall_monoN. Qed.
  #[global] Instance forall_flip_monoN' {A} n :
    Proper (pointwise_relation A (flip (⊢{n})) ==> flip (⊢{n})) bi_forall.
  Proof. repeat intro. by apply forall_monoN. Qed.

  (** [bi_exist] *)
  Lemma exist_introN {A} (P : A → PROP) a n : P a ⊢{n} ∃ a, P a.
  Proof. apply entails_entailsN, bi.exist_intro. Qed.
  Lemma exist_introN' {A} P (Q : A → PROP) a n : (P ⊢{n} Q a) → P ⊢{n} ∃ a, Q a.
  Proof. etrans; eauto using exist_introN. Qed.
  Lemma exist_monoN {A} (P Q : A → PROP) n :
    (∀ a : A, P a ⊢{n} Q a) → (∃ a, P a) ⊢{n} ∃ a, Q a.
  Proof. intros. apply exist_elimN=>a. exact: exist_introN'. Qed.
  #[global] Instance exist_monoN' {A} n :
    Proper (pointwise_relation A (⊢{n}) ==> (⊢{n})) bi_exist.
  Proof. repeat intro. by apply exist_monoN. Qed.
  #[global] Instance uPred_exist_flip_monoN' {A} n :
    Proper (pointwise_relation A (flip (⊢{n})) ==> flip (⊢{n})) bi_exist.
  Proof. repeat intro. by apply exist_monoN. Qed.

  (** [bi_sep] *)
  Lemma sep_monoN_l P P' Q' n : (P' ⊢{n} Q') → P ∗ P' ⊢{n} P ∗ Q'.
  Proof. intros. by eapply sep_monoN. Qed.
  Lemma sep_monoN_r P P' Q n : (P ⊢{n} Q) → P ∗ P' ⊢{n} Q ∗ P'.
  Proof. intros. by eapply sep_monoN. Qed.
  #[global] Instance sep_monoN' n : Proper ((⊢{n}) ==> (⊢{n}) ==> (⊢{n})) bi_sep.
  Proof. repeat intro. by apply sep_monoN. Qed.
  #[global] Instance sep_flip_monoN' n :
    Proper ((⊢{n}) --> (⊢{n}) --> flip (⊢{n})) bi_sep.
  Proof. repeat intro. by apply sep_monoN. Qed.

  (** [bi_emp] *)
  Lemma emp_sep_1N P n : P ⊢{n} emp ∗ P.
  Proof. apply entails_entailsN, bi.emp_sep_1. Qed.
  Lemma emp_sep_2N P n : emp ∗ P ⊢{n} P.
  Proof. apply entails_entailsN, bi.emp_sep_2. Qed.

  (** [bi_wand] *)
  Lemma wand_elimN_l' P Q R n : (P ⊢{n} Q -∗ R) → (P ∗ Q ⊢{n} R).
  Proof. intros ->. apply entails_entailsN, bi.wand_elim_l. Qed.
  Lemma wand_elimN_r' P Q R n : (Q ⊢{n} P -∗ R) → (P ∗ Q ⊢{n} R).
  Proof. intros. rewrite comm. by apply wand_elimN_l'. Qed.
  Lemma wand_elimN_r P Q n : P ∗ (P -∗ Q) ⊢{n} Q.
  Proof. by etrans; last by apply wand_elimN_r'. Qed.
  Lemma wand_elimN_l P Q n : (P -∗ Q) ∗ P ⊢{n} Q.
  Proof. by etrans; last by apply wand_elimN_l'. Qed.
  Lemma wand_introN_l P Q R n : (Q ∗ P ⊢{n} R) → P ⊢{n} Q -∗ R.
  Proof. intros. apply wand_introN_r. by rewrite comm. Qed.
  Lemma wand_monoN P P' Q Q' n : (Q ⊢{n} P) → (P' ⊢{n} Q') → (P -∗ P') ⊢{n} (Q -∗ Q').
  Proof.
    intros HQP HPQ. apply wand_introN_r. rewrite HQP -HPQ. by apply wand_elimN_l'.
  Qed.
  #[global] Instance wand_monoN' n : Proper ((⊢{n}) --> (⊢{n}) ==> (⊢{n})) bi_wand.
  Proof. repeat intro. by apply wand_monoN. Qed.
  #[global] Instance wand_flip_monoN' n :
    Proper ((⊢{n}) ==> (⊢{n}) --> flip (⊢{n})) bi_wand.
  Proof. repeat intro. by apply wand_monoN. Qed.

  (** [bi_persitently] *)
  Lemma persistently_forall_2N `{BiPersistentlyForall PROP} {A} (P : A → PROP) n :
    (∀ a, <pers> P a) ⊢{n} <pers> (∀ a, P a).
  Proof. apply entails_entailsN, persistently_forall_2. Qed.

  (** [bi_later] *)
  Lemma later_forall_2N {A} (P : A → PROP) n : (∀ a, ▷ P a) ⊢{n} ▷ (∀ a, P a).
  Proof. apply entails_entailsN, bi.later_forall_2. Qed.

  (** [bi_affinely] *)
  Lemma affinely_monoN P Q n : (P ⊢{n} Q) → (<affine> P ⊢{n} <affine> Q).
  Proof. rewrite /bi_affinely. by intros ->. Qed.
  #[global] Instance affinely_monoN' n : Proper ((⊢{n}) ==> (⊢{n})) bi_affinely.
  Proof. repeat intro. by apply affinely_monoN. Qed.
  #[global] Instance affinely_flip_monoN' n :
    Proper ((⊢{n}) --> flip (⊢{n})) bi_affinely.
  Proof. repeat intro. by apply affinely_monoN. Qed.
  Lemma affinely_idempN P n : <affine> <affine> P ⊣⊢{n} <affine> P.
  Proof. apply dist_entailsN. by rewrite bi.affinely_idemp. Qed.
  Lemma affinely_introN' P Q n : (<affine> P ⊢{n} Q) → (<affine> P ⊢{n} <affine> Q).
  Proof. intros <-. apply affinely_idempN. Qed.
  Lemma affinely_introN P Q n `{!Affine P} : (P ⊢{n} Q) → (P ⊢{n} <affine> Q).
  Proof. intros <-. by apply entails_entailsN, bi.affinely_intro. Qed.
  Lemma affinely_elimN P n : <affine> P ⊢{n} P.
  Proof. apply entails_entailsN, bi.affinely_elim. Qed.
  Lemma afifnely_elimN_emp P n : <affine> P ⊢{n} emp.
  Proof. apply entails_entailsN, bi.affinely_elim_emp. Qed.

  (** [only_provable] *)
  Lemma only_provable_introN (P : Prop) Q `{!Affine Q} n : P → Q ⊢{n} [| P |].
  Proof. rewrite only_provable_unfold => HP. apply: affinely_introN. exact: pure_introN. Qed.
  Lemma only_provable_elimN' (P : Prop) Q n : (P → True ⊢{n} Q) → [| P |] ⊢{n} Q.
  Proof. rewrite only_provable_unfold affinely_elimN. exact: pure_elimN'. Qed.
  Lemma only_provable_monoN (P Q : Prop) n : (P → Q) → [| P |] ⊢@{PROP,n} [| Q |].
  Proof. rewrite !only_provable_unfold; intros. by apply affinely_monoN, pure_monoN. Qed.
  #[global] Instance only_provable_monoN' n : Proper (impl ==> (⊢{n})) only_provable.
  Proof. repeat intro. by apply only_provable_monoN. Qed.
  #[global] Instance only_provable_flip_monoN n :
    Proper (impl --> flip (⊢{n})) only_provable.
  Proof. repeat intro. by apply only_provable_monoN. Qed.

End theory.
