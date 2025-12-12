(*
 * Copyright (c) 2021 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import iris.bi.monpred.
Require Import bluerock.iris.extra.proofmode.proofmode.
Require Import iris.proofmode.monpred.

Require Import bluerock.iris.extra.bi.only_provable.

Set Default Proof Using "Type".
Set Suggest Proof Using.

(** WeaklyObjective *)
(** General monPreds are only monotone w.r.t one direction of ⊑. WeaklyObjective
  also says that the monPred P is also monotone w.r.t. to the other direction.
  Effectively, P holds the same for each equivalent class of bi-indexes.
  WeaklyObjective is weaker than Objective, where it is required that P holds
  the same everywhere (recall that the bi-indexes only have a partial order). *)
Class WeaklyObjective {I} {PROP} (P: monPred I PROP) :=
  weakly_objective i j : j ⊑ i → P i ⊢ P j.
Arguments WeaklyObjective {_ _} _%_I.
Arguments weakly_objective {_ _} _%_I {_}.
#[global] Hint Mode WeaklyObjective ! + ! : typeclass_instances.
#[global] Instance : Params (@WeaklyObjective) 2 := {}.

#[global] Hint Extern 200 (WeaklyObjective (match ?x with | _ => _ end)) =>
  destruct x : typeclass_instances.

(** [WeaklyObjectiveN] states that predicate [P] taking [N] arguments is [WeaklyObjective] *)
Notation WeaklyObjective1 P := (∀ a, WeaklyObjective (P a)).
Notation WeaklyObjective2 P := (∀ a b, WeaklyObjective (P a b)).
Notation WeaklyObjective3 P := (∀ a b c, WeaklyObjective (P a b c)).
Notation WeaklyObjective4 P := (∀ a b c d, WeaklyObjective (P a b c d)).
Notation WeaklyObjective5 P := (∀ a b c d e, WeaklyObjective (P a b c d e)).

(* TODO: upstream *)
Bind Scope bi_scope with monPred.

Section weakly_obj.
  Context {I : biIndex} {PROP : bi}.

  Notation monPred := (monPred I PROP).
  Implicit Types (P Q : monPred).

  #[global] Instance symmetric_weakly_objective P :
    Symmetric (@sqsubseteq I _) → WeaklyObjective P.
  Proof. by intros ??? ->. Qed.

  #[global] Instance objective_weakly_objective P :
    Objective P → WeaklyObjective P.
  Proof. intros ????. by rewrite objective_at. Qed.

  #[global] Instance weakly_objective_mono :
    Proper (equiv ==> impl) (@WeaklyObjective I PROP).
  Proof. intros P1 P2 HP ? i j ?. by rewrite -HP weakly_objective. Qed.
  #[global] Instance weakly_objective_flip_mono :
    Proper (equiv ==> flip impl) (@WeaklyObjective I PROP).
  Proof. intros P1 P2 HP ? i j ?. by rewrite HP weakly_objective. Qed.
  #[global] Instance weakly_objective_proper :
    Proper (equiv ==> iff) (@WeaklyObjective I PROP).
  Proof.
    intros P Q EQ. split.
    - by apply weakly_objective_mono.
    - by apply weakly_objective_flip_mono.
  Qed.

  #[global] Instance embed_weakly_objective (P : PROP) : @WeaklyObjective I PROP ⎡P⎤.
  Proof. intros ??. by rewrite !monPred_at_embed. Qed.
  #[global] Instance pure_weakly_objective φ : @WeaklyObjective I PROP ⌜φ⌝.
  Proof. intros ??. by rewrite !monPred_at_pure. Qed.
  #[global] Instance only_provable_weakly_objective φ : @WeaklyObjective I PROP [|φ|].
  Proof. intros ??. by rewrite !monPred_at_only_provable. Qed.
  #[global] Instance emp_weakly_objective : @WeaklyObjective I PROP emp.
  Proof. intros ??. by rewrite !monPred_at_emp. Qed.

  #[global] Instance and_weakly_objective P Q
    `{!WeaklyObjective P, !WeaklyObjective Q} : WeaklyObjective (P ∧ Q).
  Proof. intros i j Lej. by rewrite !monPred_at_and -!(weakly_objective _ i). Qed.
  #[global] Instance or_weakly_objective P Q
    `{!WeaklyObjective P, !WeaklyObjective Q} : WeaklyObjective (P ∨ Q).
  Proof. intros i j Lej. by rewrite !monPred_at_or !(weakly_objective _ i). Qed.

  #[global] Instance impl_weakly_objective P Q
    `{!WeaklyObjective P, !WeaklyObjective Q} : WeaklyObjective (P → Q).
  Proof.
    intros i j Lej.
    rewrite !monPred_at_impl. apply bi.forall_intro=> i'.
    rewrite bi.pure_impl_forall. apply bi.forall_intro=>Le.
    rewrite (weakly_objective P _ _ Le) Lej -Le -(weakly_objective Q _ _ Lej).
    by rewrite (bi.forall_elim i) bi.pure_impl_forall bi.forall_elim //.
  Qed.

  #[global] Instance forall_weakly_objective {A} Φ {H : ∀ x : A, WeaklyObjective (Φ x)} :
    @WeaklyObjective I PROP (∀ x, Φ x)%I.
  Proof.
    intros i j Lej. rewrite !monPred_at_forall.
    apply bi.forall_intro => x. rewrite -(weakly_objective _ i) //. eauto.
  Qed.
  #[global] Instance exists_weakly_objective {A} Φ {H : ∀ x : A, WeaklyObjective (Φ x)} :
    @WeaklyObjective I PROP (∃ x, Φ x)%I.
  Proof.
    intros i j Lej. rewrite !monPred_at_exist.
    apply bi.exist_elim => x. rewrite (weakly_objective _ i); eauto.
  Qed.

  #[global] Instance sep_weakly_objective P Q
    `{!WeaklyObjective P, !WeaklyObjective Q} : WeaklyObjective (P ∗ Q).
  Proof. intros i j Lej. by rewrite !monPred_at_sep !(weakly_objective _ i). Qed.

  #[global] Instance wand_weakly_objective P Q
    `{!WeaklyObjective P, !WeaklyObjective Q} : WeaklyObjective (P -∗ Q).
  Proof.
    intros i j Lej.
    rewrite !monPred_at_wand. apply bi.forall_intro=> i'.
    rewrite bi.pure_impl_forall. apply bi.forall_intro=>Le.
    rewrite (weakly_objective P _ _ Le) Lej -Le -(weakly_objective Q _ _ Lej).
    by rewrite (bi.forall_elim i) bi.pure_impl_forall bi.forall_elim //.
  Qed.

  #[global] Instance persistently_weakly_objective P
    `{!WeaklyObjective P} : WeaklyObjective (<pers> P).
  Proof.
    intros i j Lej. by rewrite !monPred_at_persistently !(weakly_objective _ i).
  Qed.

  #[global] Instance affinely_weakly_objective P
    `{!WeaklyObjective P} : WeaklyObjective (<affine> P).
  Proof. rewrite /bi_affinely. apply _. Qed.
  #[global] Instance intuitionistically_weakly_objective P
    `{!WeaklyObjective P} : WeaklyObjective (□ P).
  Proof. rewrite /bi_intuitionistically. apply _. Qed.
  #[global] Instance absorbingly_weakly_objective P
    `{!WeaklyObjective P} : WeaklyObjective (<absorb> P).
  Proof. rewrite /bi_absorbingly. apply _. Qed.
  #[global] Instance persistently_if_weakly_objective P p
    `{!WeaklyObjective P} : WeaklyObjective (<pers>?p P).
  Proof. rewrite /bi_persistently_if. destruct p; apply _. Qed.
  #[global] Instance affinely_if_weakly_objective P p
    `{!WeaklyObjective P} : WeaklyObjective (<affine>?p P).
  Proof. rewrite /bi_affinely_if. destruct p; apply _. Qed.
  #[global] Instance absorbingly_if_weakly_objective P p
    `{!WeaklyObjective P} : WeaklyObjective (<absorb>?p P).
  Proof. rewrite /bi_absorbingly_if. destruct p; apply _. Qed.
  #[global] Instance intuitionistically_if_weakly_objective P p
    `{!WeaklyObjective P} : WeaklyObjective (□?p P).
  Proof. rewrite /bi_intuitionistically_if. destruct p; apply _. Qed.

  #[global] Instance bupd_weakly_objective `{BiBUpd PROP} P
    `{!WeaklyObjective P} : WeaklyObjective (|==> P)%I.
  Proof. intros ???. by rewrite !monPred_at_bupd weakly_objective. Qed.

  #[global] Instance fupd_weakly_objective `{BiFUpd PROP} E1 E2 P
    `{!WeaklyObjective P} : WeaklyObjective (|={E1,E2}=> P)%I.
  Proof. intros ???. by rewrite !monPred_at_fupd weakly_objective. Qed.

  #[global] Instance later_weakly_objective P
    `{!WeaklyObjective P} : WeaklyObjective (▷ P).
  Proof. intros ???. by rewrite !monPred_at_later weakly_objective. Qed.
  #[global] Instance laterN_weakly_objective P
    `{!WeaklyObjective P} n : WeaklyObjective (▷^n P).
  Proof. induction n; apply _. Qed.
  #[global] Instance except0_weakly_objective P
    `{!WeaklyObjective P} : WeaklyObjective (◇ P).
  Proof. rewrite /bi_except_0. apply _. Qed.

  #[global] Instance plainly_weakly_objective `{BiPlainly PROP} P :
    WeaklyObjective (■ P).
  Proof. rewrite monPred_plainly_unfold. apply _. Qed.
  #[global] Instance plainly_if_weakly_objective `{BiPlainly PROP} P p
    `{!WeaklyObjective P} : WeaklyObjective (■?p P).
  Proof. rewrite /plainly_if. destruct p; apply _. Qed.


  Lemma big_sepL_weakly_objective_lookup {A}
    (Φ : nat → A → monPred) (l : list A) :
    (∀ n x, l !! n = Some x → WeaklyObjective (Φ n x)) →
    WeaklyObjective ([∗ list] n↦x ∈ l, Φ n x)%I.
  Proof.
    intros HΦ ???. rewrite !monPred_at_big_sepL.
    apply big_sepL_mono => ?? /HΦ ?. by apply weakly_objective.
  Qed.
  Lemma big_sepM_weakly_objective_lookup `{Countable K} {A}
    (Φ : K → A → monPred) (m : gmap K A) :
    (∀ k x, m !! k = Some x → WeaklyObjective (Φ k x)) →
    WeaklyObjective ([∗ map] k↦x ∈ m, Φ k x)%I.
  Proof.
    intros HΦ ???. rewrite !monPred_at_big_sepM.
    apply big_sepM_mono => ?? /HΦ ?. by apply weakly_objective.
  Qed.
  Lemma big_sepS_weakly_objective_elem_of `{Countable A}
    (Φ : A → monPred) (X : gset A) :
    (∀ y, y ∈ X → WeaklyObjective (Φ y)) →
    WeaklyObjective ([∗ set] y ∈ X, Φ y)%I.
  Proof.
    intros HΦ ???. rewrite !monPred_at_big_sepS.
    apply big_sepS_mono => ? /HΦ ?. by apply weakly_objective.
  Qed.
  Lemma big_sepMS_weakly_objective_elem_of `{Countable A}
    (Φ : A → monPred) (X : gmultiset A) :
    (∀ y, y ∈ X → WeaklyObjective (Φ y)) →
    WeaklyObjective ([∗ mset] y ∈ X, Φ y)%I.
  Proof.
    intros HΦ ???. rewrite !monPred_at_big_sepMS.
    apply big_sepMS_mono => ? /HΦ ?. by apply weakly_objective.
  Qed.

  Lemma big_sepL2_weakly_objective_lookup {A B}
    (Φ : nat → A → B → monPred) (l : list A) (k : list B) :
    (∀ n x y, l !! n = Some x → k !! n = Some y → WeaklyObjective (Φ n x y)) →
    WeaklyObjective ([∗ list] n↦x; y ∈ l; k, Φ n x y)%I.
  Proof.
    intros HW. rewrite big_sepL2_alt.
    apply /and_weakly_objective /big_sepL_weakly_objective_lookup.
    move => n [x y] /= /lookup_zip_with_Some [_] [_] [] [<- <-] [].
    apply HW.
  Qed.

  #[global] Instance big_sepL_weakly_objective {A}
    (Φ : nat → A → monPred) (l : list A) `{∀ n x, WeaklyObjective (Φ n x)} :
    WeaklyObjective ([∗ list] n↦x ∈ l, Φ n x)%I.
  Proof. by apply big_sepL_weakly_objective_lookup, _. Qed.
  #[global] Instance big_sepM_weakly_objective `{Countable K} {A}
    (Φ : K → A → monPred) (m : gmap K A) `{∀ k x, WeaklyObjective (Φ k x)} :
    WeaklyObjective ([∗ map] k↦x ∈ m, Φ k x)%I.
  Proof. by apply big_sepM_weakly_objective_lookup, _. Qed.
  #[global] Instance big_sepS_weakly_objective `{Countable A}
    (Φ : A → monPred) (X : gset A) `{∀ y, WeaklyObjective (Φ y)} :
    WeaklyObjective ([∗ set] y ∈ X, Φ y)%I.
  Proof. by apply big_sepS_weakly_objective_elem_of, _. Qed.
  #[global] Instance big_sepMS_weakly_objective `{Countable A}
    (Φ : A → monPred) (X : gmultiset A) `{∀ y, WeaklyObjective (Φ y)}:
    WeaklyObjective ([∗ mset] y ∈ X, Φ y)%I.
  Proof. by apply big_sepMS_weakly_objective_elem_of, _. Qed.

  #[global] Instance big_sepL2_weakly_objective {A B}
    (Φ : nat → A → B → monPred) (l : list A) (k : list B)
    `{∀ n x y, WeaklyObjective (Φ n x y)} :
    WeaklyObjective ([∗ list] n↦x; y ∈ l; k, Φ n x y)%I.
  Proof. by apply big_sepL2_weakly_objective_lookup, _. Qed.
End weakly_obj.
