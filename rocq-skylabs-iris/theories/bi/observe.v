(*
 * Copyright (c) 2020-2025 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import elpi.apps.locker.locker.
Require Import bluerock.iris.extra.bi.prelude.
Require Import iris.bi.bi iris.bi.monpred.
Require Import bluerock.iris.extra.proofmode.proofmode.

(** * Observations *)
(** We define type classes for making observations and a few instances
lifting those observations through the logic. Additional instances are
defined elsewhere. *)

(** [Observe Q P] means we can observe [Q] (persistently) given [P].
Such observations do not consume [P]. *)
Class Observe {PROP : bi} (Q P : PROP) := observe : P ⊢ <pers> Q.
#[global] Instance: Params (@observe) 1 := {}.
Arguments observe {_} (_ _)%_I {_} : assert.
Arguments Observe {_} (_ _)%_I : simpl never, assert.
#[global] Hint Mode Observe + ! ! : typeclass_instances.

(** [Observe Q P1 P2] means we can observe [Q] (persistently) given
[P1 ** P2]. Such observations do not consume the [P_i]. *)
Class Observe2 {PROP : bi} (Q P1 P2 : PROP) := observe_2 : P1 ⊢ P2 -∗ <pers> Q.
#[global] Instance: Params (@observe_2) 1 := {}.
Arguments observe_2 {_} (_ _ _)%_I {_} : assert.
Arguments Observe2 {_} (_ _ _)%_I : simpl never, assert.
#[global] Hint Mode Observe2 + ! ! ! : typeclass_instances.

(**
Do not extend this module. It exists for backwards compatibility.
*)
Module Export nary.
  (** [Agree1 P] states that [P a] can only holds for one possible [a]. *)
  Notation Agree1 P := (∀ a1 a2, Observe2 [| a1 = a2 |] (P a1) (P a2)).

  (**
  [LaterAgreeN P] states that [P] takes [N] arguments and [P a_1 .. a_N]
  only holds for one possible [a_N], UP TO later (as appropriate for
  higher-order ghost state).
  *)
  Notation LaterAgree1 P := (∀ a1 a2, Observe2 (▷ (a1 ≡ a2)) (P a1) (P a2)).
  Notation LaterAgree2 P := (∀ a, LaterAgree1 (P a)).
  Notation LaterAgree3 P := (∀ a, LaterAgree2 (P a)).
  Notation LaterAgree4 P := (∀ a, LaterAgree3 (P a)).
  Notation LaterAgree5 P := (∀ a, LaterAgree4 (P a)).
End nary.

#[global] Instance Observe_mono {PROP : bi} :
  Proper ((⊢) ==> flip (⊢) ==> impl) (@Observe PROP).
Proof. solve_proper. Qed.
#[global] Instance Observe_flip_mono {PROP : bi} :
  Proper (flip (⊢) ==> (⊢) ==> flip impl) (@Observe PROP).
Proof. solve_proper. Qed.
#[global] Instance Observe_proper {PROP : bi} :
  Proper ((≡) ==> (≡) ==> (↔)) (@Observe PROP).
Proof. solve_proper. Qed.

#[global] Instance Observe2_mono {PROP : bi} :
  Proper ((⊢) ==> flip (⊢) ==> flip (⊢) ==> impl) (@Observe2 PROP).
Proof. solve_proper. Qed.
#[global] Instance Observe2_flip_mono {PROP : bi} :
  Proper (flip (⊢) ==> (⊢) ==> (⊢) ==> flip impl) (@Observe2 PROP).
Proof. solve_proper. Qed.
#[global] Instance Observe2_proper {PROP : bi} :
  Proper ((≡) ==> (≡) ==> (≡) ==> (↔)) (@Observe2 PROP).
Proof. solve_proper. Qed.

(** An example of using [observe] in the IPM *)
Section example.
  Context `{PROP : bi}.
  Context (Q P : PROP) {A} (R : A → PROP) (x y : A).
  Context `{!Observe [| x = y |] P}.
  Context `{!Observe Q (R y)}.

  Goal P ⊢ R x -∗ P ∗ R y ∗ Q.
  Proof.
    iIntros "P R".
    iDestruct (observe [| x = y |] with "P") as %->.
    iDestruct (observe Q with "R") as "#$".
    iFrame "P R".
  Abort.
End example.

Section proof_mode.
  Context {PROP : bi}.
  Implicit Types P Q : PROP.

  (** Enable things like [iIntros] and [iDestruct] when the goal is
      [Observe Q P], as well as [iApply lem] when [lem] is an
      observation instance. *)
  Lemma test_before Q P : Observe Q P.
  Proof. Fail iIntros "P". Abort.
  Lemma test_before `{Hobs : !Observe Q P} : P ⊢ <pers> Q.
  Proof. Fail iApply Hobs. Abort.
  Global Instance observe_as_emp_valid d Q P :
    AsEmpValid d (Observe Q P) (P -∗ <pers> Q).
  Proof.
    rewrite/AsEmpValid/Observe. split => ?.
    - move=>->. by auto.
    - move/bi.wand_elim_r'. by rewrite right_id.
  Qed.
  Lemma test_after `{Hobs : !Observe Q P} : P ⊢ <pers> Q.
  Proof. iApply Hobs. Abort.
  Lemma test_after Q P : Observe Q P.
  Proof. iIntros "P". Abort.

  Lemma test_before Q P1 P2 : Observe2 Q P1 P2.
  Proof. Fail iIntros "P1 P2". Abort.
  Lemma test_before `{Hobs : !Observe2 Q P1 P2} : P1 ⊢ P2 -∗ <pers> Q.
  Proof. Fail iApply Hobs. Abort.
  Global Instance observe_2_as_emp_valid d Q P1 P2 :
    AsEmpValid d (Observe2 Q P1 P2) (P1 -∗ P2 -∗ <pers> Q).
  Proof.
    rewrite/AsEmpValid/Observe2. split => ?.
    - move=>->. apply bi.wand_intro_r, bi.emp_sep_2.
    - move/bi.wand_elim_r'. by rewrite right_id.
  Qed.
  Lemma test_after Q P1 P2 : Observe2 Q P1 P2.
  Proof. iIntros "P1 P2". Abort.
  Lemma test_after `{Hobs : !Observe2 Q P1 P2} : P1 ⊢ P2 -∗ <pers> Q.
  Proof. iApply Hobs. Abort.
End proof_mode.

Section observe.
  Context {PROP : bi}.
  Implicit Types P Q : PROP.

  #[global] Instance Observe_trans : Transitive (Observe (PROP:=PROP)).
  Proof.
    intros P Q R ??. iIntros "R".
    iDestruct (observe Q with "R") as "#Q".
    iApply (observe with "Q").
  Qed.

  #[global] Instance Observe2_symm Q : Symmetric (Observe2 Q).
  Proof. Fail apply _. iIntros (P1 P2 HQ) "P2 P1". iApply (HQ with "P1 P2"). Qed.

  Lemma observe_2_observe Q P1 P2 : Observe2 Q P1 P2 ↔ Observe Q (P1 ∗ P2).
  Proof. by rewrite /Observe bi.entails_curry. Qed.
  Lemma observe_curry Q P1 P2 : Observe2 Q P1 P2 → Observe Q (P1 ∗ P2).
  Proof. apply observe_2_observe. Qed.
  Lemma observe_uncurry Q P1 P2 : Observe Q (P1 ∗ P2) → Observe2 Q P1 P2.
  Proof. apply observe_2_observe. Qed.

  (** Alternatives for eliminating observations *)
  (** We favor declaring observations with [only_provable] over [bi_pure]. *)
  Lemma observe_elim_pure (Q : Prop) P {O : Observe [| Q |] P} : P ⊢ ⌜Q⌝.
  Proof. rewrite (observe [| _ |] P). by iIntros "#%". Qed.
  Lemma observe_elim_only_provable (Q : Prop) P `{!Affine P, !Observe [| Q |] P} :
    P ⊢ [| Q |].
  Proof. iIntros "P". iDestruct (observe_elim_pure Q with "P") as "#$". Qed.
  Lemma observe_elim_strong Q P {O : Observe Q P} : P ⊢ P ∗ □ Q.
  Proof.
    rewrite -{1}(idemp bi_and P) {2}(observe Q P).
    by rewrite bi.persistently_and_intuitionistically_sep_r.
  Qed.
  Lemma observe_elim Q P {O : Observe Q P} : P ⊢ P ∗ Q.
  Proof.
    by rewrite {1}(observe_elim_strong Q P) bi.intuitionistically_elim.
  Qed.

  Lemma observe_equiv Q P `{!Observe Q P} `{!Affine Q} : P ∗ Q ⊣⊢ P.
  Proof. split'; first iIntros "[$ ?]". apply: observe_elim. Qed.

  Lemma observe_2_elim_pure (Q : Prop) P1 P2 {O : Observe2 [| Q |] P1 P2} :
    P1 ⊢ P2 -∗ ⌜Q⌝.
  Proof. rewrite (observe_2 [| _ |] P1 P2). f_equiv. by iIntros "#%". Qed.
  Lemma observe_2_elim_only_provable (Q : Prop) P1 P2
      `{!Affine P1, !Affine P2, O : !Observe2 [| Q |] P1 P2} :
    P1 ⊢ P2 -∗ [| Q |].
  Proof. exact /bi.wand_intro_r /observe_elim_only_provable /observe_curry. Qed.
  Lemma observe_2_elim_strong Q P1 P2 {O : Observe2 Q P1 P2} :
    P1 ⊢ P2 -∗ P1 ∗ P2 ∗ □ Q.
  Proof.
    apply bi.wand_intro_r. rewrite assoc.
    by apply observe_elim_strong, observe_curry.
  Qed.
  Lemma observe_2_elim Q P1 P2 {O : Observe2 Q P1 P2} : P1 ⊢ P2 -∗ P1 ∗ P2 ∗ Q.
  Proof.
    by rewrite {1}(observe_2_elim_strong Q P1 P2) bi.intuitionistically_elim.
  Qed.
  Lemma observe_2_uncurry_elim Q P1 P2 {O : Observe2 Q P1 P2} :
    P1 ∗ P2 ⊢ (P1 ∗ P2) ∗ Q.
  Proof. rewrite -(assoc bi_sep). exact /bi.wand_elim_l' /observe_2_elim. Qed.

  Lemma observe_2_equiv Q P1 P2 `{!Observe2 Q P1 P2} `{!Affine Q} : P1 ∗ P2 ∗ Q ⊣⊢ P1 ∗ P2.
  Proof. split'; first iIntros "($ & $ & _)". by apply bi.wand_elim_l', observe_2_elim. Qed.

  (** Alternatives for introducing observations *)
  (* [observe_intro_persistent] makes the goal linearly unprovable (unless [P] is affine). *)
  Lemma observe_intro_persistent Q P `{!Persistent Q} : (P ⊢ Q) → Observe Q P.
  Proof. rewrite/Observe=>->. iIntros "#$". Qed.

  Lemma observe_intro_only_provable (Q : Prop) (P : PROP) : (P ⊢ ⌜ Q ⌝) → Observe [| Q |] P.
  Proof. by rewrite /Observe persistently_only_provable =>->. Qed.

  Lemma observe_intro_only_provable_simple (Q : Prop)  (P : PROP) : Q -> Observe [| Q |] P.
  Proof. rewrite /Observe=>?. auto. Qed.

  Lemma observe_intro Q P `{!Persistent Q} : (P ⊢ P ∗ Q) → Observe Q P.
  Proof. rewrite/Observe {1}(persistent Q)=>->. iIntros "[_ $]". Qed.

  (* Ease proving the goal linearly. *)
  Lemma observe_intro_intuitionistically Q P : Observe Q P → Observe (□ Q) P.
  Proof. rewrite/Observe=>->. iIntros "#$". Qed.

  Lemma observe_intro_intuitionistically_if b Q P : Observe Q P → Observe (□?b Q) P.
  Proof. rewrite/Observe=>->. case: b => //=. iIntros "#$". Qed.

  Lemma observe_alt Q P : Observe Q P ↔ (P ⊢ <absorb> □ Q).
  Proof.
    by rewrite /Observe -bi.absorbingly_intuitionistically_into_persistently.
  Qed.

  Lemma observe_alt_sep_True Q P : Observe Q P ↔ (P ⊢ □ Q ∗ True).
  Proof. by rewrite observe_alt (comm bi_sep). Qed.

  Lemma observe_equiv_sep_True Q P `{!Persistent Q} : (P ⊢ Q ∗ True) ↔ Observe Q P.
  Proof.
    by rewrite (comm bi_sep Q) /Observe bi.persistently_absorbingly.
  Qed.

  Lemma observe_only_provable_impl (Q P : Prop) :
    (P -> Q) -> Observe (PROP:=PROP) [| Q |] [| P |].
  Proof. intros HQ. iIntros "% !> !%". exact: HQ. Qed.
  Lemma observe_2_only_provable_impl (Q P1 P2 : Prop) :
    (P1 -> P2 -> Q) -> Observe2 (PROP:=PROP) [| Q |] [| P1 |] [| P2 |].
  Proof. intros HQ. iIntros "% % !> !%". exact: HQ. Qed.

  (* [observe_2_intro_persistent] makes the goal linearly unprovable (unless [P1] and [P2] are affine). *)
  Lemma observe_2_intro_persistent Q P1 P2 `{!Persistent Q} :
    (P1 ⊢ P2 -∗ Q) → Observe2 Q P1 P2.
  Proof. rewrite/Observe2=>->. f_equiv. iIntros "#$". Qed.

  Lemma observe_2_intro_only_provable (Q : Prop) (P1 P2 : PROP) : (P1 ⊢ P2 -∗ ⌜ Q ⌝) → Observe2 [| Q |] P1 P2.
  Proof. by rewrite /Observe2 persistently_only_provable =>->. Qed.

  Lemma observe_2_intro Q P1 P2 `{!Persistent Q} :
    (P1 ⊢ P2 -∗ P1 ∗ P2 ∗ Q) → Observe2 Q P1 P2.
  Proof.
    rewrite/Observe2 {1}(persistent Q)=>->. f_equiv. iIntros "(_ &_ & $)".
  Qed.

  (* Ease proving the goal linearly. *)
  Lemma observe_2_intro_intuitionistically Q P1 P2 : Observe2 Q P1 P2 → Observe2 (□ Q) P1 P2.
  Proof. rewrite/Observe2=>->. f_equiv. iIntros "#$". Qed.

  Lemma observe_2_intro_intuitionistically_if b Q P1 P2 : Observe2 Q P1 P2 → Observe2 (□?b Q) P1 P2.
  Proof. rewrite/Observe2=>->. f_equiv. case: b => //=. iIntros "#$". Qed.

  Lemma observe_2_alt Q P1 P2 : Observe2 Q P1 P2 ↔ (P1 ∗ P2 ⊢ <absorb> □ Q).
  Proof. by rewrite observe_2_observe observe_alt. Qed.

  Lemma observe_2_alt_sep_True Q P1 P2 : Observe2 Q P1 P2 ↔ (P1 ∗ P2 ⊢ □ Q ∗ True).
  Proof. by rewrite observe_2_observe observe_alt_sep_True. Qed.

  Lemma observe_2_equiv_sep_True Q P1 P2 `{!Persistent Q} : (P1 ∗ P2 ⊢ Q ∗ True) ↔ Observe2 Q P1 P2.
  Proof. by rewrite observe_2_observe observe_equiv_sep_True. Qed.
End observe.

(** Instances *)
Section bi.
  Context {PROP : bi}.
  Implicit Types P Q : PROP.

  (*
  This instance is necessary when _defining_ observations, both by itself
  and as "leaf" of searches involving [observe_sep_{l,r}].
  *)
  Global Instance observe_refl Q `{!Persistent Q} : Observe Q Q.
  Proof. exact: observe_intro_persistent. Qed.

  Global Instance observe_exist {A} Q (P : A → PROP) :
    (∀ x, Observe Q (P x)) → Observe Q (∃ x, P x).
  Proof.
    intros. iDestruct 1 as (x) "P". iApply (observe with "P").
  Qed.
  Global Instance observe_2_exist {A} Q (P1 P2 : A → PROP) :
    (∀ x y, Observe2 Q (P1 x) (P2 y)) → Observe2 Q (∃ x, P1 x) (∃ y, P2 y).
  Proof.
    intros. iDestruct 1 as (x) "P1". iDestruct 1 as (y) "P2".
    iApply (observe_2 with "P1 P2").
  Qed.

  Global Instance observe_sep_l Q P R : Observe Q P → Observe Q (P ∗ R).
  Proof. intros. iIntros "[P _]". iApply (observe with "P"). Qed.
  Global Instance observe_sep_r Q P R : Observe Q P → Observe Q (R ∗ P).
  Proof. intros. iIntros "[_ P]". iApply (observe with "P"). Qed.
  Global Instance observe_2_sep_l Q P1 P2 R1 R2 :
    Observe2 Q P1 P2 → Observe2 Q (P1 ∗ R1) (P2 ∗ R2).
  Proof.
    intros. iIntros "[P1 _] [P2 _]". iApply (observe_2 with "P1 P2").
  Qed.
  Global Instance observe_2_sep_r Q P1 P2 R1 R2 :
    Observe2 Q P1 P2 → Observe2 Q (R1 ∗ P1) (R2 ∗ P2).
  Proof.
    intros. iIntros "[_ P1] [_ P2]". iApply (observe_2 with "P1 P2").
  Qed.

  Global Instance observe_and_l Q P R : Observe Q P → Observe Q (P ∧ R).
  Proof. intros. iIntros "[P _]". iApply (observe with "P"). Qed.
  Global Instance observe_and_r Q P R : Observe Q P → Observe Q (R ∧ P).
  Proof. intros. iIntros "[_ P]". iApply (observe with "P"). Qed.
  Global Instance observe_2_and_l Q P1 P2 R1 R2 :
    Observe2 Q P1 P2 → Observe2 Q (P1 ∧ R1) (P2 ∧ R2).
  Proof.
    intros. iIntros "[P1 _] [P2 _]". iApply (observe_2 with "P1 P2").
  Qed.
  Global Instance observe_2_and_r Q P1 P2 R1 R2 :
    Observe2 Q P1 P2 → Observe2 Q (R1 ∧ P1) (R2 ∧ P2).
  Proof.
    intros. iIntros "[_ P1] [_ P2]". iApply (observe_2 with "P1 P2").
  Qed.

  Global Instance observe_or Q P R :
    Observe Q P → Observe Q R → Observe Q (P ∨ R).
  Proof.
    intros. iIntros "[P|R]".
    by iApply (observe with "P"). by iApply (observe with "R").
  Qed.
  Global Instance observe_2_or Q P1 P2 R1 R2 :
    Observe2 Q P1 P2 → Observe2 Q P1 R2 →
    Observe2 Q R1 P2 → Observe2 Q R1 R2 →
    Observe2 Q (P1 ∨ R1) (P2 ∨ R2).
  Proof.
    intros. iIntros "[P1|R1] [P2|R2]".
    - iApply (observe_2 with "P1 P2").
    - iApply (observe_2 with "P1 R2").
    - iApply (observe_2 with "R1 P2").
    - iApply (observe_2 with "R1 R2").
  Qed.

  #[global] Instance observe_later Q P : Observe Q P → Observe (▷ Q) (▷ P).
  Proof. rewrite /Observe=>->. by rewrite bi.later_persistently. Qed.
  #[global] Instance observe_2_later Q P1 P2 :
    Observe2 Q P1 P2 → Observe2 (▷ Q) (▷ P1) (▷ P2).
  Proof.
    intros. apply observe_uncurry. rewrite -bi.later_sep.
    by apply observe_later, observe_curry.
  Qed.

  Global Instance observe_from_false Q : Observe Q False.
  Proof. iDestruct 1 as "[]". Qed.
  Global Instance observe_2_from_false_1 Q P : Observe2 Q False P.
  Proof. iDestruct 1 as "[]". Qed.
  Global Instance observe_2_from_false_2 Q P : Observe2 Q P False.
  Proof. iDestruct 2 as "[]". Qed.

  Global Instance observe_persistently Q P :
    Observe Q P → Observe Q (<pers> P).
  Proof. intros. iIntros "#P". iApply (observe with "P"). Qed.
  Global Instance observe_2_persistently Q P1 P2 :
    Observe2 Q P1 P2 → Observe2 Q (<pers> P1) (<pers> P2).
  Proof. intros. iIntros "#P1 #P2". iApply (observe_2 with "P1 P2"). Qed.

  Global Instance observe_intuitionistically Q P :
    Observe Q P → Observe Q (□ P).
  Proof. intros. iIntros "#P". iApply (observe with "P"). Qed.
  Global Instance observe_2_intuitionistically Q P1 P2 :
    Observe2 Q P1 P2 → Observe2 Q (□ P1) (□ P2).
  Proof. intros. iIntros "#P1 #P2". iApply (observe_2 with "P1 P2"). Qed.

  Global Instance observe_intuitionistically_if b Q P :
    Observe Q P → Observe Q (□?b P).
  Proof. intros. case: b => //=. iIntros "#P". iApply (observe with "P"). Qed.
  Global Instance observe_2_intuitionistically_if b Q P1 P2 :
    Observe2 Q P1 P2 → Observe2 Q (□?b P1) (□?b P2).
  Proof. intros. case: b => //=. iIntros "#P1 #P2". iApply (observe_2 with "P1 P2"). Qed.
End bi.

Section monpred.
  Context {I : biIndex} {PROP : bi}.
  Implicit Types i : I.
  Implicit Types P Q : (monPred I PROP).

  (** It's not clear these should be instances. *)
  Lemma monPred_observe Q P :
    (∀ i, Observe (Q i) (P i)) → Observe Q P.
  Proof.
    rewrite/Observe=>Hobs. constructor=>i.
    by rewrite (Hobs i) monPred_at_persistently.
  Qed.
  Lemma monPred_observe_2 Q P1 P2 :
    (∀ i, Observe2 (Q i) (P1 i) (P2 i)) → Observe2 Q P1 P2.
  Proof.
    intros Hobs. apply observe_uncurry, monPred_observe=>i.
    rewrite monPred_at_sep. by apply observe_curry.
  Qed.

  Lemma monPred_observe_only_provable (Q : Prop) P
    (Hobs : ∀ i, Observe [| Q |] (P i)) :
    Observe [| Q |] P.
  Proof.
    apply monPred_observe => i.
    by rewrite monPred_at_only_provable.
  Qed.

  Lemma monPred_observe_2_only_provable (Q : Prop) P1 P2
    (Hobs : ∀ i, Observe2 [| Q |] (P1 i) (P2 i)) :
    Observe2 [| Q |] P1 P2.
  Proof.
    apply monPred_observe_2 => i.
    by rewrite monPred_at_only_provable.
  Qed.

  (** These should certainly not be instances. *)
  Lemma observe_monPred_at Q P i : Observe Q P → Observe (Q i) (P i).
  Proof.
    intros [Hobs]. rewrite/Observe (Hobs i).
    by rewrite monPred_at_persistently.
  Qed.
  Lemma observe_2_monPred_at Q P1 P2 i :
    Observe2 Q P1 P2 → Observe2 (Q i) (P1 i) (P2 i).
  Proof.
    intros [Hobs]. rewrite/Observe2 (Hobs i).
    by rewrite monPred_wand_force monPred_at_persistently.
  Qed.

  Global Instance observe_pure_monPred_at (Q : Prop) P i :
    Observe [! Q !] P → Observe [! Q !] (P i).
  Proof.
    intros. rewrite -(monPred_at_pure i). by apply observe_monPred_at.
  Qed.
  Global Instance observe_2_pure_monPred (Q : Prop) P1 P2 i :
    Observe2 [! Q !] P1 P2 → Observe2 [! Q !] (P1 i) (P2 i).
  Proof.
    intros. rewrite -(monPred_at_pure i). by apply observe_2_monPred_at.
  Qed.

  Global Instance observe_only_provable_monPred_at (Q : Prop) P i :
    Observe [| Q |] P → Observe [| Q |] (P i).
  Proof.
    intros. rewrite -(monPred_at_only_provable i). by apply observe_monPred_at.
  Qed.
  Global Instance observe_2_only_provable_monPred_at (Q : Prop) P1 P2 i :
    Observe2 [| Q |] P1 P2 → Observe2 [| Q |] (P1 i) (P2 i).
  Proof.
    intros. rewrite -(monPred_at_only_provable i).
    by apply observe_2_monPred_at.
  Qed.

  Global Instance observe_2_internal_eq_monPred_at
      `{!BiInternalEq PROP} {A : ofe} x y P1 P2 i :
    Observe2 (x ≡@{A} y) P1 P2 -> Observe2 (x ≡ y) (P1 i) (P2 i).
  Proof.
    intros. rewrite -(monPred_at_internal_eq i). exact: observe_2_monPred_at.
  Qed.
  Global Instance observe_2_later_internal_eq_monPred_at
      `{!BiInternalEq PROP} {A : ofe} x y P1 P2 i :
    Observe2 (▷ (x ≡@{A} y)) P1 P2 -> Observe2 (▷ (x ≡ y)) (P1 i) (P2 i).
  Proof.
    intros. rewrite -(monPred_at_internal_eq i) -monPred_at_later.
    exact: observe_2_monPred_at.
  Qed.
End monpred.

Section embed.
  Context `{BiEmbed PROP1 PROP2}.
  Local Notation embed := (embed (A:=PROP1) (B:=PROP2)).
  Implicit Types P Q : PROP1.

  Global Instance embed_observe Q P : Observe Q P → Observe (embed Q) (embed P).
  Proof.
    rewrite/Observe=>->. by rewrite embed_persistently.
  Qed.
  Global Instance embed_observe_2 Q P1 P2 :
    Observe2 Q P1 P2 → Observe2 (embed Q) (embed P1) (embed P2).
  Proof.
    intros Hobs. apply observe_uncurry. rewrite -embed_sep.
    by apply embed_observe, observe_curry.
  Qed.
End embed.

(** Helpful lemmas. *)
Section theory.
  Context {PROP : bi}.
  Implicit Types P Q : PROP.

  Lemma observe_pure (Q : Prop) P : Observe [! Q !] P ↔ Observe [| Q |] P.
  Proof. by rewrite /Observe bi.persistently_pure persistently_only_provable. Qed.

  Lemma observe_2_pure (Q : Prop) P1 P2 :
    Observe2 [! Q !] P1 P2 ↔ Observe2 [| Q |] P1 P2.
  Proof. by rewrite /Observe2 bi.persistently_pure persistently_only_provable. Qed.

  Lemma observe_lhs p P Q : Observe [| p |] P → (p → P ⊢ Q) → P ⊢ Q.
  Proof.
    iIntros (Hp HpPQ) "P"; iDestruct (Hp with "P") as %?. by iApply (HpPQ with "P").
  Qed.

  Lemma observe_2_lhs p P1 P2 Q :
    Observe2 [| p |] P1 P2 → (p → P1 ∗ P2 ⊢ Q) → P1 ∗ P2 ⊢ Q.
  Proof.
    iIntros (Hp HpPQ) "[P1 P2]"; iDestruct (Hp with "P1 P2") as %?.
    by iApply (HpPQ with "[$P1 $P2]").
  Qed.

  Lemma observe_both p P Q :
    Observe [| p |] P → Observe [| p |] Q → (p → P ⊣⊢ Q) → P ⊣⊢ Q.
  Proof. intros ?? HpPQ. split'; apply: observe_lhs => Hp; by rewrite HpPQ. Qed.

  Lemma observe_2_both p P1 P2 Q1 Q2 :
    Observe2 [| p |] P1 P2 → Observe2 [| p |] Q1 Q2 →
    (p → P1 ∗ P2 ⊣⊢ Q1 ∗ Q2) → P1 ∗ P2 ⊣⊢ Q1 ∗ Q2.
  Proof. intros ?? HpPQ. split'; apply: observe_2_lhs => Hp; by rewrite HpPQ. Qed.

  (**
    These help deriving observations for [R] from observations for [Q].

    Recommended use:
    [apply: (observe_derive_only_provable Q_pattern).].
    [apply: (observe_2_derive_only_provable Q_pattern).].
    then prove [Q -> R].

    This is almost setoid rewriting, but it does not support rewriting by implication,
    and those idioms give [Q -> R] as output goal instead of input.
  *)
  Lemma observe_derive_only_provable (Q : Prop) {R : Prop} {P} :
    (Q → R) → Observe [| Q |] P → Observe [| R |] P.
  Proof. move=> HQR. apply Observe_mono => //. by f_equiv. Qed.

  Lemma observe_2_derive_only_provable (Q : Prop) {R : Prop} {P1 P2} :
    (Q → R) → Observe2 [| Q |] P1 P2 → Observe2 [| R |] P1 P2.
  Proof. move=> HQR. apply Observe2_mono => //. by f_equiv. Qed.

  Lemma observe2_inj {A B R1 R2} f `{Inj A B R1 R2 f} x y P1 P2 :
    Observe2 [| R2 (f x) (f y) |] P1 P2 -> Observe2 [| R1 x y |] P1 P2.
  Proof. apply observe_2_derive_only_provable, inj, _. Qed.
End theory.

(** [observable P] is the largest observation deducible from [P].

Motivation: framing [P] might make the goal unprovable, for instance in
[Observe Q P → P -∗ P ∗ Q]

But after observing [observable P], framing [P] always preserves provability. *)
mlock Definition observable {PROP : bi} (P : PROP) : PROP :=
  □ (∀ Q : PROP, [| Observe Q P |] -∗ Q).
#[global] Arguments observable {_} _ : assert.
#[global] Instance: Params (@observable) 1 := {}.

Section observable_theory.
  Context {PROP : bi}.
  Implicit Types P Q : PROP.

  #[global] Instance observable_persistent P : Persistent (observable P).
  Proof. rewrite observable.unlock. apply _. Qed.
  #[global] Instance observable_affine P : Affine (observable P).
  Proof. rewrite observable.unlock. apply _. Qed.
  #[global] Instance observe_observable `{!BiPersistentlyForall PROP} P :
    Observe (observable P) P.
  Proof.
    rewrite observable.unlock.
    apply observe_intro_intuitionistically.
    iIntros "P" (Q HQP). iDestruct (HQP with "P") as "#$".
  Qed.

  #[global] Instance observable_observe P Q `{!Observe Q P} :
    Observe Q (observable P).
  Proof.
    rewrite observable.unlock.
    iIntros "#P". by iApply ("P" $! Q with "[%]").
  Qed.

  Lemma observable_emp `{!BiPersistentlyForall PROP} : observable emp ⊣⊢@{PROP} emp.
  Proof.
    iSplit; first by eauto.
    iIntros "_". iApply (observe (observable emp) emp with "[//]").
  Qed.

  Lemma observable_False : observable False ⊣⊢@{PROP} False.
  Proof.
    iSplit; last by iIntros.
    iIntros "O".
    iDestruct (observe False with "O") as "#$".
  Qed.

  (**
  This is not invertible. _If_ instead we had
  [observable_sep_inv P Q : observable P ∗ observable Q ⊢ observable (P ∗ Q)]
  owning one [fracR] ghost variable would entail a contradiction:
  <<
  observable (own γ 1) ⊢ (* by persistence *)
  observable (own γ 1) ** observable (own γ 1) |-/- (* [observable_sep_inv] *)
  observable (own γ 1 ** own γ 1) |-- (* [own_valid_2] + validity of fractions *)
  False
  >>
  *)
  Lemma observable_sep P Q : observable (P ∗ Q) ⊢ observable P ∗ observable Q.
  Proof.
    rewrite observable.unlock.
    iIntros "#PQ".
    iSplit; iModIntro; iIntros (R) "%O"; iApply "PQ"; iPureIntro; apply _.
  Qed.

  #[global] Instance observable_mono :
    Proper ((⊢) ==> (⊢)) (observable (PROP := PROP)).
  Proof.
    (* TODO AUTO: fails *)
    (* rewrite observable.unlock; solve_proper. *)
    intros ???.
    rewrite observable.unlock; do 5 f_equiv.
    (* TODO AUTO: [f_equiv] uses [Observe_trans] :-( *)
    exact: Observe_mono.
  Qed.

  #[global] Instance observable_flip_mono :
    Proper (flip (⊢) ==> flip (⊢)) (observable (PROP := PROP)).
  Proof. solve_proper. Qed.

  #[global] Instance observable_proper :
    Proper ((⊣⊢) ==> (⊣⊢)) (observable (PROP := PROP)).
  Proof.
    intros ?? HE%bi.equiv_entails.
    apply (anti_symm (⊢)); apply observable_mono, HE.
  Qed.

End observable_theory.

#[global] Hint Resolve observe_intro_only_provable_simple : core.
