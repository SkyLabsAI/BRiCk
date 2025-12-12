(*
 * Copyright (C) 2020-2022 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Export bluerock.iris.extra.bi.fractional.

Require Import bluerock.iris.extra.bi.prelude.
Require Import bluerock.iris.extra.bi.observe.
Require Import bluerock.iris.extra.bi.spec.exclusive.
Require Import bluerock.iris.extra.proofmode.proofmode.

#[local] Set Primitive Projections.
#[local] Set Default Proof Using "Type*".

(** * Spec building block: fractional ownership *)
(**
Overview:

- [FracVadidN], [Frac2ValidN], [FracSplittable_N R]

- Tactic [solve_frac] for solving [FracSplittable_N]

- [FracLaterAgree1] for higher-order predicates

[FracSplittable_N R], where [N] counts the number of arguments taken
by [R] after its fraction, is short-hand for:

- [R] is _timeless_, meaning it represents ownership;

- [R] is _fractional_, meaning it can be split and combined using
addition on fractions; and

- the fraction in [R] is _valid_, meaning [≤ 1].

After defining the [FracSplittable_N], we given an example of a
predicate [R] taking arguments before and after its fraction.
*)

(**
[FracValidN P] observes [q ≤ 1] from [P] applied to fraction [q] and
then [N] arguments.
*)
Notation FracValid0 P := (∀ q, Observe [| q ≤ 1 |]%Qp (P q)) (only parsing).
Notation FracValid1 P := (∀ q a, Observe [| q ≤ 1 |]%Qp (P q a)) (only parsing).
Notation FracValid2 P := (∀ q a b, Observe [| q ≤ 1 |]%Qp (P q a b)) (only parsing).
Notation FracValid3 P := (∀ q a b c, Observe [| q ≤ 1 |]%Qp (P q a b c)) (only parsing).
Notation FracValid4 P := (∀ q a b c d, Observe [| q ≤ 1 |]%Qp (P q a b c d)) (only parsing).
Notation FracValid5 P := (∀ q a b c d e, Observe [| q ≤ 1 |]%Qp (P q a b c d e)) (only parsing).

(**
[Frac2ValidN P] is a useful corollary of [FracValidN], observing [q1 +
q2 ≤ 1] given [P q1 a1 .. aN ** P q2 b1 .. bN].
*)
Notation Frac2Valid0 P := (∀ q1 q2, Observe2 [| q1 + q2 ≤ 1 |]%Qp (P q1) (P q2)) (only parsing).
Notation Frac2Valid1 P := (∀ q1 q2 a1 a2, Observe2 [| q1 + q2 ≤ 1 |]%Qp (P q1 a1) (P q2 a2)) (only parsing).

Ltac solve_frac := solve [intros; split; apply _].

Class FracSplittable_0 {PROP : bi} (R : Qp → PROP) : Prop := {
  #[global] frac_splittable_0_fractional :: Fractional R;
  #[global] frac_splittable_0_timeless :: Timeless1 R;
  #[global] frac_splittable_0_frac_valid :: FracValid0 R;
}.
Section frac_0.
  Context {PROP : bi} (R : Qp → PROP) `{!FracSplittable_0 R}.

  Global Instance frac_splittable_0_as_fractional : AsFractional0 R.
  Proof. solve_as_frac. Qed.
  Global Instance frac_splittable_0_frac_valid_2 : Frac2Valid0 R.
  Proof.
    intros. iIntros "R1 R2". iCombine "R1 R2" as "R". iApply (observe with "R").
  Qed.
End frac_0.
Section frac_1_gen.
  Context {A} {PROP : bi} (R : Qp → A → PROP).
  Context {frac_splittable_1_frac_valid : FracValid1 R}.
  Context {frac_splittable_1_as_fractional : AsFractional1 R}.

  Global Instance frac_splittable_1_frac_valid_2 : AgreeF1 R -> Frac2Valid1 R.
  Proof.
    intros Ha *. iIntros "R1 R2".
    iDestruct (Ha with "R1 R2") as %->.
    iCombine "R1 R2" as "R". iApply (observe with "R").
  Qed.

  Global Instance frac_splittable_1_agreef_excl_gen q v1 v2 `{!AgreeF1 R} :
    Observe2 False (R 1%Qp v1) (R q v2).
  Proof.
    iIntros "R1 R2".
    by iDestruct (observe_2 [| _ + _ ≤ _ |]%Qp with "R1 R2") as %?%Qp.not_add_le_l.
  Qed.

  Goal AgreeF1 R → Exclusive1 (R 1).
  Proof. apply _. Abort.
End frac_1_gen.

Class FracSplittable_1 {A} {PROP : bi} (R : Qp → A → PROP) : Prop := {
  #[global] frac_splittable_1_fractional :: Fractional1 R;
  #[global] frac_splittable_1_timeless :: Timeless2 R;
  #[global] frac_splittable_1_frac_valid :: FracValid1 R;
}.
Section frac_1.
  Context {A} {PROP : bi} (R : Qp → A → PROP) `{!FracSplittable_1 R}.

  Global Instance frac_splittable_1_as_fractional : AsFractional1 R.
  Proof. solve_as_frac. Qed.

  Goal AgreeF1 R -> Frac2Valid1 R.
  Proof. apply _. Abort.

  Goal AgreeF1 R → Exclusive1 (R 1).
  Proof. apply _. Abort.
End frac_1.

Class FracSplittable_2 {A B} {PROP : bi} (R : Qp → A → B → PROP) : Prop := {
  #[global] frac_splittable_2_fractional :: Fractional2 R;
  #[global] frac_splittable_2_timeless :: Timeless3 R;
  #[global] frac_splittable_2_frac_valid :: FracValid2 R;
}.
Section frac_2.
  Context {A B} {PROP : bi} (R : Qp → A → B → PROP) `{!FracSplittable_2 R}.

  Global Instance frac_splittable_2_as_fractional : AsFractional2 R.
  Proof. solve_as_frac. Qed.
End frac_2.

Class FracSplittable_3 {A B C} {PROP : bi}
    (R : Qp → A → B → C → PROP) : Prop := {
  #[global] frac_splittable_3_fractional :: Fractional3 R;
  #[global] frac_splittable_3_timeless :: Timeless4 R;
  #[global] frac_splittable_3_frac_valid :: FracValid3 R;
}.
Section frac_3.
  Context {A B C} {PROP : bi} (R : Qp → A → B → C → PROP) `{!FracSplittable_3 R}.

  Global Instance frac_splittable_3_as_fractional : AsFractional3 R.
  Proof. solve_as_frac. Qed.
End frac_3.

Class FracSplittable_4 {A B C D} {PROP : bi}
    (R : Qp → A → B → C → D → PROP) : Prop := {
  #[global] frac_splittable_4_fractional :: Fractional4 R;
  #[global] frac_splittable_4_timeless :: Timeless5 R;
  #[global] frac_splittable_4_frac_valid :: FracValid4 R;
}.
Section frac_4.
  Context {A B C D} {PROP : bi} (R : Qp → A → B → C → D → PROP).
  Context `{!FracSplittable_4 R}.

  Global Instance frac_splittable_4_as_fractional : AsFractional4 R.
  Proof. solve_as_frac. Qed.
End frac_4.

Class FracSplittable_5 {A B C D E} {PROP : bi}
    (R : Qp → A → B → C → D → E → PROP) : Prop := {
  #[global] frac_splittable_5_fractional :: Fractional5 R;
  #[global] frac_splittable_5_timeless :: Timeless6 R;
  #[global] frac_splittable_5_frac_valid :: FracValid5 R;
}.
Section frac_5.
  Context {A B C D E} {PROP : bi} (R : Qp → A → B → C → D → E → PROP).
  Context `{!FracSplittable_5 R}.

  Global Instance frac_splittable_5_as_fractional : AsFractional5 R.
  Proof. solve_as_frac. Qed.
End frac_5.

Class FracSplittable_6 {A B C D E F} {PROP : bi}
    (R : Qp → A → B → C → D → E → F → PROP) : Prop := {
  #[global] frac_splittable_6_fractional a b c d e f :: Fractional (λ q, R q a b c d e f);
  #[global] frac_splittable_6_timeless q a b c d e f :: Timeless (R q a b c d e f);
  #[global] frac_splittable_6_frac_valid (q : Qp) a b c d e f ::
    Observe [| q ≤ 1 |]%Qp (R q a b c d e f);
}.
Section frac_6.
  Context {A B C D E F} {PROP : bi} (R : Qp → A → B → C → D → E → F → PROP).
  Context `{!FracSplittable_6 R}.

  Global Instance frac_splittable_6_as_fractional q a b c d e f :
    AsFractional (R q a b c d e f) (λ q, R q a b c d e f) q.
  Proof. solve_as_frac. Qed.
End frac_6.

Class FracSplittable_7 {A B C D E F G} {PROP : bi}
    (R : Qp → A → B → C → D → E → F → G → PROP) : Prop := {
  #[global] frac_splittable_7_fractional a b c d e f g ::
    Fractional (λ q, R q a b c d e f g);
  #[global] frac_splittable_7_timeless q a b c d e f g :: Timeless (R q a b c d e f g);
  #[global] frac_splittable_7_frac_valid (q : Qp) a b c d e f g ::
    Observe [| q ≤ 1 |]%Qp (R q a b c d e f g);
}.
Section frac_7.
  Context {A B C D E F G} {PROP : bi} (R : Qp → A → B → C → D → E → F → G → PROP).
  Context `{!FracSplittable_7 R}.

  Global Instance frac_splittable_7_as_fractional q a b c d e f g :
    AsFractional (R q a b c d e f g) (λ q, R q a b c d e f g) q.
  Proof. solve_as_frac. Qed.
End frac_7.

Class FracSplittable_8 {A B C D E F G H} {PROP : bi}
    (R : Qp → A → B → C → D → E → F → G → H → PROP) : Prop := {
  #[global] frac_splittable_8_fractional a b c d e f g h ::
    Fractional (λ q, R q a b c d e f g h);
  #[global] frac_splittable_8_timeless q a b c d e f g h ::
    Timeless (R q a b c d e f g h);
  #[global] frac_splittable_8_frac_valid (q : Qp) a b c d e f g h ::
    Observe [| q ≤ 1 |]%Qp (R q a b c d e f g h);
}.
Section frac_8.
  Context {A B C D E F G H} {PROP : bi} (R : Qp → A → B → C → D → E → F → G → H → PROP).
  Context `{!FracSplittable_8 R}.

  Global Instance frac_splittable_8_as_fractional q a b c d e f g h :
    AsFractional (R q a b c d e f g h) (λ q, R q a b c d e f g h) q.
  Proof. solve_as_frac. Qed.
End frac_8.

Class FracSplittable_9 {A B C D E F G H I} {PROP : bi}
    (R : Qp → A → B → C → D → E → F → G → H → I → PROP) : Prop := {
  #[global] frac_splittable_9_fractional a b c d e f g h i ::
    Fractional (λ q, R q a b c d e f g h i);
  #[global] frac_splittable_9_timeless q a b c d e f g h i ::
    Timeless (R q a b c d e f g h i);
  #[global] frac_splittable_9_frac_valid (q : Qp) a b c d e f g h i ::
    Observe [| q ≤ 1 |]%Qp (R q a b c d e f g h i);
}.
Section frac_9.
  Context {A B C D E F G H I} {PROP : bi}
    (R : Qp → A → B → C → D → E → F → G → H → I → PROP).
  Context `{!FracSplittable_9 R}.

  Global Instance frac_splittable_9_as_fractional q a b c d e f g h i :
    AsFractional (R q a b c d e f g h i) (λ q, R q a b c d e f g h i) q.
  Proof. solve_as_frac. Qed.
End frac_9.

(** To accomodate arguments _before_ a fraction, universally quantify
over those arguments and cover the remaining arguments using a
[Frac_i]. Here's an example. *)
Module example.
  Class Res {PROP : bi} : Type := {
    my_thing (x : nat) (q : Qp) (y : nat) : PROP;
    #[global] my_thing_frac x :: FracSplittable_1 (my_thing x);
  }.

  Lemma my_thing_example `{Res} q1 q2 x y :
    my_thing x (q1 + q2) y ⊣⊢ my_thing x q1 y ∗ my_thing x q2 y.
  Proof. exact: fractional. Qed.
End example.


(**
Fractional ghost state with agreement on one higher-order argument.
Compared to [FracSplittable_1], we

- drop [Timeless] because higher-order ghost state depends on the
step-index, and

- add [Contractive] and [LaterAgreeF1] to enable agreement lemmas.
*)
Class FracLaterAgree1 {A : ofe} {PROP} `{!BiInternalEq PROP}
    (R : Qp -> A -> PROP) : Prop := {
  #[global] frac_later_agree_1_fractional a :: Fractional (fun q => R q a);
  #[global] frac_later_agree_1_valid q a :: Observe [| q ≤ 1 |]%Qp (R q a);
  #[global] frac_later_agree_1_contractive q :: Contractive (R q);
  #[global] frac_later_agree_1_agree :: LaterAgreeF1 R;
}.
#[global] Hint Mode FracLaterAgree1 - - - ! : typeclass_instances.

Section frac_later_agree.
  Context {A : ofe} `{!BiInternalEq PROP}.
  Context (R : Qp -> A -> PROP).
  Context `{!frac_splittable.FracLaterAgree1 R}.
  #[local] Set Default Proof Using "Type*".
  #[local] Notation PROPO := (bi_ofeO PROP).

  #[global] Instance frac_later_agree_1_ne q : NonExpansive (R q).
  Proof. exact: contractive_ne. Qed.
  #[global] Instance frac_later_agree_1_proper q :
    Proper (equiv ==> equiv) (R q).
  Proof. exact: ne_proper. Qed.

  #[global] Instance frac_later_agree_1_as_fractional q a :
    AsFractional (R q a) (fun q => R q a) q.
  Proof. exact: Build_AsFractional. Qed.

  #[global] Instance frac_later_agree_1_equivI q1 q2 a1 a2 :
    Observe2 (R q1 a1 ≡@{PROPO} R q1 a2) (R q1 a1) (R q2 a2).
  Proof.
    iIntros "R1 R2". iDestruct (observe_2 (▷ (_ ≡ _)) with "R1 R2") as "#Eq".
    rewrite (f_equivI_contractive (R q1)). auto.
  Qed.

  #[global] Instance frac_later_agree_1_valid_2 q1 q2 a1 a2 :
    Observe2 [| q1 + q2 ≤ 1 |]%Qp (R q1 a1) (R q2 a2).
  Proof.
    iIntros "R1 R2". iDestruct (observe_2 (_ ≡ _) with "R1 R2") as "#Eq".
    iRewrite "Eq" in "R1". iCombine "R1 R2" as "R". iApply (observe with "R").
  Qed.

  #[global] Instance frac_later_agree_1_exclusive : Exclusive1 (R 1).
  Proof.
    intros. iIntros "R1 R2".
    by iDestruct (frac_later_agree_1_valid_2 with "R1 R2") as %?.
  Qed.
End frac_later_agree.
