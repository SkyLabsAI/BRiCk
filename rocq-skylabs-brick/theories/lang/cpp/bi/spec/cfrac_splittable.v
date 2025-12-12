(*
 * Copyright (C) 2023 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Export bluerock.lang.cpp.bi.cfractional.

Require Import bluerock.iris.extra.bi.prelude.
Require Import bluerock.iris.extra.bi.observe.
Require Import bluerock.iris.extra.proofmode.proofmode.

#[local] Set Primitive Projections.
#[local] Set Printing Coercions.
#[local] Set Default Proof Using "Type*".

(** * Spec building block: const/mutable fractional ownership *)
(**
Overview:

- [CFracSplittable_N R]

- Tactic [solve_cfrac] for solving [CFracSplittable_N]

[CFracSplittable_N R], where [N] counts the number of arguments taken
by [R] after its const/mutable fraction, is short-hand for:

- [R] is _timeless_, meaning it represents ownership;

- [R] is _const/mutable fractional_, meaning it can be split and
combined using [andb] on booleans and addition on fractions; and

- the fraction in [R] is _valid_, meaning [≤ 1].
*)

Ltac solve_cfrac := solve [intros; split; [apply _..|solve_cfrac_valid]].

Class CFracSplittable_0 {PROP : bi} (R : cQp.t → PROP) : Prop := {
  #[global] cfrac_splittable_0_fractional :: CFractional R;
  #[global] cfrac_splittable_0_timeless :: Timeless1 R;
  #[global] cfrac_splittable_0_frac_valid :: CFracValid0 R;
}.
Section cfrac_0.
  Context {PROP : bi} (R : cQp.t → PROP) `{!CFracSplittable_0 R}.

  #[global] Instance cfrac_splittable_0_as_fractional : AsCFractional0 R.
  Proof. solve_as_cfrac. Qed.
End cfrac_0.

Class CFracSplittable_1 {A} {PROP : bi} (R : cQp.t → A → PROP) : Prop := {
  #[global] cfrac_splittable_1_fractional :: CFractional1 R;
  #[global] cfrac_splittable_1_timeless :: Timeless2 R;
  #[global] cfrac_splittable_1_frac_valid :: CFracValid1 R;
}.
Section cfrac_1.
  Context {A} {PROP : bi} (R : cQp.t → A → PROP) `{!CFracSplittable_1 R}.

  #[global] Instance cfrac_splittable_1_as_fractional : AsCFractional1 R.
  Proof. solve_as_cfrac. Qed.
End cfrac_1.

Class CFracSplittable_2 {A B} {PROP : bi} (R : cQp.t → A → B → PROP) : Prop := {
  #[global] cfrac_splittable_2_fractional :: CFractional2 R;
  #[global] cfrac_splittable_2_timeless :: Timeless3 R;
  #[global] cfrac_splittable_2_frac_valid :: CFracValid2 R;
}.
Section cfrac_2.
  Context {A B} {PROP : bi} (R : cQp.t → A → B → PROP) `{!CFracSplittable_2 R}.

  #[global] Instance cfrac_splittable_2_as_fractional : AsCFractional2 R.
  Proof. solve_as_cfrac. Qed.
End cfrac_2.

Class CFracSplittable_3 {A B C} {PROP : bi}
    (R : cQp.t → A → B → C → PROP) : Prop := {
  #[global] cfrac_splittable_3_fractional :: CFractional3 R;
  #[global] cfrac_splittable_3_timeless :: Timeless4 R;
  #[global] cfrac_splittable_3_frac_valid :: CFracValid3 R;
}.
Section cfrac_3.
  Context {A B C} {PROP : bi} (R : cQp.t → A → B → C → PROP) `{!CFracSplittable_3 R}.

  #[global] Instance cfrac_splittable_3_as_fractional : AsCFractional3 R.
  Proof. solve_as_cfrac. Qed.
End cfrac_3.

Class CFracSplittable_4 {A B C D} {PROP : bi}
    (R : cQp.t → A → B → C → D → PROP) : Prop := {
  #[global] cfrac_splittable_4_fractional :: CFractional4 R;
  #[global] cfrac_splittable_4_timeless :: Timeless5 R;
  #[global] cfrac_splittable_4_frac_valid :: CFracValid4 R;
}.
Section cfrac_4.
  Context {A B C D} {PROP : bi} (R : cQp.t → A → B → C → D → PROP).
  Context `{!CFracSplittable_4 R}.

  #[global] Instance cfrac_splittable_4_as_fractional : AsCFractional4 R.
  Proof. solve_as_cfrac. Qed.
End cfrac_4.

Class CFracSplittable_5 {A B C D E} {PROP : bi}
    (R : cQp.t → A → B → C → D → E → PROP) : Prop := {
  #[global] cfrac_splittable_5_fractional :: CFractional5 R;
  #[global] cfrac_splittable_5_timeless :: Timeless6 R;
  #[global] cfrac_splittable_5_frac_valid :: CFracValid5 R;
}.
Section cfrac_5.
  Context {A B C D E} {PROP : bi} (R : cQp.t → A → B → C → D → E → PROP).
  Context `{!CFracSplittable_5 R}.

  #[global] Instance cfrac_splittable_5_as_fractional : AsCFractional5 R.
  Proof. solve_as_cfrac. Qed.
End cfrac_5.
