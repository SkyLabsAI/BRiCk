(*
 * Copyright (c) 2022 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Export bluerock.iris.extra.bi.fractional.

Require Import bluerock.prelude.numbers.

(** * Splitting and combining fractions *)
(**
Overview:

- [QpTC.Add], [QpTC.Mul], [QpTC.Div] normalizing operations on
fractions

- [SplitFrac], [CombineFrac] split and combine [Qp] expressions built
up from constants, [+], [*], and [/]. They simpilfy their outputs more
aggressively than Iris' [IntoSep], [FromSep] instances for splitting
and combining predicates satisfying [AsFractional].
*)

(**
Our rules are syntactic: All definitions appearing in input positions
should be opaque for typeclass resolution.
*)
#[global] Hint Opaque
  pos_to_Qp	(** e.g., [1%Qp = pos_to_Qp 1] *)
  Qp.add
  Qp.div	(** for emphasis---it's already opaque *)
  Qp.mul
: typeclass_instances.

#[local] Notation Cut := TCNoBackTrack.

(** ** Operations on fractions *)
Module QpTC.

  #[local] Open Scope Qp_scope.

  (**
  Note: Some of the following instances overlap. We keep them to
  shorten proof terms, using [Cut] to avoid backtracking.
  *)

  (** [Add q1 q2 q] sets [q := q1 + q2] with simplifications. *)
  Class Add (q1 q2 q : Qp) : Prop := add : q1 + q2 = q.
  #[global] Hint Mode Add + + - : typeclass_instances.
  #[global] Arguments Add : simpl never.
  #[global] Arguments add _ _ {_ _} : assert.
  Notation ADD q1 q2 q := (Cut (Add q1 q2 q)) (only parsing).

  (** [Mul q1 q2 q] sets [q := q1 * q2] with simplifications. *)
  Class Mul (q1 q2 q : Qp) : Prop := mul : q1 * q2 = q.
  #[global] Hint Mode Mul + + - : typeclass_instances.
  #[global] Arguments Mul : simpl never.
  #[global] Arguments mul _ _ {_ _} : assert.
  Notation MUL q1 q2 q := (Cut (Mul q1 q2 q)) (only parsing).

  (** [Div q1 q2 q] sets [q := q1 / q2] with simplifications. *)
  Class Div (q1 q2 q : Qp) : Prop := div : q1 / q2 = q.
  #[global] Hint Mode Div + + - : typeclass_instances.
  #[global] Arguments Div : simpl never.
  #[global] Arguments div _ _ {_ _} : assert.
  Notation DIV q1 q2 q := (Cut (Div q1 q2 q)) (only parsing).

  (** [Add] *)

  #[global] Instance add_half_half : Add (1/2) (1/2) 1 | 10.
  Proof. apply Qp.half_half. Qed.
  #[global] Instance add_div_2 q : Add (q/2) (q/2) q | 12.
  Proof. apply Qp.div_2. Qed.
  #[global] Instance add_div_4 q : Add (q/4) (q/4) (q/2) | 10.
  Proof. apply Qp.div_4. Qed.
  #[global] Instance add_quarter_three_quarter : Add (1/4) (3/4) 1 | 10.
  Proof. apply Qp.quarter_three_quarter. Qed.
  #[global] Instance add_three_quarter_quarter : Add (3/4) (1/4) 1 | 10.
  Proof. apply Qp.three_quarter_quarter. Qed.
  #[global] Instance add_third_two_thirds : Add (1/3) (2/3) 1 | 10.
  Proof. apply Qp.third_two_thirds. Qed.
  #[global] Instance add_two_thirds_third : Add (2/3) (1/3) 1 | 10.
  Proof. apply Qp.two_thirds_third. Qed.
  #[global] Instance add_1_1 : Add 1 1 2 | 10.
  Proof. apply Qp.add_1_1. Qed.

  (** [q/(2*p) + q/(2*p) --> q/p] *)
  #[global] Instance add_div_2_mul_ll q p qp :
    DIV q p qp -> Add (q / (2 * p)) (q / (2 * p)) qp | 20.
  Proof. rewrite /Div/Add=>-[]<-. apply Qp.div_2_mul. Qed.
  #[global] Instance add_div_2_mul_rr q p qp :
    DIV q p qp -> Add (q / (p * 2)) (q / (p * 2)) qp | 20.
  Proof. rewrite [p*2]comm_L. apply _. Qed.
  #[global] Instance add_div_2_mul_lr q p qp :
    DIV q p qp -> Add (q / (2 * p)) (q / (p * 2)) qp | 20.
  Proof. rewrite [p*2]comm_L. apply _. Qed.
  #[global] Instance add_div_2_mul_rl q p qp :
    DIV q p qp -> Add (q / (p * 2)) (q / (2 * p)) qp | 20.
  Proof. rewrite [p*2]comm_L. apply _. Qed.

  (** [q + q = 2*q] *)
  #[global] Instance add_diag q p : MUL 2 q p -> Add q q p | 21.
  Proof. rewrite /Mul=>-[]<-. apply Qp.add_diag. Qed.

  (** [p*q1 + p*q2 = p*(q1 + q2)] *)
  #[global] Instance add_mul_l q1 q2 q p pq :
    ADD q1 q2 q -> MUL p q pq -> Add (p * q1) (p * q2) pq | 22.
  Proof. rewrite /Add/Mul=>-[]<-[]<-. by rewrite Qp.mul_add_distr_l. Qed.
  #[global] Instance add_mul_r q1 q2 q p qp :
    ADD q1 q2 q -> MUL q p qp -> Add (q1 * p) (q2 * p) qp | 22.
  Proof. rewrite /Add/Mul=>-[]<-[]<-. by rewrite Qp.mul_add_distr_r. Qed.

  (** [q1/p + q2/p = (q1 + q2)/p] *)
  #[global] Instance add_div q1 q2 q p qp :
    ADD q1 q2 q -> DIV q p qp -> Add (q1 / p) (q2 / p) qp | 25.
  Proof. rewrite /Add/Div=>-[]<-[]<-. by rewrite Qp.div_add_distr. Qed.

  #[global] Instance add_xx q1 q2 : Add q1 q2 (q1 + q2) | 50.
  Proof. done. Qed.

  (** [Mul] *)

  #[global] Instance mul_22 : Mul 2 2 4 | 10.
  Proof. apply Qp.mul_2_2. Qed.
  #[global] Instance mul_1x q : Mul 1 q q | 10.
  Proof. rewrite /Mul. by rewrite left_id_L. Qed.
  #[global] Instance mul_x1 q : Mul q 1 q | 10.
  Proof. rewrite /Mul. by rewrite right_id_L. Qed.
  #[global] Instance mul_div_r q p : Mul q (p/q) p | 10.
  Proof. apply Qp.mul_div_r. Qed.
  #[global] Instance mul_div_l q p : Mul (q/p) p q | 10.
  Proof. apply Qp.mul_div_l. Qed.
  #[global] Instance mul_xx q1 q2 : Mul q1 q2 (q1 * q2) | 50.
  Proof. done. Qed.

  (** [Div] *)

  #[global] Instance div_1 q : Div q 1 q | 10.
  Proof. rewrite /Div. by rewrite right_id_L. Qed.
  #[global] Instance div_1_2 : Div 1 2 (1/2) | 10.
  Proof. done. Qed.
  #[global] Instance div_half_2 : Div (1/2) 2 (1/4) | 10.
  Proof. rewrite /Div. by rewrite Qp.div_div Qp.mul_2_2. Qed.
  #[global] Instance div_1_4 : Div 1 4 (1/4) | 10.
  Proof. done. Qed.

  (** [(r*p)/(r*q) --> p/q] *)
  #[global] Instance div_mul_cancel_l p q r pq :
    DIV p q pq -> Div (r * p) (r * q) pq | 20.
  Proof.
    intros [?]. rewrite /Div. by rewrite Qp.div_mul_cancel_l div.
  Qed.

  (** [(p*r)/(q*r) --> p/q] *)
  #[global] Instance div_mul_cancel_r p q r pq :
    DIV p q pq -> Div (p*r) (q*r) pq | 20.
  Proof.
    intros [?]. rewrite /Div. by rewrite Qp.div_mul_cancel_r div.
  Qed.

  (** [p/q/r --> p/(q*r)] *)
  #[global] Instance div_div p q r qr pqr :
    MUL q r qr -> DIV p qr pqr -> Div (p/q) r pqr | 20.
  Proof.
    intros [?] [?]. rewrite /Div. by rewrite Qp.div_div mul div.
  Qed.

  #[global] Instance div_xx q1 q2 : Div q1 q2 (q1 / q2) | 50.
  Proof. done. Qed.

End QpTC.

(** ** Splitting fractions *)
(**
[SplitFrac q q1 q2] splits fraction [q] into [q1], [q2] s.t. [q = q1 +
q2], adjusting the outputs [q1], [q2] for readabilty. It works by
searching for a [+] in the given term to split on. If that search
fails, it divides by two.
*)
Class SplitFrac (q q1 q2 : Qp) : Prop := split_frac : q = (q1 + q2)%Qp.
#[global] Hint Mode SplitFrac + - - : typeclass_instances.
#[global] Arguments SplitFrac : simpl never.
#[global] Arguments split_frac _ {_ _ _} : assert.

Module split_frac.
  #[local] Open Scope Qp_scope.

  (**
  [OnAdd] hunts for a [+] in the given term to split on, simplifying
  the results. Unlike [SplitFrac], this judgment fails rather than
  divide by two.
  *)
  Class OnAdd (q q1 q2 : Qp) : Prop := on_add : q = (q1 + q2)%Qp.
  #[global] Hint Mode OnAdd + - - : typeclass_instances.
  #[global] Arguments OnAdd : simpl never.
  #[global] Arguments on_add _ {_ _ _} : assert.
  Notation ON_ADD q q1 q2 := (Cut (OnAdd q q1 q2)) (only parsing).

  (**
  Splitting on [+] and [2*q] are the base cases.
  *)
  #[global] Instance on_add_add q1 q2 : OnAdd (q1 + q2) q1 q2 | 10.
  Proof. done. Qed.

  (** [2*q = q + q] *)
  #[global] Instance on_add_2x q : OnAdd (2 * q) q q | 10.
  Proof. rewrite /OnAdd. by rewrite Qp.add_diag. Qed.
  #[global] Instance on_add_x2 q : OnAdd (q * 2) q q | 10.
  Proof. rewrite comm_L. apply _. Qed.

  (** [4*q = 2*q + 2*q] *)
  #[global] Instance on_add_4x q : OnAdd (4 * q) (2 * q) (2 * q) | 10.
  Proof. rewrite -Qp.mul_2_2 -assoc_L. apply _. Qed.
  #[global] Instance on_add_x4 q : OnAdd (q * 4) (q * 2) (q * 2) | 10.
  Proof. rewrite [q*4]comm_L [q*2]comm_L. apply _. Qed.

  (**
  To split on [+] in [p * q], attempt to split on [+] in [p]. If that
  fails, attempt to split on [+] in [q]. If that fails, the split in
  [p * q] fails.
  *)

  (** [(q1 + q2)*p --> q1*p + q2*p] *)
  #[global] Instance on_add_mul_r p q q1 q2 q1p q2p :
    ON_ADD q q1 q2 -> QpTC.MUL q1 p q1p -> QpTC.MUL q2 p q2p ->
    OnAdd (q * p) q1p q2p | 20.
  Proof.
    intros [?] [?] [?]. rewrite /OnAdd.
    by rewrite (on_add q) Qp.mul_add_distr_r !QpTC.mul.
  Qed.

  (** [p*(q1 + q2) --> p*q1 + p*q2] *)
  #[global] Instance on_add_mul_l p q q1 q2 pq1 pq2 :
    ON_ADD q q1 q2 -> QpTC.MUL p q1 pq1 -> QpTC.MUL p q2 pq2 ->
    OnAdd (p * q) pq1 pq2 | 21.
  Proof.
    intros [?] [?] [?]. rewrite /OnAdd.
    by rewrite (on_add q) Qp.mul_add_distr_l !QpTC.mul.
  Qed.

  (**
  To split on [+] in [p / q], attempt to split on [+] in [p]. If that
  fails, the in [p / q] fails.
  *)

  (** [(q1+q2)/p --> q1/p + q2/p] *)
  #[global] Instance on_add_div p q q1 q2 q1p q2p :
    ON_ADD q q1 q2 -> QpTC.DIV q1 p q1p -> QpTC.DIV q2 p q2p ->
    OnAdd (q / p) q1p q2p | 20.
  Proof.
    intros [?] [?] [?]. rewrite /OnAdd.
    by rewrite (on_add q) Qp.div_add_distr !QpTC.div.
  Qed.

  (**
  We use this auxiliary judgment to [Cut] in [SplitFrac].
  *)
  Class Split (q q1 q2 : Qp) : Prop := split : q = (q1 + q2)%Qp.
  #[global] Hint Mode Split + - - : typeclass_instances.
  #[global] Arguments Split : simpl never.
  #[global] Arguments split _ {_ _ _} : assert.
  Notation SPLIT q q1 q2 := (Cut (Split q q1 q2)) (only parsing).

  #[global] Instance split_structural q q1 q2 :
    ON_ADD q q1 q2 -> Split q q1 q2 | 10.
  Proof. by case. Qed.

  #[global] Instance split_div_2 q qout :
    QpTC.DIV q 2 qout -> Split q qout qout | 50.
  Proof.
    intros [?]. rewrite /Split. rewrite -(Qp.div_2 q). by f_equal.
  Qed.

  Goal forall q, Split q (q/2) (q/2).
  Proof. apply _. Abort.
  Goal forall q, Split (q/2) (q/4) (q/4).
  Proof. apply _. Abort.

End split_frac.

#[global] Instance split_frac_split q q1 q2 :
  split_frac.SPLIT q q1 q2 -> SplitFrac q q1 q2 | 10.
Proof. by case. Qed.

(** ** Combining fractions *)
(**
[CombineFrac q1 q2 q] combines fractions [q1], [q2] into [q = q1 +
q2], adjusting the output [q] for readability.
*)
Class CombineFrac (q1 q2 q : Qp) : Prop := combine_frac : (q1 + q2)%Qp = q.
#[global] Hint Mode CombineFrac + + - : typeclass_instances.
#[global] Arguments CombineFrac : simpl never.
#[global] Arguments combine_frac _ _ {_ _} : assert.

#[global] Instance combine_frac_add q1 q2 q :
  QpTC.ADD q1 q2 q -> CombineFrac q1 q2 q | 10.
Proof. by case. Qed.
