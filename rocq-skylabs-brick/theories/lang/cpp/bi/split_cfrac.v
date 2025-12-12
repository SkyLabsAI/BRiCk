(*
 * Copyright (c) 2022 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Export bluerock.lang.cpp.algebra.cfrac.
Require Import bluerock.iris.extra.bi.prelude.
Require Import bluerock.iris.extra.bi.split_andb.
Require Import bluerock.iris.extra.bi.split_frac.
Require Import bluerock.iris.extra.proofmode.proofmode.
Import ChargeNotation.

#[local] Set Printing Coercions.

(** * Splitting and combining const/mutable fractional things *)
(**
Overview:

- [cQpTC.IsConst], [cQpTC.Frac] normalizing projections from
const/mutable fractions

- [SplitCFrac], [CombineCFrac] split and combine terms of type [cQp.t]
*)

(**
Our rules are syntactic: All operations appearing in input positions
should be opaque for typeclass resolution.

Most rules key on [cQp.add] and [cQp.scale] which are opaque. Rule
[combine_frac.fold_add] keys on [Qp.add] and [andb]. The former is
opaque. (We choose not to touch the opacity of [andb]. See
../../bi/split_andb.v.)
*)

#[local] Notation Cut := TCNoBackTrack.

#[local] Open Scope cQp_scope.

(** ** Operations on const/mutable fractions *)
Module cQpTC.

  (** [IsConst q b] sets [b := cQp.is_const q] with simplifications. *)
  Class IsConst (q : cQp.t) (b : bool) : Prop := is_const : cQp.is_const q = b.
  #[global] Hint Mode IsConst + - : typeclass_instances.
  #[global] Arguments IsConst : simpl never.
  #[global] Arguments is_const _ {_ _} : assert.
  Notation IS_CONST q b := (Cut (IsConst q b)) (only parsing).

  (** [Frac cq q] sets [q := cQp.frac cq] with simplifications. *)
  Class Frac (cq : cQp.t) (q : Qp) : Prop := frac : cQp.frac cq = q.
  #[global] Hint Mode Frac + - : typeclass_instances.
  #[global] Arguments Frac : simpl never.
  #[global] Arguments frac _ {_ _} : assert.
  Notation FRAC q b := (Cut (Frac q b)) (only parsing).

  (** [IsConst] *)

  #[global] Instance is_const_mk c q : IsConst (cQp.mk c q) c | 10.
  Proof. done. Qed.

  #[global] Instance is_const_scale q cq c :
    IS_CONST cq c -> IsConst (cQp.scale q cq) c | 20.
  Proof.
    intros [?]. rewrite /IsConst.
    by rewrite cQp.is_const_scale is_const.
  Qed.

  #[global] Instance is_const_add cq1 cq2 c1 c2 c :
    IS_CONST cq1 c1 -> IS_CONST cq2 c2 -> CombineAndB c1 c2 c ->
    IsConst (cq1 + cq2) c | 20.
  Proof.
    intros [?] [?] ?. rewrite /IsConst.
    by rewrite cQp.is_const_add !is_const combine_andb.
  Qed.

  #[global] Instance is_const_var q : IsConst q (cQp.is_const q) | 50.
  Proof. done. Qed.

  (** [Frac] *)

  #[global] Instance frac_mk c q : Frac (cQp.mk c q) q | 10.
  Proof. done. Qed.

  #[global] Instance frac_scale q1 q2 q cq :
    FRAC cq q2 -> QpTC.MUL q1 q2 q ->
    Frac (cQp.scale q1 cq) q | 20.
  Proof.
    intros [?] [?]. rewrite /Frac.
    by rewrite cQp.frac_scale frac QpTC.mul.
  Qed.

  #[global] Instance frac_add cq1 cq2 q1 q2 q :
    FRAC cq1 q1 -> FRAC cq2 q2 -> QpTC.ADD q1 q2 q ->
    Frac (cq1 + cq2) q | 20.
  Proof.
    intros [?] [?] [?]. rewrite /Frac.
    by rewrite cQp.frac_add !frac QpTC.add.
  Qed.

  #[global] Instance frac_var cq : Frac cq (cQp.frac cq) | 50.
  Proof. done. Qed.

End cQpTC.

(** ** Splitting const/mutable fractions *)
(**
[SplitCFrac q q1 q2] splits [q : cQp.t] into [q1], [q2] s.t. [q = q1 +
q2], adjusting the outputs [q1], [q2] for readabilty.
*)
Class SplitCFrac (cv cv1 cv2 : cQp.t) : Prop := split_cfrac : cv = cv1 + cv2.
#[global] Hint Mode SplitCFrac + - - : typeclass_instances.
#[global] Arguments SplitCFrac : simpl never.
#[global] Arguments split_cfrac _ {_ _ _} : assert.

Module split_cfrac.

  (**
  We use this auxiliary judgment to [Cut] in [SplitCFrac].
  *)
  Class Split (q q1 q2 : cQp.t) : Prop := split : q = q1 + q2.
  #[global] Hint Mode Split + - - : typeclass_instances.
  #[global] Arguments Split : simpl never.
  #[global] Arguments split _ {_ _ _} : assert.
  Notation SPLIT q q1 q2 := (Cut (Split q q1 q2)) (only parsing).

  (** Splitting on [cQp.add] is immediate *)

  #[global] Instance split_add q1 q2 : Split (q1 + q2) q1 q2 | 10.
  Proof. done. Qed.

  Goal forall q1 q2, Split (q1 ⋅ q2) q1 q2.
  Proof. apply _. Abort.

  (** Splitting on [cQp.scale q] preserves the factor [q] *)

  #[global] Instance split_scale q cv cv1 cv2 :
    SPLIT cv cv1 cv2 ->
    Split (cQp.scale q cv) (cQp.scale q cv1) (cQp.scale q cv2) | 20.
  Proof.
    intros [?]. rewrite /Split.
    by rewrite (split cv) cQp.scale_add_r.
  Qed.

  (** Default: Split componentwise *)

  #[global] Instance split_parts cq c c1 c2 q q1 q2 :
    cQpTC.IS_CONST cq c -> cQpTC.FRAC cq q ->
    SplitAndB c c1 c2 -> SplitFrac q q1 q2 ->
    Split cq (cQp.mk c1 q1) (cQp.mk c2 q2) | 50.
  Proof.
    intros [?] [?] ??. rewrite /Split cQp.add_eq/=.
    rewrite (cQp.eta cq) cQpTC.is_const cQpTC.frac. by f_equal.
  Qed.

End split_cfrac.

#[global] Instance split_cfrac_split cv cv1 cv2 :
  split_cfrac.SPLIT cv cv1 cv2 -> SplitCFrac cv cv1 cv2 | 10.
Proof. by case. Qed.

(** ** Combining const/mutable fractions *)
(**
[CombineCFrac q1 q2 q] combine [q1, q2 : cQp.t] into [q = q1 + q2],
adjusting the output [q] for readability.
*)
Class CombineCFrac (q1 q2 q : cQp.t) : Prop := combine_cfrac : q1 + q2 = q.
#[global] Hint Mode CombineCFrac + + - : typeclass_instances.
#[global] Arguments CombineCFrac : simpl never.
#[global] Arguments combine_cfrac _ _ {_ _} : assert.

Module combine_cfrac.

  (**
  [Fold p q] folds occurrences of [cQp.add] and eliminates occurrences
  of eta-expanded [cQp.mk] in [p] to produce [q].
  *)
  Class Fold (p q : cQp.t) : Prop := fold : p = q.
  #[global] Hint Mode Fold + - : typeclass_instances.
  #[global] Arguments Fold : simpl never.
  #[global] Arguments fold _ {_ _} : assert.
  Notation FOLD p q := (Cut (Fold p q)) (only parsing).

  #[global] Instance fold_eta q :
    Fold (cQp.mk (cQp.is_const q) (cQp.frac q)) q | 10.
  Proof. done. Qed.

  (** Account for [Qp.Add]'s [q + q --> 2q] *)
  #[global] Instance fold_add_diag q :
    Fold (cQp.mk (cQp.is_const q) (2 * cQp.frac q)) (q + q) | 10.
  Proof.
    rewrite /Fold cQp.add_eq.
    by rewrite andb_diag Qp.add_diag.
  Qed.

  #[global] Instance fold_scale p q' q :
    FOLD q' q ->
    Fold (cQp.scale p q') (cQp.scale p q) | 20.
  Proof.
    intros [?]. rewrite /Fold. by rewrite (fold q').
  Qed.

  #[global] Instance fold_add p1 p2 q1 q2 :
    FOLD p1 q1 -> FOLD p2 q2 ->
    Fold (Reduce (cQp.add p1 p2)) (cQp.add q1 q2) | 20.
  Proof.
    intros [?] [?]. rewrite /Fold.
    by rewrite (fold p1) (fold p2).
  Qed.

  #[global] Instance fold_skip q : Fold q q | 50.
  Proof. done. Qed.

  (**
  We use this auxiliary judgment to [Cut] in [CombineCFrac].
  *)
  Class Combine (q1 q2 q : cQp.t) : Prop := combine : q1 + q2 = q.
  #[global] Hint Mode Combine + + - : typeclass_instances.
  #[global] Arguments Combine : simpl never.
  #[global] Arguments combine _ _ {_ _} : assert.
  Notation COMBINE q1 q2 q := (Cut (Combine q1 q2 q)) (only parsing).

  (** Combining terms of the form [cQp.scale p] preserves that structure *)

  #[global] Instance combine_scale p q1 q2 q :
    COMBINE q1 q2 q ->
    Combine (cQp.scale p q1) (cQp.scale p q2) (cQp.scale p q) | 20.
  Proof.
    intros [?]. rewrite /Combine.
    by rewrite -cQp.scale_add_r combine.
  Qed.

  (** Default: Combine componentwise *)

  #[global] Instance combine_parts cq1 cq2 cq c1 c2 c q1 q2 q :
    cQpTC.IS_CONST cq1 c1 -> cQpTC.FRAC cq1 q1 ->
    cQpTC.IS_CONST cq2 c2 -> cQpTC.FRAC cq2 q2 ->
    CombineAndB c1 c2 c -> CombineFrac q1 q2 q -> FOLD (cQp.mk c q) cq ->
    Combine cq1 cq2 cq | 50.
  Proof.
    intros [?] [?] [?] [?] ?? [<-]. rewrite /Combine cQp.add_eq.
    rewrite !cQpTC.is_const !cQpTC.frac. by f_equal.
  Qed.

End combine_cfrac.

#[global] Instance combine_cfrac_add q1 q2 q :
  combine_cfrac.COMBINE q1 q2 q -> CombineCFrac q1 q2 q | 10.
Proof. by case. Qed.
