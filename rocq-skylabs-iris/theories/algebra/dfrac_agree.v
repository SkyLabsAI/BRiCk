(*
 * Copyright (C) 2022 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import iris.algebra.frac.	(** for [fracO] *)
Require Import iris.algebra.proofmode_classes.	(** for [IsOp] *)
Require Export iris.algebra.lib.dfrac_agree.
Require Export bluerock.prelude.base.
Set Printing Coercions.

Lemma qple_dfrac_own_incl {SI : sidx} q1 q2 :
  (q1 ≤ q2)%Qp ↔ DfracOwn q1 ≼ DfracOwn q2 ∨ DfracOwn q1 = DfracOwn q2.
Proof.
  by rewrite dfrac_own_included (inj_iff DfracOwn) -Qp.le_lteq.
Qed.

Definition dfrac_agreeRF {SI : sidx} (F : oFunctor) : rFunctor :=
  constRF dfracR * agreeRF F.

(**
Iris left [to_frac_agree] transparent in [typeclass_instances] in an
attempt to reuse instances for the underlying [to_dfrac_agree].
Unfortunately, some useful instances aren't derivable. We declare what
we need and, orthogonally, mark [to_frac_agree] TC opaque to speed up
type class resolution.
*)

Section dfrac_agree.
  Context {SI : sidx} {A : ofe}.
  Implicit Types (q : Qp) (d : dfrac) (a : A).

  Lemma to_dfrac_agree_valid d a : ✓ to_dfrac_agree d a -> ✓ d.
  Proof. by rewrite/to_dfrac_agree pair_valid=>-[]. Qed.

  #[global] Instance to_frac_agree_ne q : NonExpansive (@to_frac_agree _ A q).
  Proof. Fail apply _. apply to_dfrac_agree_ne. Qed.
  #[global] Instance to_frac_agree_proper q :
    Proper (equiv ==> equiv) (@to_frac_agree _ A q).
  Proof. Fail apply _. apply to_dfrac_agree_proper. Qed.

  #[global] Instance to_frac_agree_exclusive a :
    Exclusive (to_frac_agree 1 a) := _.
  #[global] Instance to_frac_agree_discrete q a :
    Discrete a -> Discrete (to_frac_agree q a) := _.
  #[global] Instance to_frac_agree_injN n :
    Inj2 (dist n) (dist n) (dist n) (@to_frac_agree _ A).
  Proof.
    Fail apply _. by intros q1 a1 q2 a2 [[= ->]->]%to_dfrac_agree_injN.
  Qed.
  #[global] Instance to_frac_agree_inj :
    Inj2 equiv equiv equiv (@to_frac_agree _ A).
  Proof.
    Fail apply _. by intros q1 a1 q2 a2 [[= ->]->]%to_dfrac_agree_inj.
  Qed.

  (** IPM support *)

  #[global] Instance to_dfrac_agree_is_op a d d1 d2 :
    IsOp d d1 d2 ->
    IsOp' (to_dfrac_agree d a) (to_dfrac_agree d1 a) (to_dfrac_agree d2 a).
  Proof. rewrite/IsOp'/IsOp=>->. apply dfrac_agree_op. Qed.
  #[global] Instance to_frac_agree_is_op a q q1 q2 :
    IsOp q q1 q2 ->
    IsOp' (to_frac_agree q a) (to_frac_agree q1 a) (to_frac_agree q2 a) := _.
End dfrac_agree.
#[global] Hint Opaque to_frac_agree : typeclass_instances.
