(*
 * Copyright (c) 2023 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bluerock.lang.cpp.logic.heap_pred.prelude.
Require Import bluerock.lang.cpp.logic.heap_pred.valid.
Require Import bluerock.lang.cpp.logic.heap_pred.null.

#[local] Set Printing Coercions.
Implicit Types (σ : genv) (p : ptr) (o : offset).

mlock
Definition structR `{Σ : cpp_logic} {σ : genv} (cls : globname) (q : cQp.t) : Rep :=
  as_Rep (fun p => struct_padding p cls q).

mlock
Definition unionR `{Σ : cpp_logic} {σ : genv} (cls : globname) (q : cQp.t) (i : option nat) : Rep :=
  as_Rep (fun p => union_padding p cls q i).

Section aggregate.
  Context `{Σ : cpp_logic} {σ : genv}.
  Variable cls : globname.

  #[global] Instance structR_fractional : CFractional (structR cls).
  Proof. rewrite structR.unlock; eapply as_Rep_cfractional => ?; eapply struct_padding_fractional. Qed.
  #[global] Instance structR_cfractional_eta : CFractional (fun q => structR cls q).
  Proof.  apply structR_fractional. Qed.

  #[global] Instance structR_timeless : Timeless2 structR.
  Proof. rewrite structR.unlock; apply _. Qed.
  #[global] Instance structR_frac_valid : CFracValid0 (structR cls).
  Proof. rewrite structR.unlock. constructor. intros; apply as_Rep_only_provable_observe. refine _. Qed.
  #[global] Instance structR_frac_valid_eta : CFracValid0 (fun q => structR cls q).
  Proof. apply structR_frac_valid. Qed.

  #[global] Instance structR_as_fractional : AsCFractional0 (structR cls).
  Proof. solve_as_cfrac. Qed.

  #[global] Instance union_fractional : CFractional1 (unionR cls).
  Proof. rewrite unionR.unlock; intros; eapply as_Rep_cfractional => ?; eapply union_padding_fractional. Qed.
  #[global] Instance union_timeless : Timeless3 unionR.
  Proof. rewrite unionR.unlock; apply _. Qed.
  #[global] Instance union_frac_valid : CFracValid1 (unionR cls).
  Proof. rewrite unionR.unlock. constructor. intros; apply as_Rep_only_provable_observe. refine _. Qed.

  #[global] Instance union_as_fractional : AsCFractional1 (unionR cls).
  Proof. solve_as_cfrac. Qed.

  #[global] Instance structR_type_ptr_observe : forall q cls, Observe (type_ptrR (Tnamed cls)) (structR cls q).
  Proof.
    intros; eapply observe_at; intros.
    rewrite _at_type_ptrR structR.unlock _at_as_Rep. refine _.
  Qed.
  #[global] Instance structR_strict_valid_observe q : Observe svalidR (structR cls q).
  Proof. rewrite -type_ptrR_svalidR; apply _. Qed.
  #[global] Instance structR_valid_observe q : Observe validR (structR cls q).
  Proof. rewrite -svalidR_validR; apply _. Qed.

  #[global] Instance structR_nonnull q : Observe nonnullR (structR cls q).
  Proof.
    iIntros "H".
    iDestruct (observe (type_ptrR _) with "H") as "#T".
    iApply (observe with "T").
  Qed.


  #[global] Instance unionR_type_ptr_observe : forall q i, Observe (type_ptrR (Tnamed cls)) (unionR cls q i).
  Proof.
    intros; eapply observe_at; intros.
    rewrite _at_type_ptrR unionR.unlock _at_as_Rep. refine _.
  Qed.
  #[global] Instance unionR_strict_valid_observe q i : Observe svalidR (unionR cls q i).
  Proof. rewrite -type_ptrR_svalidR; apply _. Qed.
  #[global] Instance unionR_valid_observe q i : Observe validR (unionR cls q i).
  Proof. rewrite -svalidR_validR; apply _. Qed.

  #[global] Instance unionR_nonnull q i : Observe nonnullR (unionR cls q i).
  Proof.
    iIntros "H".
    iDestruct (observe (type_ptrR _) with "H") as "#T".
    iApply (observe with "T").
  Qed.

  #[global] Instance unionR_agree q q' i i' :
      Observe2 [| i = i' |] (unionR cls q i) (unionR cls q' i').
  Proof. rewrite unionR.unlock. eapply observe_2_at.
         intros; rewrite _at_only_provable !_at_as_Rep. refine _.
  Qed.

End aggregate.
