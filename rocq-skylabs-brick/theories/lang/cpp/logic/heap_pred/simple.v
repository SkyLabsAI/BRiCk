(*
 * Copyright (c) 2023 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bluerock.lang.cpp.logic.heap_pred.prelude.
Require Import bluerock.lang.cpp.logic.heap_pred.valid.

#[local] Set Printing Coercions.
Implicit Types (σ : genv) (p : ptr) (o : offset).

(** ** Object derivations
    The path from the object to its complete object.
  *)
mlock
Definition derivationR `{Σ : cpp_logic} {σ} (cls : globname) (mdc : list globname)
  (q : cQp.t) : Rep :=
    as_Rep (mdc_path cls mdc q).

mlock
Definition alignedR `{Σ : cpp_logic} {σ} (al : N) : Rep :=
  as_Rep (λ p, [| aligned_ptr al p |]).

(* [Rep] version of (to be deprecated) [aligned_ptr_ty] *)
mlock
Definition aligned_ofR `{Σ : cpp_logic} {σ} (ty : type) : Rep :=
  ∃ align : N, [| align_of ty = Some align |] ** alignedR align.

Section with_cpp.
  Context `{Σ : cpp_logic} {σ}.

  (** ** [alignedR] *)
  #[global] Instance alignedR_persistent {al} : Persistent (alignedR al).
  Proof. rewrite alignedR.unlock. apply _. Qed.
  #[global] Instance alignedR_affine {al} : Affine (alignedR al).
  Proof. rewrite alignedR.unlock. apply _. Qed.
  #[global] Instance alignedR_timeless {al} : Timeless (alignedR al).
  Proof. rewrite alignedR.unlock. apply _. Qed.

  #[global] Instance alignedR_divide_mono :
    Proper (flip N.divide ==> bi_entails) alignedR.
  Proof.
    intros m n ?.
    rewrite alignedR.unlock. constructor=>p/=. iIntros "!%".
    exact: aligned_ptr_divide_weaken.
  Qed.

  #[global] Instance alignedR_divide_flip_mono :
    Proper (N.divide ==> flip bi_entails) alignedR.
  Proof. solve_proper. Qed.

  Lemma alignedR_divide_weaken m n :
    (n | m)%N ->
    alignedR m ⊢ alignedR n.
  Proof. by move->. Qed.

  (* To use sparingly: we're deprecating [aligned_ptr] *)
  Lemma _at_alignedR (p : ptr) n :
    p |-> alignedR n -|- [| aligned_ptr n p |].
  Proof. by rewrite alignedR.unlock _at_as_Rep. Qed.

  #[global] Instance aligned_ofR_persistent {ty} : Persistent (aligned_ofR ty).
  Proof. rewrite aligned_ofR.unlock. apply _. Qed.
  #[global] Instance aligned_ofR_affine {ty} : Affine (aligned_ofR ty).
  Proof. rewrite aligned_ofR.unlock. apply _. Qed.
  #[global] Instance aligned_ofR_timeless {ty} : Timeless (aligned_ofR ty).
  Proof. rewrite aligned_ofR.unlock. apply _. Qed.

  Lemma aligned_ofR_aligned_ptr_ty p ty :
    p |-> aligned_ofR ty -|- [| aligned_ptr_ty ty p |].
  Proof.
    rewrite aligned_ofR.unlock alignedR.unlock /aligned_ptr_ty _at_exists only_provable_exist.
    f_equiv => n. rewrite _at_sep _at_as_Rep _at_only_provable.
    by iIntros "!%".
  Qed.

  Lemma type_ptrR_aligned_ofR ty :
    type_ptrR ty |-- aligned_ofR ty.
  Proof.
    apply Rep_entails_at => p.
    by rewrite _at_type_ptrR type_ptr_aligned_pure aligned_ofR_aligned_ptr_ty.
  Qed.

  Lemma type_ptr_aligned_ofR p ty :
    type_ptr ty p |-- p |-> aligned_ofR ty.
  Proof. by rewrite -type_ptrR_aligned_ofR _at_type_ptrR. Qed.

  (** ** [derivationR] *)
  #[global] Instance derivationR_timeless cls mdc q : Timeless (derivationR cls mdc q).
  Proof. rewrite derivationR.unlock. refine _. Qed.
  #[global] Instance derivationR_cfractional cls mdc : CFractional (derivationR cls mdc).
  Proof. rewrite derivationR.unlock. refine _. Qed.
  #[global] Instance derivationR_as_frac cls mdc :
    AsCFractional0 (derivationR cls mdc).
  Proof. solve_as_cfrac. Qed.

  #[global] Instance derivationR_strict_valid cls mdc q : Observe svalidR (derivationR cls mdc q).
  Proof.
    red. eapply Rep_entails_at. intros.
    rewrite derivationR.unlock _at_as_Rep _at_pers svalidR_eq _at_as_Rep.
    apply mdc_path_strict_valid.
  Qed.
  #[global] Instance mdc_path_not_null p cls path q
    : Observe [| p <> nullptr |] (p |-> derivationR cls path q).
  Proof.
    red.
    iIntros "X".
    destruct (decide (p = nullptr)); eauto.
    iDestruct (observe (p |-> svalidR) with "X") as "#SV".
    subst; rewrite _at_svalidR not_strictly_valid_ptr_nullptr.
    iDestruct "SV" as "[]".
  Qed.
End with_cpp.
