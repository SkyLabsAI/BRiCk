(*
 * Copyright (c) 2023-2025 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bluerock.lang.cpp.logic.heap_pred.prelude.
Require Import bluerock.lang.cpp.logic.heap_pred.valid.

#[local] Set Printing Coercions.
Implicit Types (σ : genv) (p : ptr) (o : offset).

mlock Definition nullR `{Σ : cpp_logic} : Rep :=
  as_Rep (fun addr => [| addr = nullptr |]).

mlock Definition nonnullR `{Σ : cpp_logic} : Rep :=
  as_Rep (fun addr => [| addr <> nullptr |]).

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.

  Lemma _at_nullR p :
      _at p nullR -|- [| p = nullptr |].
  Proof. by rewrite nullR.unlock _at_as_Rep. Qed.

  #[global] Instance nullR_persistent : Persistent nullR.
  Proof. rewrite nullR.unlock. apply _. Qed.
  #[global] Instance nullR_affine : Affine nullR.
  Proof. rewrite nullR.unlock. apply _. Qed.
  #[global] Instance nullR_timeless : Timeless nullR.
  Proof. rewrite nullR.unlock. apply _. Qed.

  Lemma _at_nonnullR p : _at p nonnullR -|- [| p <> nullptr |].
  Proof. by rewrite nonnullR.unlock _at_as_Rep. Qed.

  #[global] Instance nonnullR_persistent : Persistent nonnullR.
  Proof. rewrite unlock. apply _. Qed.
  #[global] Instance nonnullR_affine : Affine nonnullR.
  Proof. rewrite unlock. apply _. Qed.
  #[global] Instance nonnullR_timeless : Timeless nonnullR.
  Proof. rewrite unlock. apply _. Qed.

  #[global] Instance type_ptrR_observe_nonnull ty :
    Observe nonnullR (type_ptrR ty).
  Proof.
    rewrite nonnullR.unlock type_ptrR_eq /type_ptrR_def.
    exact: as_Rep_observe.
  Qed.

  Lemma null_nonnull (R : Rep) : nullR |-- nonnullR -* R.
  Proof.
    rewrite nullR.unlock nonnullR.unlock.
    constructor=>p /=. rewrite monPred_at_wand/=.
    by iIntros "->" (? <-%ptr_rel_elim) "%".
  Qed.

  Lemma null_validR : nullR |-- validR.
  Proof.
    rewrite nullR.unlock validR_eq /validR_def.
    constructor => p /=. iIntros "->". iApply valid_ptr_nullptr.
  Qed.

  #[global]
  Instance null_valid_observe : Observe validR nullR.
  Proof. rewrite -null_validR. refine _. Qed.

  Lemma has_type_nullptr p :
    has_type (Vptr p) Tnullptr -|- p |-> nullR.
  Proof. by rewrite has_type_nullptr' nullR.unlock _at_as_Rep. Qed.

End with_cpp.

#[deprecated(note="since 2022-04-07; use `nullR` instead")]
Notation is_null := nullR (only parsing).
#[deprecated(note="since 2022-04-07; use `nullR.unlock` instead")]
Notation is_null_eq := nullR.unlock (only parsing).
(*
#[deprecated(note="since 2022-04-07; use `nullR_def` instead")]
Notation is_null_def := nullR_def (only parsing).
*)
