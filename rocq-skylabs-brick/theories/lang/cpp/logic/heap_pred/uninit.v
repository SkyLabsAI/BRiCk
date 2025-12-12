(*
 * Copyright (c) 2023 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bluerock.lang.cpp.logic.heap_pred.prelude.
Require Import bluerock.lang.cpp.logic.heap_pred.valid.
Require Import bluerock.lang.cpp.logic.heap_pred.null.
Require Import bluerock.lang.cpp.logic.heap_pred.tptsto.

#[local] Set Printing Coercions.
Implicit Types (σ : genv) (p : ptr) (o : offset).

(**
  [uninitR ty q]: the argument pointer points to an uninitialized value [Vundef] of C++ type [ty].
  Unlike [primR], does not imply [has_type_prop].

  NOTE the [ty] argument *must* be a primitive type.

  TODO is it possible to generalize this to support aggregate types? structures seem easy enough
      but unions seem more difficult, possibly we can achieve that through the use of disjunction?
*)
mlock
Definition uninitR `{Σ : cpp_logic} {σ : genv} (ty : Rtype) (q : cQp.t) : Rep :=
  tptstoR ty q Vundef.

Section with_cpp.
  Context `{Σ : cpp_logic} {σ : genv}.

  #[global] Instance uninitR_timeless ty q
    : Timeless (uninitR ty q).
  Proof. rewrite uninitR.unlock. apply _. Qed.

  #[global] Instance uninitR_cfractional ty :
    CFractional (uninitR ty).
  Proof. rewrite uninitR.unlock. apply _. Qed.
  #[global] Instance unintR_as_fractional ty :
    AsCFractional0 (uninitR ty).
  Proof. solve_as_cfrac. Qed.

  #[global] Instance uninitR_observe_frac_valid ty :
    CFracValid0 (uninitR ty).
  Proof. rewrite uninitR.unlock. solve_cfrac_valid. Qed.

  Lemma uninitR_tptstoR ty q : uninitR ty q -|- tptstoR ty q Vundef.
  Proof. by rewrite uninitR.unlock tptstoR.unlock. Qed.

  #[global]
  Instance uninitR_type_ptr_observe ty q : Observe (type_ptrR ty) (uninitR ty q).
  Proof. rewrite uninitR_tptstoR. apply _. Qed.

  #[global]
  Instance uninitR_valid_observe {ty q} : Observe validR (uninitR ty q).
  Proof. rewrite -svalidR_validR -type_ptrR_svalidR; refine _. Qed.

  #[global]
  Instance uninitR_nonnull_observe {ty q} :
    Observe nonnullR (uninitR ty q).
  Proof. rewrite uninitR_tptstoR. apply _. Qed.

  Lemma nullptr_uninitR ty q : nullptr |-> uninitR ty q |-- False.
  Proof.
    rewrite uninitR_tptstoR tptstoR_nonnull _at_pers _at_nonnullR. eauto.
  Qed.

End with_cpp.
