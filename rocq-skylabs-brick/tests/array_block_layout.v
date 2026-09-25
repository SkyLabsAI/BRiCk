(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.semantics.
Require Import skylabs.lang.cpp.logic.pred.
Require Import skylabs.lang.cpp.logic.heap_pred.
Require Import skylabs.lang.cpp.logic.layout.

Set Default Proof Using "Type*".

Section with_cpp.
  Context `{Σ : cpp_logic} {σ : genv}.

  (* The direct proof from tblockR does not use either admitted decomposition. *)
  Example empty_array_layout t q sz :
    size_of σ t = Some sz ->
    tblockR (Tarray t 0) q -|- validR ** aligned_ofR t.
  Proof. apply tblockR_array_zero. Qed.

  Example empty_array_byte_decomposition t q sz :
    size_of σ t = Some sz ->
    tblockR (Tarray t 0) q -|- aligned_ofR t ** validR.
  Proof.
    move=> Hsz. rewrite (tblockR_array_better t 0 q sz) //=.
    by rewrite _offsetR_sub_0 ?right_id.
  Qed.

  Example empty_array_typed_decomposition t q sz :
    size_of σ t = Some sz ->
    tblockR (Tarray t 0) q -|- aligned_ofR t ** validR.
  Proof.
    move=> Hsz. rewrite tblockR_array; last by eexists.
    rewrite /= _offsetR_sub_0 ?right_id //; by eexists.
  Qed.

  (* A zero length must not make an unsized element type admissible. *)
  Example empty_array_unsized q :
    tblockR (Tarray "void" 0) q -|- False.
  Proof. by rewrite /tblockR. Qed.
End with_cpp.
