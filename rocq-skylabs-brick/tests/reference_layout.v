(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.semantics.genv.
Require Import skylabs.lang.cpp.semantics.types.

Section with_genv.
  Context {σ : genv}.

  (* These are reference-cell sizes, independent of the referent's layout.
     C++ sizeof/alignof expressions erase references before querying layout. *)
  Example lvalue_reference_size : SizeOf "char&" (pointer_size σ).
  Proof. apply _. Qed.

  Example rvalue_reference_size : SizeOf "char&&" (pointer_size σ).
  Proof. apply _. Qed.

  Example reference_to_incomplete_size :
    SizeOf (Tref "Incomplete") (pointer_size σ).
  Proof. apply _. Qed.

  Example qualified_reference_size :
    size_of σ (Tconst "int&") = Some (pointer_size σ).
  Proof. reflexivity. Qed.

  Example lvalue_reference_alignment ty :
    is_Some (@align_of σ (Tref ty)).
  Proof.
    destruct (align_of_size_of' (Tref ty) _ (size_of_ref ty)) as [al [Hal _]].
    by exists al.
  Qed.

  Example rvalue_reference_alignment ty :
    is_Some (@align_of σ (Trv_ref ty)).
  Proof.
    destruct (align_of_size_of' (Trv_ref ty) _ (size_of_rv_ref ty)) as [al [Hal _]].
    by exists al.
  Qed.
End with_genv.
