(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.semantics.genv.
Require Import skylabs.lang.cpp.semantics.types.

#[local] Definition member_type : type := "int C::*"%cpp_type.

#[local] Definition layout_env (sz : bitsize) : genv :=
  {| genv_tu := empty_tu abi.x64_linux; member_pointer_bitsize := sz |}.

(* The new parameter must not be replaced by the ordinary pointer width. *)
Example distinct_pointer_widths :
  pointer_size (layout_env bitsize.W128) = 8%N /\
  size_of (layout_env bitsize.W128) member_type = Some 16%N.
Proof. split; reflexivity. Qed.

Example qualified_member_pointer_array :
  size_of (layout_env bitsize.W32) (Tarray (Tconst member_type) 3) = Some 12%N.
Proof. reflexivity. Qed.

Example extension_cannot_change_member_pointer_width :
  ~ genv_leq (layout_env bitsize.W64) (layout_env bitsize.W128).
Proof. move=> /member_pointer_bitsize_le. discriminate. Qed.

Section with_genv.
  Context {σ : genv}.

  Example member_pointer_size_instance cls ty :
    SizeOf (Tmember_pointer cls ty) (member_pointer_size σ).
  Proof. apply _. Qed.

  Example member_pointer_alignment cls ty :
    is_Some (@align_of σ (Tmember_pointer cls ty)).
  Proof.
    destruct (align_of_size_of' _ _ (size_of_member_pointer cls ty)) as [al [Hal _]].
    by exists al.
  Qed.
End with_genv.
