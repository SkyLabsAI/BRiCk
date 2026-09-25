(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.semantics.genv.
Require Import skylabs.lang.cpp.semantics.types.
Require Import skylabs.lang.cpp.model.simple_pred.

Import SimpleCPP.

Section with_genv.
  Context `{Σ : cpp_logic} {σ : genv}.

  Example member_pointer_encoding_matches_size cls ty v vs :
    pure_encodes (Tmember_pointer cls ty) v vs ->
    size_of σ (Tmember_pointer cls ty) = Some (N.of_nat (length vs)).
  Proof. move=> /length_encodes ->. reflexivity. Qed.

  Example undefined_member_pointer_encoding cls ty :
    pure_encodes (Tmember_pointer cls ty) VALUES_DEFS_IMPL.Vundef
      (repeat Rundef (bitsize.bytesNat (member_pointer_bitsize σ))).
  Proof. reflexivity. Qed.
End with_genv.
