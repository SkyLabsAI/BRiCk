(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import Stdlib.NArith.BinNat.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.syntax.supported.
Require Import skylabs.lang.cpp.semantics.genv.
Require Import skylabs.lang.cpp.semantics.values.

Import ListNotations.

Abbreviation Tm256i := (Tvector Tlonglong 4 32).
Abbreviation Tm256i_u := (Tvector Tlonglong 4 1).

Example support_accepts_m256i_type :
  check.type Tm256i = check.OK.
Proof. reflexivity. Qed.

Example support_accepts_m256i_u_type :
  check.type Tm256i_u = check.OK.
Proof. reflexivity. Qed.

Example m256i_and_m256i_u_distinct :
  Tm256i <> Tm256i_u.
Proof. discriminate. Qed.

Example size_of_m256i {σ : genv} :
  size_of σ Tm256i = Some 32%N.
Proof. reflexivity. Qed.

Example size_of_m256i_u {σ : genv} :
  size_of σ Tm256i_u = Some 32%N.
Proof. reflexivity. Qed.

Example align_of_m256i {σ : genv} :
  align_of (σ:=σ) Tm256i = Some 32%N.
Proof.
  apply (align_of_vector Tlonglong 4 32 32);
    [reflexivity | lia | exists 5%N; reflexivity | exists 1%N; lia].
Qed.

Example align_of_m256i_u {σ : genv} :
  align_of (σ:=σ) Tm256i_u = Some 1%N.
Proof.
  apply (align_of_vector Tlonglong 4 1 32);
    [reflexivity | lia | exists 0%N; reflexivity | exists 32%N; lia].
Qed.

Example is_true_vvec_none :
  is_true (Vvec (repeat 0%N 32)) = None.
Proof. reflexivity. Qed.

Example has_type_prop_zero_m256i {σ : genv} :
  has_type_prop (σ:=σ) (Vvec (repeat 0%N 32)) Tm256i.
Proof.
  apply has_vector_type.
  - rewrite repeat_length. lia.
  - rewrite repeat_length. reflexivity.
  - set (k := 32%nat); induction k as [|k IH]; simpl; constructor; [lia | exact IH].
Qed.

Example support_rejects_zero_len_vector :
  check.type (Tvector Tint 0 16) <> check.OK.
Proof. discriminate. Qed.

Example support_rejects_struct_elem_vector :
  check.type (Tvector (Tnamed "Foo") 4 16) <> check.OK.
Proof. discriminate. Qed.
