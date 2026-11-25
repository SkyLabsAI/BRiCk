(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.prelude.base.
Require Import skylabs.prelude.arith.z_to_bytes.
Require Import skylabs.iris.extra.proofmode.proofmode.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.semantics.
Require Import skylabs.lang.cpp.logic.heap_pred.
Require Import skylabs.lang.cpp.logic.raw.

Section tests.
  Context `{Σ : cpp_logic} {σ : genv}.

  Example signed_zero sz :
    raw_bytes_of_val σ (Tnum sz Signed) (Vint 0)
      (replicate (N.to_nat (int_rank.bytesN sz)) (raw_int_byte 0)).
  Proof. apply raw_bytes_of_val_int_zeros. Qed.

  Example short_minus_one :
    raw_bytes_of_val σ "short"%cpp_type (Vint (-1)) (replicate 2 (raw_int_byte 255)).
  Proof.
    rewrite raw_byte_of_int_eq. exists [255%N; 255%N].
    split; last done. split.
    - repeat constructor; apply has_type_byte_bound; lia.
    - rewrite _Z_from_bytes_eq /_Z_from_bytes_def /_Z_from_bytes_le.
      destruct (genv_byte_order σ); vm_compute; reflexivity.
  Qed.

  Example short_zero_from_bytes q :
    type_ptrR "short"%cpp_type ** rawsR q (replicate 2 (raw_int_byte 0)) |--
    primR "short"%cpp_type q (Vint 0).
  Proof.
    rewrite primR_to_rawsR. iIntros "(T & R)".
    iExists _. iFrame. iPureIntro. apply raw_bytes_of_val_int_zeros.
  Qed.

  Example split_short q :
    anyR "short"%cpp_type q |-- anyR "unsigned char[2]"%cpp_type q ** type_ptrR "short"%cpp_type.
  Proof. rewrite decode_int_anyR. done. Qed.
End tests.
