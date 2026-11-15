(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.semantics.

Set Default Proof Using "Type*".
#[local] Open Scope Z_scope.

Definition shift_tu (ver : lang_version.t) : translation_unit :=
  empty_tu (abi.mkT int_rank.Ilong Signed Signed Little ver).

Section with_genv.
  Context {σ : genv}.

  (* The high byte is promoted to signed int before shifting. *)
  Example shl_cpp17_high_byte :
    eval_binop_pure (shift_tu lang_version.Cpp17) Bshl
      "int" "int" "int" 128 24 (-2147483648).
  Proof.
    change (eval_binop_pure (shift_tu lang_version.Cpp17) Bshl "int" "int" "int" 128 24
      (Vint (to_signed (int_rank.bitsize int_rank.Iint) (Z.shiftl 128 24)))).
    eapply eval_shl with (w := int_rank.Iint) (sgn := Signed);
      try typeclasses eauto; try apply has_int_type; vm_compute;
      intuition (try apply has_int_type; vm_compute; intuition congruence).
  Qed.

  Example shl_cpp17_max_byte :
    eval_binop_pure (shift_tu lang_version.Cpp17) Bshl
      "int" "int" "int" 255 24 (-16777216).
  Proof.
    change (eval_binop_pure (shift_tu lang_version.Cpp17) Bshl "int" "int" "int" 255 24
      (Vint (to_signed (int_rank.bitsize int_rank.Iint) (Z.shiftl 255 24)))).
    eapply eval_shl with (w := int_rank.Iint) (sgn := Signed);
      try typeclasses eauto; try apply has_int_type; vm_compute;
      intuition (try apply has_int_type; vm_compute; intuition congruence).
  Qed.

  Example shl_cpp20_negative :
    eval_binop_pure (shift_tu lang_version.Cpp20) Bshl
      "int" "int" "int" (-1) 1 (-2).
  Proof.
    change (eval_binop_pure (shift_tu lang_version.Cpp20) Bshl "int" "int" "int" (-1) 1
      (Vint (to_signed (int_rank.bitsize int_rank.Iint) (Z.shiftl (-1) 1)))).
    eapply eval_shl with (w := int_rank.Iint) (sgn := Signed);
      try typeclasses eauto; try apply has_int_type; vm_compute;
      intuition (try apply has_int_type; vm_compute; intuition congruence).
  Qed.

  Example shl_cpp20_wrap :
    eval_binop_pure (shift_tu lang_version.Cpp20) Bshl
      "int" "int" "int" 2147483647 2 (-4).
  Proof.
    change (eval_binop_pure (shift_tu lang_version.Cpp20) Bshl "int" "int" "int" 2147483647 2
      (Vint (to_signed (int_rank.bitsize int_rank.Iint) (Z.shiftl 2147483647 2)))).
    eapply eval_shl with (w := int_rank.Iint) (sgn := Signed);
      try typeclasses eauto; try apply has_int_type; vm_compute;
      intuition (try apply has_int_type; vm_compute; intuition congruence).
  Qed.

  Example shr_cpp20_negative :
    eval_binop_pure (shift_tu lang_version.Cpp20) Bshr
      "int" "int" "int" (-127) 4 (-8).
  Proof.
    change (eval_binop_pure (shift_tu lang_version.Cpp20) Bshr
      "int" "int" "int" (-127) 4 (Vint (Z.shiftr (-127) 4))).
    eapply eval_shr with (w := int_rank.Iint) (sgn := Signed);
      try typeclasses eauto; try apply has_int_type; vm_compute;
      intuition (try apply has_int_type; vm_compute; intuition congruence).
  Qed.

  Example shr_cpp17_nonnegative :
    eval_binop_pure (shift_tu lang_version.Cpp17) Bshr
      "int" "int" "int" 255 4 15.
  Proof.
    change (eval_binop_pure (shift_tu lang_version.Cpp17) Bshr
      "int" "int" "int" 255 4 (Vint (Z.shiftr 255 4))).
    eapply eval_shr with (w := int_rank.Iint) (sgn := Signed);
      try typeclasses eauto; try apply has_int_type; vm_compute;
      intuition (try apply has_int_type; vm_compute; intuition congruence).
  Qed.

  Example shl_unsigned_wrap :
    eval_binop_pure (shift_tu lang_version.Cpp17) Bshl
      "unsigned int" "long" "unsigned int" 4294967295 1 4294967294.
  Proof.
    change (eval_binop_pure (shift_tu lang_version.Cpp17) Bshl
      "unsigned int" "long" "unsigned int" 4294967295 1
      (Vint (trim 32 (Z.shiftl 4294967295 1)))).
    eapply eval_shl with (w := int_rank.Iint) (sgn := Unsigned);
      try typeclasses eauto; try apply has_int_type; vm_compute; intuition congruence.
  Qed.

End with_genv.
