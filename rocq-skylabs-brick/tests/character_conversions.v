(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.semantics.cast.
Require Import skylabs.lang.cpp.semantics.genv.
Require Import skylabs.lang.cpp.semantics.values.

(* The direct code-unit conversion agrees with the existing integral-target
   conversion for every width, source signedness and code-unit value. *)
Example char_conversion_matches_integral_conversion
    (from_bits to_bits : N) (from_sgn : signed) (n : N) :
  char_to_char from_bits from_sgn to_bits n =
    Z.to_N (of_char from_bits from_sgn to_bits Unsigned n).
Proof.
  rewrite /char_to_char of_char.unlock.
  destruct from_sgn; last reflexivity.
  case_bool_decide; last reflexivity.
  rewrite to_signed_bits_id; [reflexivity | split; lia].
Qed.

#[local] Definition char_env (sgn : signed) : genv :=
  {| genv_tu := empty_tu (abi.mkT int_rank.Ilong sgn Signed Little lang_version.Cpp23)
   ; member_pointer_bitsize := bitsize.W64 |}.

Example signed_char_widen16 :
  @conv_int (char_env Signed) (genv_tu (char_env Signed))
    "char"%cpp_type "char16_t"%cpp_type (Vchar 255) (Vchar 65535).
Proof.
  rewrite /conv_int /= /char_to_char. split; last reflexivity.
  apply has_type_prop_char'. by vm_compute.
Qed.

Example signed_char_widen32 :
  @conv_int (char_env Signed) (genv_tu (char_env Signed))
    "char"%cpp_type "char32_t"%cpp_type (Vchar 255) (Vchar 4294967295).
Proof.
  rewrite /conv_int /= /char_to_char. split; last reflexivity.
  apply has_type_prop_char'. by vm_compute.
Qed.

Example signed_high_bit_widen16 :
  @conv_int (char_env Signed) (genv_tu (char_env Signed))
    "char"%cpp_type "char16_t"%cpp_type (Vchar 128) (Vchar 65408).
Proof.
  rewrite /conv_int /= /char_to_char. split; last reflexivity.
  apply has_type_prop_char'. by vm_compute.
Qed.

Example unsigned_char_widen16 :
  @conv_int (char_env Unsigned) (genv_tu (char_env Unsigned))
    "char"%cpp_type "char16_t"%cpp_type (Vchar 255) (Vchar 255).
Proof.
  rewrite /conv_int /= /char_to_char. split; last reflexivity.
  apply has_type_prop_char'. by vm_compute.
Qed.

Example char16_narrow :
  @conv_int (char_env Signed) (genv_tu (char_env Signed))
    "char16_t"%cpp_type "char"%cpp_type (Vchar 65535) (Vchar 255).
Proof.
  rewrite /conv_int /= /char_to_char. split; last reflexivity.
  apply has_type_prop_char'. by vm_compute.
Qed.

Example signed_char_does_not_zero_extend :
  ~ @conv_int (char_env Signed) (genv_tu (char_env Signed))
      "char"%cpp_type "char16_t"%cpp_type (Vchar 255) (Vchar 255).
Proof. rewrite /conv_int /= /char_to_char. intros [_ H]. discriminate H. Qed.
