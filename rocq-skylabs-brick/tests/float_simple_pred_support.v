(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import Stdlib.ZArith.BinInt.
Require Import Stdlib.micromega.Lia.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.semantics.genv.
Require Import skylabs.lang.cpp.semantics.values.
Require Import skylabs.lang.cpp.model.simple_pred.

Open Scope Z_scope.

Import SimpleCPP.

Definition f16_one_bits : Z := 15360%Z.
Definition f32_one_bits : Z := 1065353216%Z.
Definition f128_one_bits : Z :=
  85065399433376081038215121361612832768%Z.

Definition f16_one : float_type.car float_type.Ffloat16 :=
  float_value.of_bits float_type.Ffloat16 f16_one_bits.
Definition f32_one : float_type.car float_type.Ffloat :=
  float_value.of_bits float_type.Ffloat f32_one_bits.
Definition f128_one : float_type.car float_type.Ffloat128 :=
  float_value.of_bits float_type.Ffloat128 f128_one_bits.

Section pure_encoding_tests.
  Context `{Σ : cpp_logic} {σ : genv}.

  Example pure_encodes_float16_one :
    pure_encodes Tfloat16 (VALUES_DEFS_IMPL.Vfloat float_type.Ffloat16 f16_one)
      (Z_to_bytes bitsize.W16 Unsigned f16_one_bits).
  Proof.
    rewrite /pure_encodes /=.
    split; [reflexivity|].
    split.
    - replace (float_value.to_bits f16_one) with f16_one_bits.
      + rewrite /in_Z_to_bytes_bounds /f16_one_bits /=.
        change (0 <= 15360 /\ 15360 < 65536)%Z. lia.
      + symmetry. apply float_value.to_of_bits. change (0 <= 15360 < 65536)%Z. lia.
    - reflexivity.
  Qed.

  Example pure_encodes_float32_one :
    pure_encodes Tfloat (VALUES_DEFS_IMPL.Vfloat float_type.Ffloat f32_one)
      (Z_to_bytes bitsize.W32 Unsigned f32_one_bits).
  Proof.
    rewrite /pure_encodes /=.
    split; [reflexivity|].
    split.
    - replace (float_value.to_bits f32_one) with f32_one_bits.
      + rewrite /in_Z_to_bytes_bounds /f32_one_bits /=.
        change (0 <= 1065353216 /\ 1065353216 < 4294967296)%Z. lia.
      + symmetry. apply float_value.to_of_bits.
        change (0 <= 1065353216 < 4294967296)%Z. lia.
    - reflexivity.
  Qed.

  Example pure_encodes_float128_one :
    pure_encodes Tfloat128 (VALUES_DEFS_IMPL.Vfloat float_type.Ffloat128 f128_one)
      (Z_to_bytes bitsize.W128 Unsigned f128_one_bits).
  Proof.
    rewrite /pure_encodes /=.
    split; [reflexivity|].
    split.
    - replace (float_value.to_bits f128_one) with f128_one_bits.
      + rewrite /in_Z_to_bytes_bounds /f128_one_bits /=.
        change (0 <= 85065399433376081038215121361612832768 /\
                85065399433376081038215121361612832768 <
                340282366920938463463374607431768211456)%Z.
        lia.
      + symmetry.
        apply float_value.to_of_bits.
        change (0 <= 85065399433376081038215121361612832768 <
                340282366920938463463374607431768211456)%Z.
        lia.
    - reflexivity.
  Qed.

  Example pure_encodes_float16_undef_length vs :
    pure_encodes Tfloat16 VALUES_DEFS_IMPL.Vundef vs -> length vs = 2%nat.
  Proof.
    intro Henc.
    exact (length_encodes Tfloat16 VALUES_DEFS_IMPL.Vundef vs Henc).
  Qed.

  Example pure_encodes_float128_undef_length vs :
    pure_encodes Tfloat128 VALUES_DEFS_IMPL.Vundef vs -> length vs = 16%nat.
  Proof.
    intro Henc.
    exact (length_encodes Tfloat128 VALUES_DEFS_IMPL.Vundef vs Henc).
  Qed.

  Example pure_encodes_float16_rejects_float128_value vs :
    ~ pure_encodes Tfloat16 (VALUES_DEFS_IMPL.Vfloat float_type.Ffloat128 f128_one) vs.
  Proof.
    rewrite /pure_encodes /=.
    intros (Hft & _).
    discriminate Hft.
  Qed.
End pure_encoding_tests.
