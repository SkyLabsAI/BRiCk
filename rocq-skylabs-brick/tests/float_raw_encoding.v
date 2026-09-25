(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.prelude.arith.z_to_bytes.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.semantics.genv.
Require Import skylabs.lang.cpp.semantics.values.
Require Import skylabs.lang.cpp.logic.raw.

Open Scope pstring_scope.

Set Default Proof Using "Type*".

Section with_env.
  Context {σ : genv}.

  (* The unsupported-format premise must be enforced by the axiom and both
     derived entry points. Each failure is false = true, not elaboration. *)
  Fail Check (@raw_bytes_of_val_float σ float_type.Flongdouble
    (float_value.zero float_type.Flongdouble) [] eq_refl).
  Fail Check (@raw_bytes_of_val_float_intro σ float_type.Flongdouble
    (float_value.zero float_type.Flongdouble) eq_refl).
  Fail Check (@raw_bytes_of_val_float_elim σ float_type.Flongdouble
    (float_value.zero float_type.Flongdouble) [] eq_refl).

  Lemma supported_float_encoding ft (f : float_type.car ft) rs :
    float_type.supported ft = true ->
    raw_bytes_of_val σ (Tfloat_ ft) (Vfloat ft f) rs <->
    rs = float_raw_bytes σ f.
  Proof. apply raw_bytes_of_val_float. Qed.

  (* The ordinary binary32 representation is preserved in both byte orders. *)
  Lemma binary32_one_little rs :
    genv_byte_order σ = Little ->
    raw_bytes_of_val σ "float" (Vfloat float_type.Ffloat
      (float_value.of_bits float_type.Ffloat 1065353216)) rs ->
    rs = raw_int_byte <$> [0; 0; 128; 63]%N.
  Proof.
    intros Hbo Hraw.
    apply raw_bytes_of_val_float_elim in Hraw; last reflexivity.
    rewrite Hraw /float_raw_bytes Hbo _Z_to_bytes_eq. f_equal.
  Qed.

  Lemma binary32_one_big rs :
    genv_byte_order σ = Big ->
    raw_bytes_of_val σ "float" (Vfloat float_type.Ffloat
      (float_value.of_bits float_type.Ffloat 1065353216)) rs ->
    rs = raw_int_byte <$> [63; 128; 0; 0]%N.
  Proof.
    intros Hbo Hraw.
    apply raw_bytes_of_val_float_elim in Hraw; last reflexivity.
    rewrite Hraw /float_raw_bytes Hbo _Z_to_bytes_eq. f_equal.
  Qed.

  (* Object size does not require knowing the unsupported format's encoding. *)
  Lemma longdouble_object_size (f : float_type.car float_type.Flongdouble) rs :
    raw_bytes_of_val σ (Tfloat_ float_type.Flongdouble)
      (Vfloat float_type.Flongdouble f) rs ->
    length rs = 16%nat.
  Proof. apply raw_bytes_of_val_float_length. Qed.
End with_env.

(* The reverse integer/float reinterpretation rule already excludes this
   format at every integer rank, so it cannot bypass the new support guard. *)
Lemma longdouble_not_bits_compatible sz :
  ~ float_bits_compatible sz float_type.Flongdouble.
Proof. intros [_ Hwidth]. vm_compute in Hwidth. discriminate. Qed.

Set Printing Width 4611686018427387903.
Set Printing Fully Qualified.
Print Assumptions supported_float_encoding.
Print Assumptions binary32_one_little.
Print Assumptions binary32_one_big.
Print Assumptions longdouble_object_size.
Print Assumptions longdouble_not_bits_compatible.
