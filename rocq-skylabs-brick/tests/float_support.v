(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import Stdlib.ZArith.BinInt.
Require Import Stdlib.micromega.Lia.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.syntax.supported.
Require Import skylabs.lang.cpp.semantics.genv.
Require Import skylabs.lang.cpp.semantics.values.
Require Import skylabs.lang.cpp.semantics.cast.
Require Import skylabs.lang.cpp.semantics.cast_operator.
Require Import skylabs.lang.cpp.semantics.operator.
Require Import skylabs.lang.cpp.logic.raw.

Open Scope pstring_scope.
Open Scope Z_scope.

Definition one_float : Expr :=
  Efloat Ffloat (fp_of_bits Ffloat 1065353216%Z) Tfloat.

Definition one_double : Expr :=
  Efloat Fdouble (fp_of_bits Fdouble 4607182418800017408%Z) Tdouble.

Example support_accepts_float_type : check.type Tfloat = check.OK.
Proof. reflexivity. Qed.

Example support_accepts_double_type : check.type Tdouble = check.OK.
Proof. reflexivity. Qed.

Example support_rejects_float16_type : check.type Tfloat16 <> check.OK.
Proof. vm_compute. discriminate. Qed.

Example support_rejects_longdouble_type : check.type Tlongdouble <> check.OK.
Proof. vm_compute. discriminate. Qed.

Example support_rejects_float128_type : check.type Tfloat128 <> check.OK.
Proof. vm_compute. discriminate. Qed.

Example support_accepts_supported_float_literal : check.expr one_float = check.OK.
Proof. reflexivity. Qed.

Example support_rejects_unsupported_float_literal :
  check.expr (Efloat Ffloat16 tt Tfloat16) <> check.OK.
Proof. vm_compute. discriminate. Qed.

Example support_accepts_float_to_double_cast :
  check.expr (Ecast (Cfloat Tdouble) (Evar "f" Tfloat)) = check.OK.
Proof. reflexivity. Qed.

Example support_rejects_longdouble_to_double_cast :
  check.expr (Ecast (Cfloat Tdouble) (Evar "ld" Tlongdouble)) <> check.OK.
Proof. vm_compute. discriminate. Qed.

Example support_rejects_int_to_float16_cast :
  check.expr (Ecast (Cint2float Tfloat16) (Eint 0 Tint)) <> check.OK.
Proof. vm_compute. discriminate. Qed.

Example support_rejects_float128_to_int_cast :
  check.expr (Ecast (Cfloat2int Tint) (Evar "q" Tfloat128)) <> check.OK.
Proof. vm_compute. discriminate. Qed.

Example support_accepts_float_add :
  check.expr (Ebinop Badd one_float one_float Tfloat) = check.OK.
Proof. reflexivity. Qed.

Example support_rejects_float_mod :
  check.expr (Ebinop Bmod one_float one_float Tfloat) <> check.OK.
Proof. vm_compute. discriminate. Qed.

Example support_rejects_float_bitwise :
  check.expr (Ebinop Band one_float one_float Tfloat) <> check.OK.
Proof. vm_compute. discriminate. Qed.

Example support_rejects_float_shift :
  check.expr (Ebinop Bshl one_float (Eint 1 Tint) Tfloat) <> check.OK.
Proof. vm_compute. discriminate. Qed.

Example support_rejects_pointer_plus_float :
  check.expr (Ebinop Badd (Evar "p" (Tptr Tint)) one_float (Tptr Tint)) <> check.OK.
Proof. vm_compute. discriminate. Qed.

Example support_rejects_float_increment :
  check.expr (Epreinc (Evar "f" Tfloat) Tfloat) <> check.OK.
Proof. vm_compute. discriminate. Qed.

Example usual_float_arith_rejects_longdouble tu :
  usual_float_arith tu Tlongdouble Tdouble = None.
Proof. reflexivity. Qed.

Example convert_type_rejects_pointer_plus_float tu :
  convert_type_op tu Badd (Tptr Tint) Tfloat = None.
Proof. reflexivity. Qed.

Example convert_type_rejects_float_mod tu :
  convert_type_op tu Bmod Tfloat Tfloat = None.
Proof. reflexivity. Qed.

Example convert_type_accepts_float_double_add tu :
  convert_type_op tu Badd Tfloat Tdouble = Some (Tdouble, Tdouble, Tdouble).
Proof. reflexivity. Qed.

Example convert_type_accepts_double_float_add tu :
  convert_type_op tu Badd Tdouble Tfloat = Some (Tdouble, Tdouble, Tdouble).
Proof. reflexivity. Qed.

Example convert_type_accepts_float_int_add tu :
  convert_type_op tu Badd Tfloat Tint = Some (Tfloat, Tfloat, Tfloat).
Proof. reflexivity. Qed.

Example convert_type_accepts_int_double_add tu :
  convert_type_op tu Badd Tint Tdouble = Some (Tdouble, Tdouble, Tdouble).
Proof. reflexivity. Qed.

Example convert_type_accepts_float_double_compare tu :
  convert_type_op tu Blt Tfloat Tdouble = Some (Tdouble, Tdouble, Tbool).
Proof. reflexivity. Qed.

Example convert_type_accepts_int_double_compare tu :
  convert_type_op tu Bge Tint Tdouble = Some (Tdouble, Tdouble, Tbool).
Proof. reflexivity. Qed.

Example convert_rejects_unsupported_float_to_int {σ : genv} tu v v' :
  @convert σ tu Tlongdouble Tint v v' = False.
Proof. reflexivity. Qed.

Definition f32_one : fp_carrier Ffloat := fp_of_bits Ffloat 1065353216%Z.
Definition f64_one : fp_carrier Fdouble := fp_of_bits Fdouble 4607182418800017408%Z.
Definition f32_neg_zero : fp_carrier Ffloat := fp_of_bits Ffloat 2147483648%Z.
Definition f64_neg_zero : fp_carrier Fdouble := fp_of_bits Fdouble 9223372036854775808%Z.
Definition f32_inf : fp_carrier Ffloat := fp_of_bits Ffloat 2139095040%Z.
Definition f64_inf : fp_carrier Fdouble := fp_of_bits Fdouble 9218868437227405312%Z.
Definition f32_nan : fp_carrier Ffloat := fp_default_nan Ffloat.
Definition f64_nan : fp_carrier Fdouble := fp_default_nan Fdouble.
Definition f32_nan_payload : fp_carrier Ffloat := fp_of_bits Ffloat 2143289345%Z.
Definition f64_nan_payload : fp_carrier Fdouble := fp_of_bits Fdouble 9221120237041090561%Z.

Definition little_float_test_genv : genv :=
  {| genv_tu := empty_tu (abi.mkT int_rank.Ilong Signed Signed Little) |}.
Definition big_float_test_genv : genv :=
  {| genv_tu := empty_tu (abi.mkT int_rank.Ilong Signed Signed Big) |}.

Example has_type_prop_float_value {σ : genv} :
  has_type_prop (Vfloat_ Ffloat f32_one) Tfloat.
Proof. apply has_float_type. reflexivity. Qed.

Example has_type_prop_double_value {σ : genv} :
  has_type_prop (Vfloat_ Fdouble f64_one) Tdouble.
Proof. apply has_float_type. reflexivity. Qed.

Example has_type_prop_rejects_mismatched_float_index {σ : genv} :
  ~ has_type_prop (Vfloat_ Ffloat f32_one) Tdouble.
Proof.
  intros Hty.
  apply (has_type_prop_float_inv Fdouble) in Hty; last reflexivity.
  destruct Hty as [f Hf]. discriminate Hf.
Qed.

Example fp32_to_of_bits_roundtrip bits :
  (0 <= bits < 2 ^ 32)%Z -> fp_to_bits Ffloat (fp_of_bits Ffloat bits) = bits.
Proof. intros Hbits. apply fp_to_of_bits; [reflexivity|exact Hbits]. Qed.

Example fp64_to_of_bits_roundtrip bits :
  (0 <= bits < 2 ^ 64)%Z -> fp_to_bits Fdouble (fp_of_bits Fdouble bits) = bits.
Proof. intros Hbits. apply fp_to_of_bits; [reflexivity|exact Hbits]. Qed.

Example fp32_of_to_bits_roundtrip f : fp_of_bits Ffloat (fp_to_bits Ffloat f) = f.
Proof. apply fp_of_to_bits. Qed.

Example fp64_of_to_bits_roundtrip f : fp_of_bits Fdouble (fp_to_bits Fdouble f) = f.
Proof. apply fp_of_to_bits. Qed.

Example default_float_zero : get_default Tfloat = Some (Vfloat_ Ffloat (fp_zero Ffloat)).
Proof. reflexivity. Qed.

Example default_double_zero : get_default Tdouble = Some (Vfloat_ Fdouble (fp_zero Fdouble)).
Proof. reflexivity. Qed.

Example default_longdouble_unsupported : get_default Tlongdouble = None.
Proof. reflexivity. Qed.

Example float_bool_plus_zero_false : is_true (Vfloat_ Ffloat (fp_zero Ffloat)) = Some false.
Proof. simpl. rewrite fp_is_true_zero_Ffloat. reflexivity. Qed.

Example double_bool_plus_zero_false : is_true (Vfloat_ Fdouble (fp_zero Fdouble)) = Some false.
Proof. simpl. rewrite fp_is_true_zero_Fdouble. reflexivity. Qed.

Example float_bool_minus_zero_false : is_true (Vfloat_ Ffloat f32_neg_zero) = Some false.
Proof. vm_compute. reflexivity. Qed.

Example double_bool_minus_zero_false : is_true (Vfloat_ Fdouble f64_neg_zero) = Some false.
Proof. vm_compute. reflexivity. Qed.

Example float_bool_nonzero_true : is_true (Vfloat_ Ffloat f32_one) = Some true.
Proof. vm_compute. reflexivity. Qed.

Example double_bool_nonzero_true : is_true (Vfloat_ Fdouble f64_one) = Some true.
Proof. vm_compute. reflexivity. Qed.

Example float_bool_inf_true : is_true (Vfloat_ Ffloat f32_inf) = Some true.
Proof. vm_compute. reflexivity. Qed.

Example double_bool_inf_true : is_true (Vfloat_ Fdouble f64_inf) = Some true.
Proof. vm_compute. reflexivity. Qed.

Example float_bool_nan_true : is_true (Vfloat_ Ffloat f32_nan) = Some true.
Proof. vm_compute. reflexivity. Qed.

Example double_bool_nan_true : is_true (Vfloat_ Fdouble f64_nan) = Some true.
Proof. vm_compute. reflexivity. Qed.

Example float_nan_compare_unordered : fp_compare Ffloat f32_nan f32_nan = None.
Proof. vm_compute. reflexivity. Qed.

Example double_nan_compare_unordered : fp_compare Fdouble f64_nan f64_nan = None.
Proof. vm_compute. reflexivity. Qed.

Example default_nan_bits_float :
  fp_to_bits Ffloat (fp_default_nan Ffloat) = 2143289344%Z.
Proof. apply fp_to_bits_default_nan_Ffloat. Qed.

Example default_nan_bits_double :
  fp_to_bits Fdouble (fp_default_nan Fdouble) = 9221120237041090560%Z.
Proof. apply fp_to_bits_default_nan_Fdouble. Qed.

Example fp32_nan_payload_bits_preserved :
  fp_to_bits Ffloat (fp_of_bits Ffloat 2143289345%Z) = 2143289345%Z.
Proof. apply fp_to_of_bits_Ffloat. change (0 <= 2143289345 < 4294967296)%Z. lia. Qed.

Example fp64_nan_payload_bits_preserved :
  fp_to_bits Fdouble (fp_of_bits Fdouble 9221120237041090561%Z) = 9221120237041090561%Z.
Proof. apply fp_to_of_bits_Fdouble. change (0 <= 9221120237041090561 < 18446744073709551616)%Z. lia. Qed.

Example float_nan_add_canonical_bits :
  fp_to_bits Ffloat (fp_add Ffloat f32_nan f32_one) = 2143289344%Z.
Proof. vm_compute. reflexivity. Qed.

Example double_nan_add_canonical_bits :
  fp_to_bits Fdouble (fp_add Fdouble f64_nan f64_one) = 9221120237041090560%Z.
Proof. vm_compute. reflexivity. Qed.

Example float_nan_neg_canonical_bits :
  fp_to_bits Ffloat (fp_neg Ffloat f32_nan) = 2143289344%Z.
Proof. vm_compute. reflexivity. Qed.

Example double_nan_neg_canonical_bits :
  fp_to_bits Fdouble (fp_neg Fdouble f64_nan) = 9221120237041090560%Z.
Proof. vm_compute. reflexivity. Qed.

Example float_nan_eq_false :
  (if fp_compare Ffloat f32_nan f32_nan is Some Eq then true else false) = false.
Proof. vm_compute. reflexivity. Qed.

Example float_nan_neq_true :
  (if fp_compare Ffloat f32_nan f32_nan is Some Eq then false else true) = true.
Proof. vm_compute. reflexivity. Qed.

Example float_nan_ordered_lt_false :
  (if fp_compare Ffloat f32_nan f32_nan is Some Lt then true else false) = false.
Proof. vm_compute. reflexivity. Qed.

Example double_nan_eq_false :
  (if fp_compare Fdouble f64_nan f64_nan is Some Eq then true else false) = false.
Proof. vm_compute. reflexivity. Qed.

Example double_nan_neq_true :
  (if fp_compare Fdouble f64_nan f64_nan is Some Eq then false else true) = true.
Proof. vm_compute. reflexivity. Qed.

Example double_nan_ordered_lt_false :
  (if fp_compare Fdouble f64_nan f64_nan is Some Lt then true else false) = false.
Proof. vm_compute. reflexivity. Qed.

Example conv_float_identity_example {σ : genv} tu :
  conv_float tu Tfloat Tfloat (Vfloat_ Ffloat f32_one) (Vfloat_ Ffloat f32_one).
Proof. apply conv_float_id. reflexivity. Qed.

Example conv_float_to_bool_example {σ : genv} tu :
  conv_float tu Tfloat Tbool (Vfloat_ Ffloat f32_one) (Vbool true).
Proof. change true with (fp_is_true Ffloat f32_one). apply conv_float_to_bool. reflexivity. Qed.

Example conv_float_widen_example {σ : genv} tu :
  conv_float tu Tfloat Tdouble (Vfloat_ Ffloat f32_one)
    (Vfloat_ Fdouble (fp_float_to_double f32_one)).
Proof. apply conv_float_widen. Qed.

Example conv_float_narrow_example {σ : genv} tu :
  conv_float tu Tdouble Tfloat (Vfloat_ Fdouble f64_one)
    (Vfloat_ Ffloat (fp_double_to_float f64_one)).
Proof. apply conv_float_narrow. Qed.

Example conv_float_int_to_float_example {σ : genv} tu :
  conv_float tu Tint Tfloat (Vint 1) (Vfloat_ Ffloat (fp_of_Z Ffloat 1)).
Proof.
  eapply ConvFloatIntToFloat; [reflexivity|reflexivity|].
  rewrite -has_int_type /bitsize.bound /bitsize.min_val /bitsize.max_val /=; lia.
Qed.

Example conv_float_float_to_int_example {σ : genv} tu :
  conv_float tu Tfloat Tint (Vfloat_ Ffloat f32_one) (Vint 1).
Proof.
  eapply ConvFloatToInt; [reflexivity|reflexivity|vm_compute; reflexivity|].
  rewrite -has_int_type /bitsize.bound /bitsize.min_val /bitsize.max_val /=; lia.
Qed.

Example eval_add_mixed_float_double_after_conversion {σ : genv} tu :
  eval_binop_pure tu Badd Tdouble Tdouble Tdouble
    (Vfloat_ Fdouble (fp_float_to_double f32_one))
    (Vfloat_ Fdouble f64_one)
    (Vfloat_ Fdouble (fp_add Fdouble (fp_float_to_double f32_one) f64_one)).
Proof. apply eval_add_float. reflexivity. Qed.

Example eval_cmp_mixed_float_double_after_conversion {σ : genv} tu :
  eval_binop_pure tu Blt Tdouble Tdouble Tbool
    (Vfloat_ Fdouble (fp_float_to_double f32_one))
    (Vfloat_ Fdouble f64_one)
    (Vbool (fp_cmp_result (fp_compare Fdouble (fp_float_to_double f32_one) f64_one) Blt)).
Proof. apply eval_cmp_float; [tauto|reflexivity]. Qed.

Example raw_bytes_float32_intro {σ : genv} :
  raw_bytes_of_val σ Tfloat (Vfloat_ Ffloat f32_one) (fp_raw_bytes σ Ffloat f32_one).
Proof. apply raw_bytes_of_val_float_intro. reflexivity. Qed.

Example raw_bytes_float64_intro {σ : genv} :
  raw_bytes_of_val σ Tdouble (Vfloat_ Fdouble f64_one) (fp_raw_bytes σ Fdouble f64_one).
Proof. apply raw_bytes_of_val_float_intro. reflexivity. Qed.

Example raw_bytes_float32_length {σ : genv} :
  length (fp_raw_bytes σ Ffloat f32_one) = 4%nat.
Proof. rewrite fp_raw_bytes_length. reflexivity. Qed.

Example raw_bytes_float64_length {σ : genv} :
  length (fp_raw_bytes σ Fdouble f64_one) = 8%nat.
Proof. rewrite fp_raw_bytes_length. reflexivity. Qed.

Example raw_bytes_float32_one_little_endian :
  fp_raw_bytes little_float_test_genv Ffloat f32_one =
  raw_int_byte <$> [0%N; 0%N; 128%N; 63%N].
Proof.
  rewrite /fp_raw_bytes z_to_bytes._Z_to_bytes_eq /z_to_bytes._Z_to_bytes_def /z_to_bytes._Z_to_bytes_le
    /z_to_bytes._Z_to_bytes_unsigned_le /z_to_bytes._Z_to_bytes_unsigned_le' /=.
  reflexivity.
Qed.

Example raw_bytes_float32_one_big_endian :
  fp_raw_bytes big_float_test_genv Ffloat f32_one =
  raw_int_byte <$> [63%N; 128%N; 0%N; 0%N].
Proof.
  rewrite /fp_raw_bytes z_to_bytes._Z_to_bytes_eq /z_to_bytes._Z_to_bytes_def /z_to_bytes._Z_to_bytes_le
    /z_to_bytes._Z_to_bytes_unsigned_le /z_to_bytes._Z_to_bytes_unsigned_le' /=.
  reflexivity.
Qed.

Example raw_bytes_float64_one_little_endian :
  fp_raw_bytes little_float_test_genv Fdouble f64_one =
  raw_int_byte <$> [0%N; 0%N; 0%N; 0%N; 0%N; 0%N; 240%N; 63%N].
Proof.
  rewrite /fp_raw_bytes z_to_bytes._Z_to_bytes_eq /z_to_bytes._Z_to_bytes_def /z_to_bytes._Z_to_bytes_le
    /z_to_bytes._Z_to_bytes_unsigned_le /z_to_bytes._Z_to_bytes_unsigned_le' /=.
  reflexivity.
Qed.

Example raw_bytes_float64_one_big_endian :
  fp_raw_bytes big_float_test_genv Fdouble f64_one =
  raw_int_byte <$> [63%N; 240%N; 0%N; 0%N; 0%N; 0%N; 0%N; 0%N].
Proof.
  rewrite /fp_raw_bytes z_to_bytes._Z_to_bytes_eq /z_to_bytes._Z_to_bytes_def /z_to_bytes._Z_to_bytes_le
    /z_to_bytes._Z_to_bytes_unsigned_le /z_to_bytes._Z_to_bytes_unsigned_le' /=.
  reflexivity.
Qed.

Example raw_bytes_float32_same_bytes_same_value {σ : genv} rs f :
  raw_bytes_of_val σ Tfloat (Vfloat_ Ffloat f32_one) rs ->
  raw_bytes_of_val σ Tfloat (Vfloat_ Ffloat f) rs ->
  f = f32_one.
Proof.
  intros H1 H2.
  symmetry. eapply raw_bytes_of_val_float_unique_val; [reflexivity|exact H1|exact H2].
Qed.

Example raw_bytes_float64_same_bytes_same_value {σ : genv} rs f :
  raw_bytes_of_val σ Tdouble (Vfloat_ Fdouble f64_one) rs ->
  raw_bytes_of_val σ Tdouble (Vfloat_ Fdouble f) rs ->
  f = f64_one.
Proof.
  intros H1 H2.
  symmetry. eapply raw_bytes_of_val_float_unique_val; [reflexivity|exact H1|exact H2].
Qed.

Example raw_bytes_float32_nan_payload_survives_roundtrip {σ : genv} rs f :
  raw_bytes_of_val σ Tfloat (Vfloat_ Ffloat f32_nan_payload) rs ->
  raw_bytes_of_val σ Tfloat (Vfloat_ Ffloat f) rs ->
  fp_to_bits Ffloat f = 2143289345%Z.
Proof.
  intros H1 H2.
  assert (f = f32_nan_payload) as ->.
  { symmetry. eapply raw_bytes_of_val_float_unique_val; [reflexivity|exact H1|exact H2]. }
  apply fp_to_of_bits_Ffloat. change (0 <= 2143289345 < 4294967296)%Z. lia.
Qed.

Example raw_bytes_float64_nan_payload_survives_roundtrip {σ : genv} rs f :
  raw_bytes_of_val σ Tdouble (Vfloat_ Fdouble f64_nan_payload) rs ->
  raw_bytes_of_val σ Tdouble (Vfloat_ Fdouble f) rs ->
  fp_to_bits Fdouble f = 9221120237041090561%Z.
Proof.
  intros H1 H2.
  assert (f = f64_nan_payload) as ->.
  { symmetry. eapply raw_bytes_of_val_float_unique_val; [reflexivity|exact H1|exact H2]. }
  apply fp_to_of_bits_Fdouble. change (0 <= 9221120237041090561 < 18446744073709551616)%Z. lia.
Qed.

Section raw_byte_reinterpretation_tests.
  Context `{Σ : cpp_logic} {σ : genv}.

  Example raw_bytes_float32_to_unsigned_bits :
    raw_bytes_of_val σ Tuint (Vint (fp_to_bits Ffloat f32_one)) (fp_raw_bytes σ Ffloat f32_one).
  Proof.
    apply Endian.raw_bytes_of_val_float_to_unsigned_bits; reflexivity.
  Qed.

  Example raw_bytes_float64_to_unsigned_bits :
    raw_bytes_of_val σ Tulonglong (Vint (fp_to_bits Fdouble f64_one)) (fp_raw_bytes σ Fdouble f64_one).
  Proof.
    apply Endian.raw_bytes_of_val_float_to_unsigned_bits; reflexivity.
  Qed.

  Example raw_bytes_unsigned_bits_to_float32 rs :
    raw_bytes_of_val σ Tuint (Vint (fp_to_bits Ffloat f32_one)) rs ->
    raw_bytes_of_val σ Tfloat (Vfloat_ Ffloat f32_one) rs.
  Proof.
    intros Hraw.
    rewrite -(fp_of_to_bits Ffloat f32_one).
    eapply (@raw_bytes_of_val_unsigned_bits_to_float σ int_rank.Iint Ffloat (fp_to_bits Ffloat f32_one) rs);
      [reflexivity|reflexivity|exact Hraw].
  Qed.

  Example raw_bytes_unsigned_bits_to_float64 rs :
    raw_bytes_of_val σ Tulonglong (Vint (fp_to_bits Fdouble f64_one)) rs ->
    raw_bytes_of_val σ Tdouble (Vfloat_ Fdouble f64_one) rs.
  Proof.
    intros Hraw.
    rewrite -(fp_of_to_bits Fdouble f64_one).
    eapply (@raw_bytes_of_val_unsigned_bits_to_float σ int_rank.Ilonglong Fdouble (fp_to_bits Fdouble f64_one) rs);
      [reflexivity|reflexivity|exact Hraw].
  Qed.

  Example raw_bytes_unsigned_nan_payload_to_float32 rs :
    raw_bytes_of_val σ Tuint (Vint 2143289345%Z) rs ->
    raw_bytes_of_val σ Tfloat (Vfloat_ Ffloat f32_nan_payload) rs.
  Proof.
    intros Hraw.
    change (Vfloat_ Ffloat f32_nan_payload) with (Vfloat_ Ffloat (fp_of_bits Ffloat 2143289345%Z)).
    eapply (@raw_bytes_of_val_unsigned_bits_to_float σ int_rank.Iint Ffloat 2143289345%Z rs);
      [reflexivity|reflexivity|exact Hraw].
  Qed.

  Example raw_bytes_unsigned_nan_payload_to_float64 rs :
    raw_bytes_of_val σ Tulonglong (Vint 9221120237041090561%Z) rs ->
    raw_bytes_of_val σ Tdouble (Vfloat_ Fdouble f64_nan_payload) rs.
  Proof.
    intros Hraw.
    change (Vfloat_ Fdouble f64_nan_payload) with (Vfloat_ Fdouble (fp_of_bits Fdouble 9221120237041090561%Z)).
    eapply (@raw_bytes_of_val_unsigned_bits_to_float σ int_rank.Ilonglong Fdouble 9221120237041090561%Z rs);
      [reflexivity|reflexivity|exact Hraw].
  Qed.
End raw_byte_reinterpretation_tests.
