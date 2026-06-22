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

Definition f16_one_bits : Z := 15360%Z.
Definition f16_neg_zero_bits : Z := 32768%Z.
Definition f16_inf_bits : Z := 31744%Z.
Definition f16_nan_payload_bits : Z := 32257%Z.

Definition f32_one_bits : Z := 1065353216%Z.
Definition f32_neg_zero_bits : Z := 2147483648%Z.
Definition f32_inf_bits : Z := 2139095040%Z.
Definition f32_nan_payload_bits : Z := 2143289345%Z.

Definition f64_one_bits : Z := 4607182418800017408%Z.
Definition f64_neg_zero_bits : Z := 9223372036854775808%Z.
Definition f64_inf_bits : Z := 9218868437227405312%Z.
Definition f64_nan_payload_bits : Z := 9221120237041090561%Z.

Definition f128_one_bits : Z :=
  85065399433376081038215121361612832768%Z.
Definition f128_neg_zero_bits : Z :=
  170141183460469231731687303715884105728%Z.
Definition f128_inf_bits : Z :=
  170135991163610696904058773219554885632%Z.
Definition f128_nan_payload_bits : Z :=
  170138587312039964317873038467719495681%Z.

Definition f16_one : float_type.car float_type.Ffloat16 :=
  float_value.of_bits float_type.Ffloat16 f16_one_bits.
Definition f32_one : float_type.car float_type.Ffloat :=
  float_value.of_bits float_type.Ffloat f32_one_bits.
Definition f64_one : float_type.car float_type.Fdouble :=
  float_value.of_bits float_type.Fdouble f64_one_bits.
Definition f128_one : float_type.car float_type.Ffloat128 :=
  float_value.of_bits float_type.Ffloat128 f128_one_bits.

Definition f16_neg_zero : float_type.car float_type.Ffloat16 :=
  float_value.of_bits float_type.Ffloat16 f16_neg_zero_bits.
Definition f32_neg_zero : float_type.car float_type.Ffloat :=
  float_value.of_bits float_type.Ffloat f32_neg_zero_bits.
Definition f64_neg_zero : float_type.car float_type.Fdouble :=
  float_value.of_bits float_type.Fdouble f64_neg_zero_bits.
Definition f128_neg_zero : float_type.car float_type.Ffloat128 :=
  float_value.of_bits float_type.Ffloat128 f128_neg_zero_bits.

Definition f16_inf : float_type.car float_type.Ffloat16 :=
  float_value.of_bits float_type.Ffloat16 f16_inf_bits.
Definition f32_inf : float_type.car float_type.Ffloat :=
  float_value.of_bits float_type.Ffloat f32_inf_bits.
Definition f64_inf : float_type.car float_type.Fdouble :=
  float_value.of_bits float_type.Fdouble f64_inf_bits.
Definition f128_inf : float_type.car float_type.Ffloat128 :=
  float_value.of_bits float_type.Ffloat128 f128_inf_bits.

Definition f16_nan : float_type.car float_type.Ffloat16 :=
  proj1_sig (float_value.default_nan float_type.Ffloat16).
Definition f32_nan : float_type.car float_type.Ffloat :=
  proj1_sig (float_value.default_nan float_type.Ffloat).
Definition f64_nan : float_type.car float_type.Fdouble :=
  proj1_sig (float_value.default_nan float_type.Fdouble).
Definition f128_nan : float_type.car float_type.Ffloat128 :=
  proj1_sig (float_value.default_nan float_type.Ffloat128).

Definition f16_nan_payload : float_type.car float_type.Ffloat16 :=
  float_value.of_bits float_type.Ffloat16 f16_nan_payload_bits.
Definition f32_nan_payload : float_type.car float_type.Ffloat :=
  float_value.of_bits float_type.Ffloat f32_nan_payload_bits.
Definition f64_nan_payload : float_type.car float_type.Fdouble :=
  float_value.of_bits float_type.Fdouble f64_nan_payload_bits.
Definition f128_nan_payload : float_type.car float_type.Ffloat128 :=
  float_value.of_bits float_type.Ffloat128 f128_nan_payload_bits.

Definition one_float16 : Expr := Efloat float_type.Ffloat16 f16_one.
Definition one_float : Expr := Efloat float_type.Ffloat f32_one.
Definition one_double : Expr := Efloat float_type.Fdouble f64_one.
Definition one_float128 : Expr := Efloat float_type.Ffloat128 f128_one.

Example support_accepts_float16_type :
  check.type Tfloat16 = check.OK.
Proof. reflexivity. Qed.

Example support_accepts_float_type :
  check.type Tfloat = check.OK.
Proof. reflexivity. Qed.

Example support_accepts_double_type :
  check.type Tdouble = check.OK.
Proof. reflexivity. Qed.

Example support_accepts_float128_type :
  check.type Tfloat128 = check.OK.
Proof. reflexivity. Qed.

Example support_rejects_longdouble_type :
  check.type Tlongdouble = check.FAIL "unsupported floating width".
Proof. reflexivity. Qed.

Example support_accepts_float16_literal :
  check.expr one_float16 = check.OK.
Proof. reflexivity. Qed.

Example support_accepts_float_literal :
  check.expr one_float = check.OK.
Proof. reflexivity. Qed.

Example support_accepts_double_literal :
  check.expr one_double = check.OK.
Proof. reflexivity. Qed.

Example support_accepts_float128_literal :
  check.expr one_float128 = check.OK.
Proof. reflexivity. Qed.

Example support_rejects_longdouble_literal :
  check.expr (Efloat float_type.Flongdouble (float_value.zero float_type.Flongdouble)) =
    check.FAIL "unsupported floating width".
Proof. reflexivity. Qed.

Example support_accepts_float_to_double_cast :
  check.expr (Ecast (Cfloat Tdouble) one_float) = check.OK.
Proof. reflexivity. Qed.

Example support_accepts_double_to_float128_cast :
  check.expr (Ecast (Cfloat Tfloat128) one_double) = check.OK.
Proof. reflexivity. Qed.

Example support_accepts_int_to_float16_cast :
  check.expr (Ecast (Cint2float Tfloat16) (Eint 0 Tint)) = check.OK.
Proof. reflexivity. Qed.

Example support_accepts_float128_to_int_cast :
  check.expr (Ecast (Cfloat2int Tint) one_float128) = check.OK.
Proof. reflexivity. Qed.

Example support_accepts_float_to_bool_cast :
  check.expr (Ecast Cfloat2bool one_float) = check.OK.
Proof. reflexivity. Qed.

Definition small_enum_name : name := "Small".

Example support_accepts_char_to_float_cast :
  check.expr (Ecast (Cint2float Tfloat) (Echar 65 Tchar)) = check.OK.
Proof. reflexivity. Qed.

Example support_accepts_float_to_char_cast :
  check.expr (Ecast (Cfloat2int Tchar) one_float) = check.OK.
Proof. reflexivity. Qed.

Example support_accepts_enum_to_float_cast :
  check.expr (Ecast (Cint2float Tfloat) (Eenum_const small_enum_name "A")) = check.OK.
Proof. reflexivity. Qed.

Example support_accepts_float_to_enum_cast :
  check.expr (Ecast (Cfloat2int (Tenum small_enum_name)) one_float) = check.OK.
Proof. reflexivity. Qed.

Example support_accepts_float_unary_plus :
  check.expr (Eunop Uplus one_float Tfloat) = check.OK.
Proof. reflexivity. Qed.

Example support_accepts_float_unary_minus :
  check.expr (Eunop Uminus one_float Tfloat) = check.OK.
Proof. reflexivity. Qed.

Example support_accepts_float_logical_not :
  check.expr (Eunop Unot one_float Tbool) = check.OK.
Proof. reflexivity. Qed.

Example support_accepts_float_add :
  check.expr (Ebinop Badd one_float one_double Tdouble) = check.OK.
Proof. reflexivity. Qed.

Example support_accepts_float_sub :
  check.expr (Ebinop Bsub one_float one_float Tfloat) = check.OK.
Proof. reflexivity. Qed.

Example support_accepts_float_mul :
  check.expr (Ebinop Bmul one_float one_float Tfloat) = check.OK.
Proof. reflexivity. Qed.

Example support_accepts_float_div :
  check.expr (Ebinop Bdiv one_float one_float Tfloat) = check.OK.
Proof. reflexivity. Qed.

Example support_accepts_float_less_than :
  check.expr (Ebinop Blt one_float one_double Tbool) = check.OK.
Proof. reflexivity. Qed.

Example support_rejects_float_mod :
  check.expr (Ebinop Bmod one_float one_float Tfloat) <> check.OK.
Proof. vm_compute; discriminate. Qed.

Example support_rejects_float_bitand :
  check.expr (Ebinop Band one_float one_float Tfloat) <> check.OK.
Proof. vm_compute; discriminate. Qed.

Example support_rejects_float_shift_left :
  check.expr (Ebinop Bshl one_float (Eint 1 Tint) Tfloat) <> check.OK.
Proof. vm_compute; discriminate. Qed.

Example support_rejects_float_three_way_compare :
  check.expr (Ebinop Bcmp one_float one_float Tfloat) <> check.OK.
Proof. vm_compute; discriminate. Qed.

Example support_rejects_pointer_float_add :
  check.expr (Ebinop Badd (Evar "p" (Tptr Tint)) one_float (Tptr Tint)) <> check.OK.
Proof. vm_compute; discriminate. Qed.

Example support_rejects_float_preinc :
  check.expr (Epreinc (Evar "f" Tfloat) Tfloat) <> check.OK.
Proof. vm_compute; discriminate. Qed.

Example support_rejects_float_postdec :
  check.expr (Epostdec (Evar "f" Tfloat) Tfloat) <> check.OK.
Proof. vm_compute; discriminate. Qed.

Example convert_type_float_add_promotes_to_double tu :
  convert_type_op tu Badd Tfloat Tdouble = Some (Tdouble, Tdouble, Tdouble).
Proof. reflexivity. Qed.

Example convert_type_float_int_add_converts_int tu :
  convert_type_op tu Badd Tfloat Tint = Some (Tfloat, Tfloat, Tfloat).
Proof. reflexivity. Qed.

Example convert_type_int_double_ge_converts_int tu :
  convert_type_op tu Bge Tint Tdouble = Some (Tdouble, Tdouble, Tbool).
Proof. reflexivity. Qed.

Example convert_type_rejects_float_mod tu :
  convert_type_op tu Bmod Tfloat Tfloat = None.
Proof. reflexivity. Qed.

Example convert_type_rejects_pointer_float_add tu :
  convert_type_op tu Badd (Tptr Tint) Tfloat = None.
Proof. reflexivity. Qed.

Example convert_includes_conv_float_for_float_to_int {σ : genv} tu v v' :
  conv_float tu Tfloat Tint v v' -> @convert σ tu Tfloat Tint v v'.
Proof. intros Hconv. rewrite /convert /=. by right. Qed.

Example has_type_prop_float_value {σ : genv} :
  has_type_prop (Vfloat float_type.Ffloat f32_one) Tfloat.
Proof. apply has_float_type. Qed.

Example has_type_prop_rejects_mismatched_float {σ : genv} :
  ~ has_type_prop (Vfloat float_type.Ffloat f32_one) Tdouble.
Proof.
  intros Hty.
  rewrite has_type_prop_float in Hty.
  destruct Hty as [f Hf]. discriminate Hf.
Qed.

Example float_to_of_bits_roundtrips bits :
  (0 <= bits < 2 ^ float_type.bit_width float_type.Ffloat)%Z ->
  float_value.to_bits float_type.Ffloat
    (float_value.of_bits float_type.Ffloat bits) = bits.
Proof. apply float_value.to_of_bits. Qed.

Example double_of_to_bits_roundtrip f :
  float_value.of_bits float_type.Fdouble
    (float_value.to_bits float_type.Fdouble f) = f.
Proof. apply float_value.of_to_bits. Qed.

Example float128_nan_payload_bits_preserved :
  float_value.to_bits float_type.Ffloat128 f128_nan_payload = f128_nan_payload_bits.
Proof.
  apply float_value.to_of_bits.
  change (0 <= 170138587312039964317873038467719495681 <
          340282366920938463463374607431768211456)%Z.
  lia.
Qed.

Example default_float_zero :
  get_default Tfloat = Some (Vfloat float_type.Ffloat (float_value.zero float_type.Ffloat)).
Proof. reflexivity. Qed.

Example default_float128_zero :
  get_default Tfloat128 = Some (Vfloat float_type.Ffloat128 (float_value.zero float_type.Ffloat128)).
Proof. reflexivity. Qed.

Example float_zero_is_false :
  is_true (Vfloat float_type.Ffloat (float_value.zero float_type.Ffloat)) = Some false.
Proof. vm_compute; reflexivity. Qed.

Example float_negative_zero_is_false :
  is_true (Vfloat float_type.Ffloat f32_neg_zero) = Some false.
Proof. vm_compute; reflexivity. Qed.

Example float_one_is_true :
  is_true (Vfloat float_type.Ffloat f32_one) = Some true.
Proof. vm_compute; reflexivity. Qed.

Example float_infinity_is_true :
  is_true (Vfloat float_type.Ffloat f32_inf) = Some true.
Proof. vm_compute; reflexivity. Qed.

Example float_nan_is_true :
  is_true (Vfloat float_type.Ffloat f32_nan) = Some true.
Proof. vm_compute; reflexivity. Qed.

Example float16_negative_zero_is_false :
  is_true (Vfloat float_type.Ffloat16 f16_neg_zero) = Some false.
Proof. vm_compute; reflexivity. Qed.

Example float16_one_is_true :
  is_true (Vfloat float_type.Ffloat16 f16_one) = Some true.
Proof. vm_compute; reflexivity. Qed.

Example float128_negative_zero_is_false :
  is_true (Vfloat float_type.Ffloat128 f128_neg_zero) = Some false.
Proof. vm_compute; reflexivity. Qed.

Example float128_infinity_is_true :
  is_true (Vfloat float_type.Ffloat128 f128_inf) = Some true.
Proof. vm_compute; reflexivity. Qed.

Example float128_nan_is_true :
  is_true (Vfloat float_type.Ffloat128 f128_nan) = Some true.
Proof. vm_compute; reflexivity. Qed.

Example eval_not_float_zero {σ : genv} tu :
  eval_unop tu Unot Tfloat Tbool
    (Vfloat float_type.Ffloat (float_value.zero float_type.Ffloat))
    (Vbool true).
Proof.
  replace true with
    (negb (@float_value.is_true float_type.Ffloat (float_value.zero float_type.Ffloat))).
  - apply eval_not_float.
  - rewrite float_value.is_true_zero. reflexivity.
Qed.

Example eval_not_float_nan {σ : genv} tu :
  eval_unop tu Unot Tfloat Tbool
    (Vfloat float_type.Ffloat f32_nan)
    (Vbool false).
Proof.
  replace false with (negb (@float_value.is_true float_type.Ffloat f32_nan)).
  - apply eval_not_float.
  - vm_compute; reflexivity.
Qed.

Example float_nan_compare_unordered :
  float_value.value_compare float_type.Ffloat f32_nan f32_nan = None.
Proof. vm_compute; reflexivity. Qed.

Example double_nan_compare_unordered :
  float_value.value_compare float_type.Fdouble f64_nan f64_nan = None.
Proof. vm_compute; reflexivity. Qed.

Example float_nan_payload_add_preserved :
  float_value.to_bits float_type.Ffloat
    (float_value.add float_type.Ffloat f32_nan_payload f32_one) =
  f32_nan_payload_bits.
Proof. vm_compute; reflexivity. Qed.

Definition little_float_test_genv : genv :=
  {| genv_tu := empty_tu (abi.mkT int_rank.Ilong Signed Signed Little lang_version.Cpp20) |}.

Example char32_to_float_uses_full_unsigned_range :
  char_to_Z_for_float little_float_test_genv char_type.C32 65535 = 65535%Z.
Proof. rewrite /char_to_Z_for_float of_char.unlock. reflexivity. Qed.

Example float_to_char_accepts_representable_char :
  float_to_char little_float_test_genv float_type.Ffloat char_type.C8
    (float_value.of_int float_type.Ffloat 65) = Some 65%N.
Proof. vm_compute; reflexivity. Qed.

Example raw_float16_intro {σ : genv} :
  raw_bytes_of_val σ Tfloat16 (Vfloat float_type.Ffloat16 f16_one)
    (float_raw_bytes σ float_type.Ffloat16 f16_one).
Proof. apply raw_bytes_of_val_float_intro. Qed.

Example raw_float_intro {σ : genv} :
  raw_bytes_of_val σ Tfloat (Vfloat float_type.Ffloat f32_one)
    (float_raw_bytes σ float_type.Ffloat f32_one).
Proof. apply raw_bytes_of_val_float_intro. Qed.

Example raw_double_intro {σ : genv} :
  raw_bytes_of_val σ Tdouble (Vfloat float_type.Fdouble f64_one)
    (float_raw_bytes σ float_type.Fdouble f64_one).
Proof. apply raw_bytes_of_val_float_intro. Qed.

Example raw_float128_intro {σ : genv} :
  raw_bytes_of_val σ Tfloat128 (Vfloat float_type.Ffloat128 f128_one)
    (float_raw_bytes σ float_type.Ffloat128 f128_one).
Proof. apply raw_bytes_of_val_float_intro. Qed.

Example float16_bits_compatible :
  float_bits_compatible int_rank.Ishort float_type.Ffloat16.
Proof. split; reflexivity. Qed.

Example float32_bits_compatible :
  float_bits_compatible int_rank.Iint float_type.Ffloat.
Proof. split; reflexivity. Qed.

Example double_bits_compatible :
  float_bits_compatible int_rank.Ilong float_type.Fdouble.
Proof. split; reflexivity. Qed.

Example float128_bits_compatible :
  float_bits_compatible int_rank.I128 float_type.Ffloat128.
Proof. split; reflexivity. Qed.

Example longdouble_raw_bits_not_binary128_compatible :
  ~ float_bits_compatible int_rank.I128 float_type.Flongdouble.
Proof. intros [_ Hwidth]. vm_compute in Hwidth. discriminate. Qed.

Example float_to_bits_has_unsigned_type {σ : genv} :
  has_type_prop (Vint (float_value.to_bits float_type.Ffloat f32_one))
    (Tnum int_rank.Iint Unsigned).
Proof.
  apply float_to_bits_has_type_unsigned.
  split; reflexivity.
Qed.
