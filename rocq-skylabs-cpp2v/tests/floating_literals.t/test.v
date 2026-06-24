Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.syntax.supported.
Require Import skylabs.lang.cpp.syntax.typing.

Require test.test_cpp.

Definition return_expr (nm : ident) : option Expr :=
  match test_cpp.source.(symbols) !! Nglobal (Nfunction function_qualifiers.N nm []) with
  | Some (Ofunction f) =>
      match f.(f_body) with
      | Some (Impl (Sseq [Sreturn (Some e)])) => Some e
      | _ => None
      end
  | _ => None
  end.

Definition check_return (nm : ident) (ft : float_type.t) : bool :=
  match return_expr nm with
  | Some e =>
      bool_decide (supported.check.expr e = []) &&
      bool_decide (decltype.of_expr e = Some (Tfloat_ ft))
  | None => false
  end.

Definition check_return_bits (nm : ident) (ft : float_type.t) (bits : Z) : bool :=
  match return_expr nm with
  | Some (Efloat ft' f) =>
      bool_decide (ft = ft') && bool_decide (float_value.to_bits ft' f = bits)
  | _ => false
  end.

Eval vm_compute in supported.check.translation_unit test_cpp.source.

Example decimal_float16_typed :
  check_return "decimal_float16" float_type.Ffloat16 = true :=
  ltac:(vm_compute; reflexivity).

Example decimal_float16_bits :
  check_return_bits "decimal_float16" float_type.Ffloat16 15360 = true :=
  ltac:(vm_compute; reflexivity).

Example decimal_float_typed :
  check_return "decimal_float" float_type.Ffloat = true :=
  ltac:(vm_compute; reflexivity).

Example decimal_float_bits :
  check_return_bits "decimal_float" float_type.Ffloat 1065353216 = true :=
  ltac:(vm_compute; reflexivity).

Example negative_zero_float_typed :
  check_return "negative_zero_float" float_type.Ffloat = true :=
  ltac:(vm_compute; reflexivity).

Example decimal_double_typed :
  check_return "decimal_double" float_type.Fdouble = true :=
  ltac:(vm_compute; reflexivity).

Example decimal_double_bits :
  check_return_bits "decimal_double" float_type.Fdouble 4612811918334230528 = true :=
  ltac:(vm_compute; reflexivity).

Example hex_double_typed :
  check_return "hex_double" float_type.Fdouble = true :=
  ltac:(vm_compute; reflexivity).

Example scientific_double_typed :
  check_return "scientific_double" float_type.Fdouble = true :=
  ltac:(vm_compute; reflexivity).

Example decimal_float128_typed :
  check_return "decimal_float128" float_type.Ffloat128 = true :=
  ltac:(vm_compute; reflexivity).

Example decimal_float128_bits :
  check_return_bits "decimal_float128" float_type.Ffloat128
    85065399433376081038215121361612832768 = true :=
  ltac:(vm_compute; reflexivity).
