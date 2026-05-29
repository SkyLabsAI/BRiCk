Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.syntax.supported.
Require Import skylabs.lang.cpp.syntax.typing.

Require test.test_cpp.

Definition return_expr (nm : ident) : option Expr :=
  match test_cpp.module.(symbols) !! Nglobal (Nfunction function_qualifiers.N nm []) with
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

Eval vm_compute in supported.check.translation_unit test_cpp.module.

Example decimal_float_typed :
  check_return "decimal_float" float_type.Ffloat = true :=
  ltac:(vm_compute; reflexivity).

Example negative_zero_float_typed :
  check_return "negative_zero_float" float_type.Ffloat = true :=
  ltac:(vm_compute; reflexivity).

Example decimal_double_typed :
  check_return "decimal_double" float_type.Fdouble = true :=
  ltac:(vm_compute; reflexivity).

Example hex_double_typed :
  check_return "hex_double" float_type.Fdouble = true :=
  ltac:(vm_compute; reflexivity).

Example scientific_double_typed :
  check_return "scientific_double" float_type.Fdouble = true :=
  ltac:(vm_compute; reflexivity).
