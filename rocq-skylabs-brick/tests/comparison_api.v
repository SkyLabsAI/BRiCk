(*
 * Copyright (c) 2026 BlueRock Security, Inc.
 * See the LICENSE-BedRock file in the repository root for license details.
 *)
Require Import skylabs.prelude.compare.
Require Import skylabs.lang.cpp.syntax.

Example names_have_comparison_laws : Comparison (compare (A:=name)) := _.
Example types_have_comparison_laws : Comparison (compare (A:=type)) := _.
Example expressions_have_comparison_laws : Comparison (compare (A:=Expr)) := _.
Example template_params_have_comparison_laws :
  Comparison (compare (A:=temp_param)) := _.
Example template_args_have_leibniz_comparison :
  LeibnizComparison (compare (A:=temp_arg)) := _.
Example exception_specs_have_leibniz_comparison :
  LeibnizComparison (compare (A:=exception_spec.t)) := _.
Example function_qualifiers_have_comparison_laws :
  Comparison (compare (A:=function_qualifiers.t)) := _.

(** Kernel reduction must expose the result, without relying on the final
conversion check of [reflexivity]. Constructor automation uses this path. *)
Example names_reduce :
  bool_decide ("left"%cpp_name = "right"%cpp_name) = false.
Proof.
  rewrite /bool_decide /decide_rel. cbn.
  lazymatch goal with |- false = false => reflexivity end.
Qed.

Example nested_types_reduce :
  bool_decide (Tptr (Tptr "int"%cpp_type) = Tptr (Tptr "unsigned char"%cpp_type)) = false.
Proof.
  rewrite /bool_decide /decide_rel. cbn.
  lazymatch goal with |- false = false => reflexivity end.
Qed.

Example nested_types_compute :
  bool_decide (Tptr (Tptr "int"%cpp_type) = Tptr (Tptr "unsigned char"%cpp_type)) = false.
Proof. vm_compute. reflexivity. Qed.

Example nested_expressions_compute :
  bool_decide (Eimplicit (Eimplicit Enull) = Eimplicit Enull) = false.
Proof. vm_compute. reflexivity. Qed.

Example template_packs_compute :
  bool_decide (Apack [Apack [Atype "int"%cpp_type]] =
    Apack [Apack [Atype "unsigned char"%cpp_type]]) = false.
Proof. vm_compute. reflexivity. Qed.

Example names_compute :
  bool_decide ("left"%cpp_name = "right"%cpp_name) = false.
Proof. vm_compute. reflexivity. Qed.

Example exception_specs_compute :
  bool_decide (exception_spec.NoThrow = exception_spec.MayThrow) = false.
Proof. vm_compute. reflexivity. Qed.

Example literal_width_precedes_bytes :
  compare (literal_string.Build_t "z"%pstring 1%N)
    (literal_string.Build_t "a"%pstring 2%N) = Lt.
Proof. vm_compute. reflexivity. Qed.

Example literal_bytes_break_ties :
  compare (literal_string.Build_t "a"%pstring 1%N)
    (literal_string.Build_t "z"%pstring 1%N) = Lt.
Proof. vm_compute. reflexivity. Qed.
