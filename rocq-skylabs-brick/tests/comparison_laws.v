Require Import skylabs.prelude.compare.
Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.syntax.compare.

Example operator_array_flag_distinct :
  atomic_name.compare compareT
    (Nop function_qualifiers.N (OONew false) [])
    (Nop function_qualifiers.N (OONew true) []) = Lt.
Proof. vm_compute. reflexivity. Qed.

Example overloaded_parameter_lists_distinct :
  atomic_name.compare compareT
    (Nfunction function_qualifiers.N "f" [("int"%cpp_type)])
    (Nfunction function_qualifiers.N "f" [("bool"%cpp_type)]) <> Eq.
Proof. vm_compute. discriminate. Qed.

Example function_qualifiers_distinct :
  atomic_name.compare compareT
    (Nfunction function_qualifiers.N "f" [])
    (Nfunction function_qualifiers.Nc "f" []) <> Eq.
Proof. vm_compute. discriminate. Qed.

Example first_name_tags_distinct :
  atomic_name.compare compareT (Nfirst_decl "x") (Nfirst_child "x") <> Eq.
Proof. vm_compute. discriminate. Qed.

Example nested_template_parameters_distinct :
  temp_param.compare compareT
    (Ptemplate "T" [Ptemplate "U" [Pvalue "n" ("int"%cpp_type)]])
    (Ptemplate "T" [Ptemplate "U" [Pvalue "n" ("bool"%cpp_type)]]) <> Eq.
Proof. vm_compute. discriminate. Qed.

Example template_parameter_kinds_distinct :
  temp_param.compare compareT (Ptype "T") (Pvalue "T" ("int"%cpp_type)) <> Eq.
Proof. vm_compute. discriminate. Qed.

Example template_parameter_list_prefix_distinct :
  temp_param.compare compareT
    (Ptemplate "T" [Ptype "X"])
    (Ptemplate "T" [Ptype "X"; Ptype "Y"]) <> Eq.
Proof. vm_compute. discriminate. Qed.

Set Printing Fully Qualified.

Definition coarse_type_compare (_ _ : type) : comparison := Eq.
#[local] Instance coarse_type_comparison : Comparison coarse_type_compare.
Proof. constructor; intros; unfold coarse_type_compare in *; cbn in *; congruence. Qed.

Lemma template_coarse_comparison : Comparison (temp_param.compare coarse_type_compare).
Proof. apply temp_param_comparison. Qed.

Example coarse_type_not_leibniz : ~ LeibnizComparison coarse_type_compare.
Proof.
  intros H.
  have bad := @LeibnizComparison.cmp_eq type coarse_type_compare H ("int"%cpp_type) ("bool"%cpp_type) eq_refl.
  discriminate bad.
Qed.

Example template_coarse_types_equal :
  temp_param.compare coarse_type_compare (Pvalue "n" ("int"%cpp_type)) (Pvalue "n" ("bool"%cpp_type)) = Eq.
Proof. vm_compute. reflexivity. Qed.
