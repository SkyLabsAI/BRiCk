Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.syntax.

Require test.cases_cpp.

Definition type_is_gstruct (n : name) : bool :=
  match test.cases_cpp.module.(types) !! n with
  | Some (Gstruct _) => true
  | _ => false
  end.

Definition type_is_gtype (n : name) : bool :=
  match test.cases_cpp.module.(types) !! n with
  | Some Gtype => true
  | _ => false
  end.

Definition type_is_typedef_to (n target : name) : bool :=
  match test.cases_cpp.module.(types) !! n with
  | Some (Gtypedef (Tnamed target')) => bool_decide (target' = target)
  | _ => false
  end.

Example typedef_before_record :
  type_is_gstruct "Before" = true :=
  ltac:(vm_compute; reflexivity).

Example typedef_after_record :
  type_is_gstruct "After" = true :=
  ltac:(vm_compute; reflexivity).

Example typedef_inline_record :
  type_is_gstruct "Inline" = true :=
  ltac:(vm_compute; reflexivity).

Example typedef_forward_only :
  type_is_gtype "ForwardOnly" = true :=
  ltac:(vm_compute; reflexivity).

Example regular_typedef_keeps_tag :
  type_is_gtype "D" = true :=
  ltac:(vm_compute; reflexivity).

Example regular_typedef_keeps_alias :
  type_is_typedef_to "Dtypedef" "D" = true :=
  ltac:(vm_compute; reflexivity).

Example regular_typedef_keeps_alias_only :
  type_is_typedef_to "Xtypedef" "X" = true :=
  ltac:(vm_compute; reflexivity).

Example regular_typedef_keeps_tag_only :
  type_is_gtype "X" = true :=
  ltac:(vm_compute; reflexivity).
