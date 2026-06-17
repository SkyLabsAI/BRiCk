Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.msyntax.

Require Import test_combined (source).

Definition is_Some {T} (a : option T) : Prop :=
  match a with
  | Some _ => True
  | None => False
  end.

Example twice_int_exists :
  is_Some (source.(symbols) !! "twice<int>(int)"%cpp_name).
Proof. vm_compute. exact I. Qed.

Example use_twice_exists :
  is_Some (source.(symbols) !! "use_twice()"%cpp_name).
Proof. vm_compute. exact I. Qed.

Example twice_template_exists :
  is_Some (translation_unit.msymbols source !! "twice<$T>($T)"%cpp_name).
Proof. vm_compute. exact I. Qed.
