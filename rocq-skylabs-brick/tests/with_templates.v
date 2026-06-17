Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.parser.plugin.cpp2v.

#[with_templates]
cpp.prog templated prog cpp:{{
template <typename T> T id(T x) { return x; }
int use() { return id<int>(3); }
}}.

Definition is_Some {T} (a : option T) : Prop :=
  match a with
  | Some _ => True
  | None => False
  end.

Example has_template_symbols :
  List.length (TM.elements templated.(translation_unit.msymbols)) = 1 := eq_refl.

Example id_int_exists :
  is_Some (templated.(symbols) !! "id<int>(int)"%cpp_name).
Proof. vm_compute. exact I. Qed.

Example use_exists :
  is_Some (templated.(symbols) !! "use()"%cpp_name).
Proof. vm_compute. exact I. Qed.

Example id_template_exists :
  is_Some (translation_unit.msymbols templated !! "id<$T>($T)"%cpp_name).
Proof. vm_compute. exact I. Qed.
