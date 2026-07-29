Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.prog.cpp.plugin.

#[with_templates]
cpp.prog source prog cpp:{{
template<class T>
struct Holder {
  typedef T value_type;
  value_type value;
};

Holder<int> make_holder() {
  return Holder<int>{1};
}
}}.

Definition is_Some {T} (a : option T) : Prop :=
  match a with
  | Some _ => True
  | None => False
  end.

Example holder_template_exists :
  is_Some (translation_unit.mtypes source !! "Holder<$T>"%cpp_name).
Proof. vm_compute. exact I. Qed.

Example value_type_template_exists :
  is_Some (translation_unit.maliases source !! "Holder<$T>::value_type"%cpp_name).
Proof. vm_compute. exact I. Qed.

Example make_holder_exists :
  is_Some (source.(symbols) !! "make_holder()"%cpp_name).
Proof. vm_compute. exact I. Qed.
