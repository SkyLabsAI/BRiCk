Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.syntax.
Require test.test_cpp.

Goal is_Some ((test_cpp.source).(symbols) !!
    "operator new(unsigned long, enum std::align_val_t)"%cpp_name).
Proof. vm_compute; eauto. Qed.

Goal complete_type (test_cpp.source).(types)
    "enum std::align_val_t"%cpp_type.
Proof.
  eapply complete_type_enum.
  - vm_compute. reflexivity.
  - constructor.
Qed.
