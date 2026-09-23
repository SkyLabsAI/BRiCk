Require Import skylabs.lang.cpp.syntax.
Require test.test_cpp.

Goal is_Some (test_cpp.source.(symbols) !!
    "operator new(unsigned long, enum std::align_val_t)"%cpp_name).
Proof. vm_compute; eauto. Qed.

(* Clang's implicit aligned allocation function is present, but cpp2v does not
   add the [std::align_val_t] enum referenced by its signature to the type
   table. *)
Eval vm_compute in
  test_cpp.source.(types) !! "std::align_val_t"%cpp_name.
