Require Import bluerock.lang.cpp.cpp.

Section with_cpp.
  Context `{Σ : cpp_logic} {σ : genv}.

  Fail Goal forall this : ptr,
      this ,, _field "foo" |-> anyR "int" 1$m |-- emp.

  Fail Goal forall this : ptr,
      this ., "foo" |-> anyR "int" 1$m |-- emp.

  Goal forall this : ptr,
      this ,, _field "C::foo" |-> anyR "int" 1$m |-- emp.
  Proof.
    Show.
  Abort.

  Goal forall this : ptr,
      this ., "C::foo" |-> anyR "int" 1$m |-- emp.
  Proof.
    Show.
  Abort.

  Check "foo"%cpp_name.
  Check "foo::bar"%cpp_name.
End with_cpp.
