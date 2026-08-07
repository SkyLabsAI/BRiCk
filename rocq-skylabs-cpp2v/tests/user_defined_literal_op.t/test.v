Require Import skylabs.lang.cpp.semantics.
Require Import test.test_cpp.

Succeed Definition ex :
  is_Some (static__source.(symbols) !! "operator""""__units(unsigned long long)"%cpp_name) :=
  ltac:(done).
Succeed Definition ex :
  static__source.(symbols) !! "operator""""_units(unsigned long long)"%cpp_name = None :=
  ltac:(done).
