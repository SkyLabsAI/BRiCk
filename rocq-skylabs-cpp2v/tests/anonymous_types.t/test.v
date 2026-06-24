Require Import skylabs.lang.cpp.semantics.

Require test.inc_hpp.
Require test.inc2_hpp.
Require test.one_two_cpp.
Require test.two_one_cpp.

#[local] Ltac check := vm_compute; reflexivity.

(* inc.hpp < one_two.cpp *)
Example _one_in_one_two : bool_decide (sub_module inc_hpp.source one_two_cpp.source) = true :=
  ltac:(check).

(* inc2.hpp < one_two.cpp *)
Example _two_in_one_two : bool_decide (sub_module inc2_hpp.source one_two_cpp.source) = true :=
  ltac:(check).

(* inc.hpp < two_one.cpp *)
Example _one_in_two_one : bool_decide (sub_module inc_hpp.source two_one_cpp.source) = true :=
  ltac:(check).

(* inc2.hpp < two_one.cpp *)
Example _two_in_two_one : bool_decide (sub_module inc2_hpp.source two_one_cpp.source) = true :=
  ltac:(check).

(* These are not strictly guaranteed, but they should hold for these examples *)

(* one_two.cpp < two_one.cpp *)
Example _one_two_two_one : bool_decide (sub_module one_two_cpp.source two_one_cpp.source) = true :=
  ltac:(vm_compute; reflexivity).

Example _two_one_one_two : bool_decide (sub_module two_one_cpp.source one_two_cpp.source) = true :=
  ltac:(vm_compute; reflexivity).

Goal True.
  idtac "Success!".
  exact I.
Qed.
