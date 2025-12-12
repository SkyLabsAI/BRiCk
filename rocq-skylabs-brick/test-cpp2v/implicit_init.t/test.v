Require Import bluerock.lang.cpp.semantics.

Require test.inc_hpp.
Require test.src_cpp.

#[local] Ltac check := vm_compute; reflexivity.

(* inc.hpp < one_two.cpp *)
Example _inc_in_src : bool_decide (sub_module inc_hpp.module src_cpp.module) = true :=
  ltac:(check).

Goal True.
  idtac "Success!".
  exact I.
Qed.
