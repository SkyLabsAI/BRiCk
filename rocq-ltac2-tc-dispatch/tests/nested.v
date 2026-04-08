Require Import skylabs.ltac2.tc_dispatch.lookup.

Module Import Nested.
  Definition inside_module : Ltac2Ref.t. constructor. Qed.
  Import Printf.
  Ltac2 inside_module () :=
    ltac1:(reflexivity).
  Instance nested_inst : Dispatch (0 = 0) (CallLtac2 inside_module) := {}.
End Nested.

Example test_success_nested : 0 = 0.
Proof.
  goal_dispatch.
Qed.
