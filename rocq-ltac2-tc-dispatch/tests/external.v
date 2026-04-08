Require Import Ltac2.Ltac2.
Require Import skylabs.ltac2.tc_dispatch.lookup.

Definition ext_tactic : Ltac2Ref.t. constructor. Qed.
Ltac2 ext_tactic () := ltac1:(reflexivity).

#[export]
Instance nested_inst : Dispatch (0 = 0) (CallLtac2 ext_tactic) := {}.
