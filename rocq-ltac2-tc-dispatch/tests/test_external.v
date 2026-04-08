Require Import skylabs.ltac2.tc_dispatch.lookup.
Require Import skylabs_tests.ltac2.tc_dispatch.external.

Goal 0 = 0.
Proof.
  goal_dispatch.
Qed.
