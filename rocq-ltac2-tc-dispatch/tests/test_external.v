Require Import skylabs_tests.ltac2.tc_dispatch.external.
Require Import skylabs.ltac2.tc_dispatch.lookup.

Goal 0 = 0.
Proof.
  goal_dispatch.
Qed.
