Require Import skylabs.ltac2.tc_crush.crush.

Goal True.
Proof.
    crush.
Qed.

Goal False -> False.
Proof.
    crush.
Qed.

Goal True /\ (False -> False).
Proof.
    crush.
Qed.
