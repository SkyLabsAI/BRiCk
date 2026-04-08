Require Import skylabs.ltac2.tc_dispatch.lookup.

Import Ltac2.
Import Printf.

Definition tac_with_args : nat -> bool -> Ltac2Ref.t. constructor. Qed.
Ltac2 tac_with_args : constr -> constr -> unit -> unit :=
  fun c1 c2 () =>
    refine '(@eq_refl _ _ :> (Nat.eqb $c1 0  = $c2)).

Instance dispatch_with_args i b : Dispatch (Nat.eqb i 0 = b) (CallLtac2 (tac_with_args i b)) := {}.

Set Default Proof Mode "Classic".

Goal Nat.eqb 0 0 = true.
Proof.
  goal_dispatch.
Qed.

Goal forall i, Nat.eqb (S i) 0 = false.
Proof.
  intros.
  goal_dispatch.
Qed.
