Require Import skylabs.ltac2.tc_dispatch.lookup.

Import Ltac2.
Import Printf.

Set Default Proof Mode "Classic".


Module LengthMismatch.
  Definition tac_with_args : nat -> Ltac2Ref.t. make_ltac2_ref. Qed.
  Ltac2 tac_with_args : constr -> constr -> unit -> unit := fun _ _ _ => ().
  Fail Instance missing_args i b : Dispatch (Nat.eqb i 0 = b) [ltac2 tac_with_args i] := {}.

  (* Ignore static check in [[ltac2]] *)
  Instance missing_args i b : Dispatch (Nat.eqb i 0 = b) (CallLtac2 (tac_with_args i)) := {}.

  Goal Nat.eqb 0 0 = true.
  Proof.
    Fail goal_dispatch.
  Abort.

  Definition tac_with_args_fixed : nat -> bool -> Ltac2Ref.t. make_ltac2_ref. Qed.
  Ltac2 tac_with_args_fixed : constr -> constr -> unit -> unit :=
    fun i b () =>
      refine '(@eq_refl _ _ :> (Nat.eqb $i 0 = $b)).
  Instance dispatch_with_args i b : Dispatch (Nat.eqb i 0 = b) [ltac2 tac_with_args_fixed i b] | 100 := {}.

  Goal Nat.eqb 0 0 = true.
  Proof.
    (* When the warning is set to error, it stops the entire search and does not find the fixed instance. *)
    Fail goal_dispatch.
    (* Turning the warning into a normal warning or turning it off allows backtracking over type errors. *)
    #[local] Set Warnings "-ltac2-tc-dispatch-type-mismatch".
    goal_dispatch.
  Qed.
End LengthMismatch.

Module TypeMismatch.
  Definition tac_with_args : nat -> Ltac2Ref.t. make_ltac2_ref. Qed.
  Ltac2 tac_with_args : unit -> unit -> unit := fun _ _ => ().
  Fail Instance missing_args i b : Dispatch (Nat.eqb i 0 = b) [ltac2 tac_with_args i] := {}.

  (* Ignore static check in [[ltac2]] *)
  Instance missing_args i b : Dispatch (Nat.eqb i 0 = b) (CallLtac2 (tac_with_args i)) := {}.

  Goal Nat.eqb 0 0 = true.
  Proof.
    Fail goal_dispatch.
  Abort.
End TypeMismatch.

Definition tac_with_args : nat -> bool -> Ltac2Ref.t. make_ltac2_ref. Qed.
Ltac2 tac_with_args : constr -> constr -> unit -> unit :=
  fun i b () =>
    refine '(@eq_refl _ _ :> (Nat.eqb $i 0 = $b)).
Instance dispatch_with_args i b : Dispatch (Nat.eqb i 0 = b) [ltac2 tac_with_args i b] := {}.

Goal Nat.eqb 0 0 = true.
Proof.
  goal_dispatch.
Qed.

Goal forall i, Nat.eqb (S i) 0 = false.
Proof.
  intros.
  goal_dispatch.
Qed.

Definition test_reduction : nat -> nat -> Ltac2Ref.t. make_ltac2_ref. Qed.
Ltac2 test_reduction : constr -> constr -> unit -> unit :=
  fun i j () =>
    Control.assert_true (Bool.neg (Constr.equal i j));
    refine 'eq_refl.
Instance test_reduction_inst i j : Dispatch (i = j) [ltac2 test_reduction i j] := {}.

Goal 1 + 2 = 3 + 0.
Proof.
  goal_dispatch.
Qed.
