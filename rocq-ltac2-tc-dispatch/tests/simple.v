Require Import skylabs.ltac2.tc_dispatch.lookup.

(* A simple success tactic *)
Definition solve_true : Ltac2Ref.t. make_ltac2_ref. Qed.
Ltac2 solve_true () := ltac1:(exact I).

(* Success Instance for True *)
Instance test_true_inst : Dispatch True [ltac2 solve_true] := {}.

Example test_succeed : True.
Proof.
  goal_dispatch.
Qed.

(* Testing the "No Instance" failure *)
Example test_fail_no_instance : unit.
Proof.
  Fail goal_dispatch.
Abort.

Inductive Broken : nat -> Prop :=.

Section BrokenSection.
  Variable X : Prop.
  (* [make_ltac2_ref] checks that the reference does not depend on section variables. *)
  Definition tac (x : X) : Ltac2Ref.t. Fail make_ltac2_ref. Abort.
  Definition tac (T : Type) : Ltac2Ref.t. make_ltac2_ref. Qed.

  (* Ltac2 [tac] does not exist yet. *)
  Fail #[global] Instance broken_inst : Dispatch (Broken 0) [ltac2 tac] := {}.

  Ltac2 tac := fun () => ().

  (* Type mismatch: tac expects no arguments *)
  Fail #[global] Instance broken_inst : Dispatch (Broken 0) [ltac2 (tac nat)] := {}.

  (* We can circumvent the check in the [[ltac2]] notation by using [CallLtac2] directly *)
  #[global] Instance broken_inst : Dispatch (Broken 0) (CallLtac2 (tac nat)) := {}.
  (* But the resulting hint will not work because our definition [tac] takes
     more arguments than the [tac] tactic. *)
  Example test_fail_bad_string : Broken 0.
  Proof.
    Fail goal_dispatch.
  Abort.
End BrokenSection.
