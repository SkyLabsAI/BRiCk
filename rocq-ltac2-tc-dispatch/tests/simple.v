Require Import skylabs.ltac2.tc_dispatch.lookup.

(* A simple success tactic *)
Definition solve_true : Ltac2Ref.t. constructor. Qed.
Ltac2 solve_true () := ltac1:(exact I).

(* A tactic that prints a message *)
Definition say_hello : Ltac2Ref.t. constructor. Qed.
Ltac2 say_hello () := Message.print (Message.of_string "Hello from dynamic lookup!").

(* Success Instance for True *)
Instance test_true_inst : Dispatch True (CallLtac2 solve_true) := {}.

(* Success Instance for False (pointing to a printing tactic) *)
Instance test_hello_inst : Dispatch False (CallLtac2 say_hello) := {}.

Example test_succeed : True.
Proof.
  goal_dispatch.
Qed.

Example test_succeed_print : False.
Proof.
  goal_dispatch.
Fail Qed.
Abort.

(* Testing the "No Instance" failure *)
Example test_fail_no_instance : unit.
Proof.
  Fail goal_dispatch.
Abort.

Inductive Broken : nat -> Prop :=.

Section BrokenSection.
  Variable X : Ltac2Ref.t.

  (* A "Broken" Instance: will be generalized *)
  #[global] Instance broken_inst : Dispatch (Broken 0) (CallLtac2 X) := {}.
End BrokenSection.

(* Generalized [Lta2Ref] *)
Example test_fail_bad_string : Broken 0.
Proof.
  Fail goal_dispatch. (* Triggers the None branch of our match *)
Abort.

(* Applied [Ltac2Ref]s are not supported *)
Definition broken_ref : nat -> Ltac2Ref.t. constructor. Qed.
Instance broken_inst_applied : Dispatch (Broken 1) (CallLtac2 (broken_ref 1)) := {}.

(* Applied [Ltac2Ref] *)
Example test_fail_bad_string : Broken 1.
Proof.
  Fail goal_dispatch. (* Triggers the None branch of our match *)
Abort.
