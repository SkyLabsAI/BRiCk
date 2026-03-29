Require Import Stdlib.Lists.List.
Require Import Stdlib.Strings.PrimString.
Require Import skylabs.ltac2.tc_dispatch.lookup.

#[local] Open Scope pstring_scope.

(* A simple success tactic *)
Ltac2 solve_true () := ltac1:(exact I).

(* A tactic that prints a message *)
Ltac2 say_hello () := Message.print (Message.of_string "Hello from dynamic lookup!").

(* Success Instance for True *)
Instance test_true_inst : Ltac2Lookup True := {
  ltac2_path := "simple" :: "tc_dispatch" :: "ltac2" :: "skylabs_tests" :: nil;
  ltac2_name := "solve_true";
}.

(* Success Instance for False (pointing to a printing tactic) *)
Instance test_hello_inst : Ltac2Lookup False := {
  ltac2_path := nil;
  ltac2_name := "say_hello";
}.

(* A "Broken" Instance: String name does not exist *)
Instance broken_inst : Ltac2Lookup (True -> True) := {
  ltac2_path := nil;
  ltac2_name := "non_existent_tactic_12345";
}.

Example test_succeed : True.
Proof.
  goal_dispatch.
Abort.


(* Testing the "No Instance" failure *)
Example test_fail_no_instance : unit.
Proof.
  Fail goal_dispatch.
Abort.

(* Testing the "Invalid Name" failure *)
Example test_fail_bad_string : nat.
Proof.
  Fail goal_dispatch. (* Triggers the None branch of our match *)
Abort.
