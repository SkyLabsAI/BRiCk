Require Import skylabs.ltac2.tc_dispatch.lookup.

Module Test1.
  (* A tactic that has multiple successes *)
  Definition solve_nat : Ltac2Ref.t. make_ltac2_ref. Qed.
  Ltac2 solve_nat () := ltac1:(exact 1 + exact 2).

  (* Success Instance for True *)
  Instance test_nat_inst : Dispatch nat [ltac2 solve_nat] := {}.

  Goal exists n : nat, n = 2.
  Proof.
    (* Test that we get the first solution. *)
    Succeed unshelve eexists;
      [goal_dispatch with typeclass_instances
      | lazymatch goal with | |- 1 = 2 => idtac end].
    (* Test that we get the second solution if the first one is insufficient. *)
    unshelve eexists;
      [goal_dispatch with typeclass_instances
      | reflexivity].
  Qed.
End Test1.

Module Test2.
  (* Test that [DispatchException] stops the search. *)
  Definition solve_nat_de : Ltac2Ref.t. make_ltac2_ref. Qed.
  Import Ltac2.
  Ltac2 solve_nat_de () :=
    Control.plus
      (fun () => exact 1)
      (fun _ =>
         Control.plus_bt
           (fun () =>
              Control.zero (DispatchException (Init.Invalid_argument Init.None))
           )
           (fun e bt => match e with DispatchException _ => Control.zero_bt e bt | _ => exact 2 end)
      ).

  (* Success Instance for True *)
  Instance test_nat_de_inst : Dispatch nat [ltac2 solve_nat_de] := {}.

  Set Default Proof Mode "Classic".
  Goal exists n : nat, n = 2.
  Proof.
    (* Test that we get the first solution. *)
    Succeed unshelve eexists;
      [goal_dispatch with typeclass_instances
      | lazymatch goal with | |- 1 = 2 => idtac end].
    (* Test that the search stops before we get to the second solution *)
    Fail unshelve eexists;
      [goal_dispatch with typeclass_instances
      | reflexivity].
  Abort.
End Test2.
