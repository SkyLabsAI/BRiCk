(*
 * Copyright (C) 2022-2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import skylabs.ltac2.extra.internal.init.
Require Import skylabs.ltac2.extra.internal.constr.
Require Import skylabs.ltac2.extra.internal.control.

(** Testing the backtrace primitives. *)
Module BT_test.
  Import Ltac2.

  Ltac2 f () := let _ := Int.add 1 1 in Control.zero (Invalid_argument None).

  Goal True.
  Proof.
    (* Uncomment the line below and make sure that [f] appears in the output. *)
    (* Set Ltac2 Backtrace. *)
    Fail Control.plus_bt f (fun e bt => Control.zero_bt e bt).
    Fail Control.plus_bt f (fun e bt => Control.throw_bt e bt).
  Abort.
End BT_test.

(** Testing [State] primitives. *)
Module State_test.
  Import Init Ltac2.

  Ltac2 Type 'a Control.State.t ::= [MyCache].
  (* local alias to fix the type parameter ['a]. *)
  Ltac2 myCache : (constr list) Control.State.t := MyCache.
  Ltac2 get ()  : constr list  :=
    Option.default [] (Control.State.get_state (myCache)).
  Ltac2 set_ (t : constr list) := Control.State.set_state (myCache) t.

  Goal forall x : nat, True /\ True.
    set_ [].
    set_ ('False :: get ()).
    if List.mem Constr.equal 'False (get ()) then () else fail.
    intro.
    (* Most tactics automatically copy state to new subgoals *)
    if List.mem Constr.equal 'False (get ()) then () else fail. (* [intro] preserves state. *)
    split.
    {
      if List.mem Constr.equal 'False (get ()) then () else fail. (* [split] preserves state. *)
      assert (True).
      {
        if List.mem Constr.equal 'False (get ()) then () else fail. (* [assert] preserves state. *)

        (* These are proper copies so that mutating the state within a
            subgoal does not affect the original goal's state. See 4 lines below. *)
        set_ [].
        exact I.
      }
      (* Original goal state unchanged. *)
      if List.mem Constr.equal 'False (get ()) then () else fail.

      Control.refine (fun () => '((fun x : bool => I) _)).
      if List.mem Constr.equal 'False (get ()) then () else fail. (* [refine] preserves state. *)
      exact true.
    }


    (* Not sure what this test was supposed to be about. *)
    set_ (List.filter (fun x => Bool.neg (Constr.equal 'False x)) (get ())).
    Fail (if List.mem Constr.equal 'False (get ()) then () else fail).


    (* [Control.new_goal] *)
    set_ (('False :: (get ()))).
    (* The new goal does not automatically inherit the original goal's state *)
    Fail
      let (ev, _) := Constr.Evar.of_constr (Constr.Evar.make 'nat) in
      Control.new_goal ev > [|
        if List.mem Constr.equal 'False (get ()) then () else fail
      ].
    (* [new_goal_w_state] *)
    let (ev, _) := Constr.Evar.of_constr (Constr.Evar.make 'nat) in
    Control.new_goals_w_state [ev] > [|
      if List.mem Constr.equal 'False (get ()) then () else fail
    ].
  Abort.
End State_test.
