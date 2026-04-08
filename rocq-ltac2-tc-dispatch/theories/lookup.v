(*
 * Copyright (C) 2026 SkyLabs AI, Inc.
 *)
Require Import Ltac2.Ltac2.
Require Import Ltac2.Control.
Require Import Ltac2.Printf.


Require Import Ltac2.Std.
Require Import Stdlib.Strings.PrimString.
Require Import skylabs.ltac2.extra.extra.

Declare ML Module "ltac2-tc-dispatch.plugin".

Module Ltac2Ref.
  (* A trivial inductive type used to store names of Ltac2 tactics via proxy constants.
     Recommended use:
     Definition my_tactic : Ltac2Ref.t. constructor. Qed.
   *)
  Inductive t := _mk.
End Ltac2Ref.

#[universes(polymorphic,cumulative)]
Inductive Handler (goal : Type) : Prop :=
| CallLtac2 (ltac2_tac : Ltac2Ref.t) : Handler goal.
#[global] Arguments CallLtac2 {_} _.


#[universes(polymorphic,cumulative)]
Inductive Dispatch (goal : Type) (handler : Handler goal) := {}.
Existing Class Dispatch.

Module ltac2.
  (* [resolve_ltac2 r args] resolves [r] to an Ltac2 tactic [f] of type [constr
  -> .. -> constr -> unit -> unit] with the number of [constr] arguments being
  equal to [|args|] and returns [f ..args]. *)
  Ltac2 @ external resolve_ltac2 : reference -> constr list -> (unit -> unit) option :=
    "ltac2_tc_dispatch" "resolve_ltac2".

  Ltac2 goal_dispatch_with (dbs : ident list option) :=
    let g := Control.goal () in
    let query := open_constr:(Dispatch $g _) in
    (* let _ := printf "query=%t" query in *)
    let _ := Constr.Unsafe.make (TC.resolve dbs query) in
    (* let _ := printf "inst=%t" inst in *)
    let inst := lazy_match! query with | Dispatch _ ?h => h end in
    let flags := RedFlags.all in
    let reduced_inst := Std.eval_lazy flags inst in
    (* let _ := printf "reduced_inst=%t" reduced_inst in *)

    let c :=
      lazy_match! reduced_inst with
      | CallLtac2 ?c => c
      | _ =>
          let msg := fprintf "Could not reduce %t to record. Stuck at: %t" inst reduced_inst in
          printf "%m" msg;
          Control.zero (Tactic_failure (Some msg))
      end
    in
    let (r, args) :=
      let (h, args) := Constr.decompose_app c in
      match Constr.Unsafe.kind h with
      | Constr.Unsafe.Constant r _ => (ConstRef r, Array.to_list args)
      | _ =>
          let msg := fprintf "[ltac2_tac] must refer to a constant without arguments. Found: %t" c in
          printf "%m" msg;
          Control.zero (Tactic_failure (Some msg))
      end
    in
    match resolve_ltac2 r args with
    | Some f => f ()
    | None =>
        let msg := fprintf "Coult not find Ltac2 tactic: %t" c in
        printf "%m" msg;
        Control.zero (Tactic_failure (Some msg))
    end
  .
End ltac2.

Ltac goal_dispatch :=
  idtac;
  ltac2:(ltac2.goal_dispatch_with None).
