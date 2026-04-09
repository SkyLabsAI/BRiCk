(*
 * Copyright (C) 2026 SkyLabs AI, Inc.
 *)
Require Import Ltac2.Ltac2.
Require Import Ltac2.Control.
Require Import Ltac2.Printf.


Require Import Ltac2.Std.
Require Import Stdlib.Strings.PrimString.
Require Import skylabs.ltac2.extra.extra.
Require Import skylabs.ltac2.logger.logger.

Declare ML Module "ltac2-tc-dispatch.plugin".

Module Ltac2Ref.
  (** [Ltac2Ref.t] is a trivial inductive type used to store names of Ltac2
      tactics via proxy constants. Recommended use:
      <<
        Definition my_tactic : Ltac2Ref.t. constructor. Qed.
      >>
   *)
  Inductive t := _mk.
End Ltac2Ref.

(** [Handler goal] represents strategies to apply to goals matching the type
    [goal]. They are registered using [Dispatch] instances. *)
#[universes(polymorphic,cumulative)]
Inductive Handler (goal : Type) : Prop :=
(** [CallLtac2 tac_ref] represents a strategy that calls the Ltac2 tactic
    referenced by [tac_ref] on [goal]. *)
| CallLtac2 (ltac2_tac : Ltac2Ref.t) : Handler goal.
#[global] Arguments CallLtac2 {_} _.

(** Instances of [Dispatch goal handler] instruct the [goal_dispatch] tactic to
    apply [handler] to [goal]. The resolution follows normal typeclass search
    logic, i.e. priorities and opacity are respected. *)
#[universes(polymorphic,cumulative)]
Inductive Dispatch (goal : Type) (handler : Handler goal) := {}.
Existing Class Dispatch.

Ltac2 Log Flag tc_dispatch.

Module ltac2.
  (** [resolve_ltac2 r args] resolves [r] to an Ltac2 tactic [f] of type
      [constr -> .. -> constr -> unit -> unit] with the number of [constr]
      arguments being equal to [|args|] and returns [f ..args]. *)
  Ltac2 @ external resolve_ltac2 : reference -> constr list -> (unit -> unit) option :=
    "ltac2_tc_dispatch" "resolve_ltac2".

  Ltac2 goal_dispatch_with (dbs : ident list option) :=
    let g := Control.goal () in
    let query := open_constr:(Dispatch $g _) in
    log[tc_dispatch, 10] "query: %t" query;
    let _ := Constr.Unsafe.make (TC.resolve dbs query) in
    let inst := lazy_match! query with | Dispatch _ ?h => h end in
    log[tc_dispatch, 10] "inst: %t" inst;
    let flags := { RedFlags.all with Std.rStrength := Std.Head } in
    let reduced_inst := Std.eval_lazy flags inst in
    log[tc_dispatch, 10] "reduced_inst: %t" reduced_inst;

    let c :=
      lazy_match! reduced_inst with
      | CallLtac2 ?c => c
      | _ =>
          let msg := fprintf "Could not reduce %t to record. Stuck at: %t" inst reduced_inst in
          log[tc_dispatch, 1] "%m" msg;
          Control.zero (Tactic_failure (Some msg))
      end
    in
    let (r, args) :=
      let (h, args) := Constr.decompose_app c in
      match Constr.Unsafe.kind h with
      | Constr.Unsafe.Constant r _ => (ConstRef r, Array.to_list args)
      | _ =>
          let msg := fprintf "[ltac2_tac] must refer to a constant without arguments. Found: %t" c in
          log[tc_dispatch, 1] "%m" msg;
          Control.zero (Tactic_failure (Some msg))
      end
    in
    match resolve_ltac2 r args with
    | Some f => f ()
    | None =>
        let msg := fprintf "Could not find Ltac2 tactic: %t" c in
        log[tc_dispatch, 1] "%m" msg;
        Control.zero (Tactic_failure (Some msg))
    end
  .

  #[global] Ltac2 Notation "goal_dispatch" dbs(opt(seq("with", list0(ident)))) := goal_dispatch_with dbs.

  Ltac2 goal_dispatch_with_ltac1 (dbs : Ltac1.t option) :=
    let dbs :=
      let f dbs :=
        List.map
          (fun db => Option.get (Ltac1.to_ident db))
          (Option.get (Ltac1.to_list dbs))
      in
      Option.map f dbs
    in
    goal_dispatch_with dbs.

  Ltac goal_dispatch_with dbs :=
    idtac;
    ltac2:(dbs |- goal_dispatch_with_ltac1 (Some dbs)).
  Ltac goal_dispatch :=
    ltac2:(goal_dispatch_with None).
End ltac2.

Tactic Notation "goal_dispatch" "with" ident_list(dbs) :=
  ltac2.goal_dispatch_with dbs.

Ltac goal_dispatch :=
  ltac2.goal_dispatch.
