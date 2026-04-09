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

#[global] Reserved Notation "'[ltac2' t ]" (format "[ltac2  t ]").

Module Type LTAC2_REF.
  Parameter t : Prop.
  Parameter _mk : t.
End LTAC2_REF.

(** [Ltac2Ref.t] is a trivial inductive type used to store names of Ltac2
    tactics via proxy constants. The constructor [_mk] is not meant to be used
    directly. Instead, use the [make_ltac2_ref] tactic which ensures that the
    reference being built does not depend on section variables.
    << Definition my_tactic : Ltac2Ref.t. make_ltac2_ref. Qed. >>
 *)
Module Ltac2Ref : LTAC2_REF.
  Inductive _t := __mk.
  Definition t := _t.
  Definition _mk := __mk.
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

  Ltac2 check_constant (c : constr) :=
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.Constant r _ => ConstRef r
    | _ =>
        let msg := fprintf "[ltac2_tac] must refer to a constant. Found: %t" c in
        log[tc_dispatch, 1] "%m" msg;
        Control.zero (Tactic_failure (Some msg))
  end.

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
      (check_constant h, Array.to_list args)
    in
    match resolve_ltac2 r args with
    | Some f => f ()
    | None =>
        let msg := fprintf "Could not find Ltac2 tactic: %t" c in
        log[tc_dispatch, 1] "%m" msg;
        Control.zero (Tactic_failure (Some msg))
    end.

  Ltac2 check_ref () :=
  (* We want to make sure that no section variables are used. There might be
     arguments already introduced. We revert all non-section variables and check
     that the resulting type does not depend on section variables. *)
    let hyps := Control.hyps () in
    let to_revert :=
      let f (i, _, _) := if Control.is_section_variable i then None else Some i in
      List.map_filter f hyps
    in
    Std.revert to_revert;
    let g := Control.goal () in
    let deps := Constr.Vars.vars_really_needed g in
    let f v :=
      if Control.is_section_variable v then
        let msg := fprintf "Signature %t depends on section variable %I" g v in
        Control.zero (Invalid_argument (Some msg))
      else
        ()
    in
    List.iter f (FSet.elements deps).

  Ltac2 check_ref_use (t : preterm) :=
    let t := Constr.pretype t in
    let (h, args) := Constr.decompose_app t in
    let r := check_constant h in
    match resolve_ltac2 r (Array.to_list args) with
    | Some _ =>
        let vars := Constr.Vars.vars_really_needed t in
        let f v :=
          if Control.is_section_variable v then
            let msg := fprintf "Ltac2Ref %t depends on section variable %I" h v in
            Control.zero (Invalid_argument (Some msg))
          else
            ()
        in
        List.iter f (FSet.elements vars);
        Control.refine (fun _ => t)
    | None =>
        let msg := fprintf "Could not find Ltac2 tactic: %t" h in
        log[tc_dispatch, 1] "%m" msg;
        Control.zero (Invalid_argument (Some msg))
    end.

  #[global] Ltac2 Notation "goal_dispatch" dbs(opt(seq("with", list0(ident)))) :=
    goal_dispatch_with dbs.

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

Ltac make_ltac2_ref :=
  ltac2:(ltac2.check_ref ()); intros; exact Ltac2Ref._mk.

#[global] Notation "'[ltac2' t ]" := (CallLtac2 ltac2:(ltac2.check_ref_use t)) (only parsing).
#[global] Notation "'[ltac2' t ]" := (CallLtac2 t) (only printing).

Tactic Notation "goal_dispatch" "with" ident_list(dbs) :=
  ltac2.goal_dispatch_with dbs.

Ltac goal_dispatch :=
  ltac2.goal_dispatch.
