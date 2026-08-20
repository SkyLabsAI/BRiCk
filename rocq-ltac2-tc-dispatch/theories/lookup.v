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

Import Std Control.

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
Variant Handler (goal : Type) : Prop :=
(** [CallLtac2 tac_ref] represents a strategy that calls the Ltac2 tactic
    referenced by [tac_ref] on [goal]. *)
| CallLtac2 (ltac2_tac : Ltac2Ref.t) : Handler goal.
#[global] Arguments CallLtac2 {_} _.

(** Instances of [Dispatch goal handler] instruct the [goal_dispatch] tactic to
    apply [handler] to [goal]. The resolution follows normal typeclass search
    logic, i.e. priorities and opacity are respected. *)
#[universes(polymorphic,cumulative)]
Class Dispatch (goal : Type) (handler : Handler goal) := {}.

Ltac2 Log Flag tc_dispatch.

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

(** [DispatchException] is a wrapper around exceptions. Exceptions wrapped in it
    will _not_ trigger backtracking in the search for [Dispatch] hints in
    [goal_dispatch_with]. *)
Ltac2 Type exn ::= [ DispatchException (exn) ].

(** [goal_dispatch_with dbs] resolves a [Dispatch] instance from the databases
    <dbs> and interprets the handler. This effectively acts like a <match goal>
    where the branches come from [Dispatch] hints in the the hint databases.

    The tactic runs the handlers in the order that they are found by typeclass
    search. The tactic completes successfully if any matching handler succeeds,
    otherwise it fails with `Control.zero`. If a handler raises an exception of
    the form [DispatchException _], the exception (including the wrapper) is
    passed through to the client of [goal_dispatch_with]. All other exceptions
    trigger backtracking in the typeclass search.

    NOTE: [Dispatch] instances should not be directly added to
    <typeclass_instances> because <typeclass_instances> is used in all searches.
    *)
Ltac2 goal_dispatch_with (dbs : Std.hint_db list) :=
  let g := Control.goal () in
  let query := open_constr:(Dispatch $g _) in
  let rec go (next : unit -> unit) :=
    let on_error :=
      match Control.case_bt next with
      | Control.Val_bt (_, on_error) => fun e => go (fun () => on_error e)
      | Control.Err_bt e bt => Control.zero_bt e bt
      end
    in
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
    | Some f =>
        Control.plus_bt f
          (fun e bt =>
             match e with
             | DispatchException e => Control.zero_bt e bt
             | _ => on_error e
             end
          )
    | None =>
        let msg := fprintf "Could not find Ltac2 tactic: %t" c in
        log[tc_dispatch, 1] "%m" msg;
        on_error (Tactic_failure (Some msg))
    end
  in
  log[tc_dispatch, 10] "query: %t" query;
  go (fun () => let _ := TC.resolve_dbs_all dbs query in ()).

(** Checks that the current proof does not require any <Section> variables.
      Fails with <Control.zero> if any <Section> variable is used.
  *)
Ltac2 check_requires_no_section_vars () :=
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

(** Checks whether the given term depends on any <Section> variables. *)
Ltac2 check_ref_uses_section_vars (t : preterm) :=
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
  let ids :=
    match dbs with
    | None => [@typeclass_instances]
    | Some dbs =>
        List.map
          (fun id => Option.get (Ltac1.to_ident id))
          (Option.get (Ltac1.to_list dbs))
    end
  in
  let dbs :=
    let f id :=
      match Std.find_hint_db id with
      | Some db => db
      | None => zero_invalid! "Could not find hint db %I" id
      end
    in
    List.map f ids
  in
  goal_dispatch_with dbs.

Ltac goal_dispatch_with_ dbs :=
  idtac;
  let f := ltac2:(dbs |- goal_dispatch_with_ltac1 (Some dbs)) in
  f dbs.
Ltac goal_dispatch :=
  idtac;
  ltac2:(goal_dispatch_with_ltac1 None).

Ltac make_ltac2_ref :=
  ltac2:(check_requires_no_section_vars ()); intros; exact Ltac2Ref._mk.

#[global] Notation "'[ltac2' t ]" := (CallLtac2 ltac2:(check_ref_uses_section_vars t)) (only parsing).
#[global] Notation "'[ltac2' t ]" := (CallLtac2 t) (only printing).

Tactic Notation "goal_dispatch" "with" ident_list(dbs) :=
  goal_dispatch_with_ dbs.
