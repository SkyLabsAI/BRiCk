(*
 * Copyright (C) 2021-2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import skylabs.ltac2.extra.internal.plugin.
Require Import skylabs.ltac2.extra.internal.control.
Require Import skylabs.ltac2.extra.internal.constr.
Require Import skylabs.ltac2.extra.internal.misc.

(** Minor extensions to [Ltac2.Std] *)
Module Std.
  Import Ltac2.
  Export Ltac2.Std.

  Ltac2 Type hint_db.

  Ltac2 @external find_hint_db : ident -> hint_db option :=
    "ltac2_extensions" "find_hint_db".

  (** Type of hint databases passed to tactics like [Std.typeclasses_eauto].
      A value of [None] means search in [typeclass_instances], shelving all
      non-class goals. A value of [Some dbs] means search in databases [dbs],
      without shelving.

      See the following OCaml modules: [Tac2tactics.typeclasses_eauto] and
      [Class_tactics.typeclasses_eauto]. *)
  Ltac2 Type hint_dbs := ident list option.

  (** Unfold the first occurrence of [r] in [c]. *)
  Ltac2 unfold_first (r : Std.reference) (c : constr) : constr :=
    Std.eval_unfold [r, Std.OnlyOccurrences [1]] c.

  (** Reduction functions. *)

  Ltac2 eval_whd : red_flags -> constr -> constr := fun flags c =>
    Misc.eval_whd_with_dbs_and_with_flags false [] flags c.

  (** Reduction with flags. *)

  Ltac2 red_flags_all : Std.red_flags := {
    Std.rStrength := Norm;
    Std.rBeta := true;
    Std.rMatch := true;
    Std.rFix := true;
    Std.rCofix := true;
    Std.rZeta := true;
    Std.rDelta := true;
    Std.rConst := [];
  }.

  Ltac2 red_flags_beta_delta : Std.red_flags := {
    Std.rStrength := Norm;
    Std.rBeta := true;
    Std.rMatch := false;
    Std.rFix := false;
    Std.rCofix := false;
    Std.rZeta := false;
    Std.rDelta := true;
    Std.rConst := [];
  }.

  Ltac2 red_flags_no_delta : reference list -> Std.red_flags := fun refs => {
    Std.rStrength := Norm;
    Std.rBeta := true;
    Std.rMatch := true;
    Std.rFix := true;
    Std.rCofix := true;
    Std.rZeta := true;
    Std.rDelta := false;
    Std.rConst := refs;
  }.

  Ltac2 red_flags_zeta : Std.red_flags := {
    Std.rStrength := Norm;
    Std.rBeta := false;
    Std.rMatch := false;
    Std.rFix := false;
    Std.rCofix := false;
    Std.rZeta := true;
    Std.rDelta := false;
    Std.rConst := [];
  }.

  Ltac2 red_flags_beta : Std.red_flags := {
    Std.rStrength := Norm;
    Std.rBeta := true;
    Std.rMatch := false;
    Std.rFix := false;
    Std.rCofix := false;
    Std.rZeta := false;
    Std.rDelta := false;
    Std.rConst := [];
  }.

  Ltac2 red_flags_none : Std.red_flags := {
    Std.rStrength := Norm;
    Std.rBeta := false;
    Std.rMatch := false;
    Std.rFix := false;
    Std.rCofix := false;
    Std.rZeta := false;
    Std.rDelta := false;
    Std.rConst := [];
  }.

  Ltac2 eval_cbn_all (c : constr) : constr := Std.eval_cbn red_flags_all c.
  Ltac2 eval_whd_all (c : constr) : constr := eval_whd red_flags_all c.

  (** Variant of [Std.intro] that panics on backtracking. *)
  Ltac2 intro_nobacktrack (id : ident option)
      (loc : Std.move_location option) : unit :=
    Control.once_nobacktrack (fun () => Std.intro id loc).

  Ltac2 constant_to_reference : constr -> reference := fun c =>
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.Constant c _ => ConstRef c
    | _ => Control.throw_invalid_argument "Std.constant_to_reference"
    end.

  Ltac2 Type strategy := [ Dfs | Bfs ].
  Ltac2 Type tc_config := {
    unique : bool;
    only_classes : bool;
    best_effort : bool;
    strategy : strategy;
    depth : int option;
    dep : bool;
  }.

  Ltac2 default_tc_config : tc_config := {
    unique := false;
    only_classes := false;
    best_effort := false;
    strategy := Dfs;
    depth := None;
    dep := true;
  }.

  Ltac2 @external typeclasses_eauto_dbs : tc_config -> hint_db list -> unit :=
    "ltac2_extensions" "typeclasses_eauto_dbs".
End Std.
