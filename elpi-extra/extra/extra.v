(*
 * Copyright (C) 2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

(** * Extensions of the Elpi standard library *)

Require Export skylabs.elpi.extra.prelude.
Require Import skylabs.elpi.extra.reification.
Require Export skylabs.elpi.extra.add_predicate_command.

(** <<Rocqlib>> effects *)

Require Stdlib.Init.Datatypes.	(* e.g., <<core.unit.{type,tt}>> *)
Require Stdlib.Numbers.BinNums.	(* e.g., <<num.N.{type,N0,Npos}>> *)
Require skylabs.ltac2.extra.extra.	(* e.g., <<skylabs.ltac2.extra.Ident.rep.{type,Rep}>> *)

(**
Coq's standard library registers <<Byte.byte>> as <<core.byte.type>>.
It does not register the following.
*)
Require Stdlib.Strings.Byte.
Register Stdlib.Strings.Byte.of_N as core.byte.of_N.
Register Stdlib.Strings.Byte.to_N as core.byte.to_N.

Register true as core.bool.true.
Register false as core.bool.false.

Register Numbers.of_Z as reif.numbers.of_Z.
Register Numbers.of_N as reif.numbers.of_N.
Register Numbers.of_pos as reif.numbers.of_pos.
Register Numbers.of_nat as reif.numbers.of_nat.
Register Numbers.of_byte as reif.numbers.of_byte.

Register Numbers.to_N as reif.numbers.to_N.
Register Numbers.to_pos as reif.numbers.to_pos.
Register Numbers.to_nat as reif.numbers.to_nat.
Register Numbers.to_byte as reif.numbers.to_byte.

(** ** Tactics *)
Module tactics.
  Definition anchor := tt.
  Ltac solve_typeclasses_eauto := first [
    solve [ once (typeclasses eauto) ] |
    lazymatch goal with
    | |- ?G => fail 2 "coq.typeclasses_eauto: cannot solve" G
    end
  ].
  Ltac solve_cbn T := let Tred := eval cbn in T in exact Tred.
End tactics.

(** ** User-facing databases *)

(**
Declare the root Elpi bundles so Rocq/dune tracks the Elpi dependency
graphs accumulated below. The <<Elpi File>> names are the public,
phase-specific names used by clients.
*)

From skylabs.elpi.extra.Program Extra Dependency "synterp.elpi" as program_synterp.
From skylabs.elpi.extra.Program Extra Dependency "interp.elpi" as program_interp.
From skylabs.elpi.extra.Tactic Extra Dependency "synterp.elpi" as tactic_synterp.
From skylabs.elpi.extra.Tactic Extra Dependency "interp.elpi" as tactic_interp.
From skylabs.elpi.extra.Command Extra Dependency "synterp.elpi" as command_synterp.
From skylabs.elpi.extra.Command Extra Dependency "interp.elpi" as command_interp.

#[synterp]
Elpi File extra.Program lp:{{
  accumulate "coq://skylabs.elpi.extra/Program/synterp".	% Program/synterp.elpi
}}.
#[interp]
Elpi File extra.Program lp:{{
  accumulate "coq://skylabs.elpi.extra/Program/interp".	% Program/interp.elpi
}}.

(**
WARNING: Accumulating <<extra.Tactic>> in the synterp phase fails. See
../tests/tc_tactic.v for workaround.

TODO: Narrow down and report.
*)
#[synterp]
Elpi File extra.Tactic lp:{{
  accumulate "coq://skylabs.elpi.extra/Tactic/synterp".	% Tactic/synterp.elpi
}}.
#[interp]
Elpi File extra.Tactic lp:{{
  accumulate "coq://skylabs.elpi.extra/Tactic/interp".	% Tactic/interp.elpi
}}.

#[synterp]
Elpi File extra.Command lp:{{
  accumulate "coq://skylabs.elpi.extra/Command/synterp".	% Command/synterp.elpi
}}.
#[interp]
Elpi File extra.Command lp:{{
  accumulate "coq://skylabs.elpi.extra/Command/interp".	% Command/interp.elpi
}}.
