(*
 * Copyright (C) 2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

(**
We need <<Export>> to make the _contents_ of synterp database
<<NES.db>> available downstream. Side-effect: The NES commands are
also available.
*)
Require Export elpi.apps.NES.NES.

Require Export skylabs.elpi.extra.prelude.

(** * Bundle NES as databases *)
(**
Synopsis:

<<
Require Import skylabs.elpi.extra.NES.

Elpi Command MyCommand.
#[phase="both"] Elpi Accumulate Db NES.db.
#[phase="both"] Elpi Accumulate File skylabs.elpi.extra.NES.code.
Elpi Accumulate lp:{{ ⋯ }}.
Elpi Export MyCommand.
>>
*)

From elpi.apps.NES.elpi Extra Dependency "nes_synterp.elpi" as nes_synterp.
From elpi.apps.NES.elpi Extra Dependency "nes_interp.elpi" as nes_interp.

#[synterp]
Elpi File skylabs.elpi.extra.NES.code lp:{{
  accumulate "coq://elpi.apps.NES.elpi/nes_synterp".
}}.

#[interp]
Elpi File skylabs.elpi.extra.NES.code lp:{{
  accumulate "coq://elpi.apps.NES.elpi/nes_interp".
}}.
