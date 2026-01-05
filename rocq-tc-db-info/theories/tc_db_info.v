(*
 * Copyright (C) BlueRock Security Inc. 2024
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

Declare ML Module "rocq-tc-db-info.plugin".

Require Import Ltac2.Ltac2.

(* [tc_db_info o_ts_db dbs classes] checks the typeclass databases [dbs] for
   [Hint Transparent] terms appearing in hints for typeclasses [classes].

   If [o_ts_db = None], it uses the transparency state of the database that the
   hint being checked is registered in. If [o_ts_db = Some db], it always uses
   [db]'s transparency state no matter in which database hints are registered
   in. *)
Ltac2 @ external tc_db_info : ident option -> ident list -> Std.reference list -> unit := "tc_db_info" "db_opacity_info".


