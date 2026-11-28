(*
 * Copyright (C) 2022 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(**
 * This file declares some Dbs for our developments.
 *)

(* [sl_opacity] is a database for marking definitions opaque.
   It is intended to be extended by users of [Hint Opaque] entries.
 *)
Create HintDb sl_opacity discriminated.

(* Typeclass search deeper than this is most likely a loop between instances:
   report it as an error with the goals on the offending branch, instead of
   backtracking into other instances. [#[global]] since most files only
   [Require] this one, e.g. via [skylabs.prelude.base]. *)
#[global] Set Typeclasses Fatal Depth 30.

Create HintDb pure discriminated.
