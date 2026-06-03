(*
 * Copyright (C) 2021 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(** * Convenience wrappers for common PROP-constraint bundles

This file defines wrappers:
  - Ghostly PROP: for `bi`s with ghost updates, and which embed siPropI; and
  - HasUsualOwn PROP T: for MpredLike `bi`s with an `own` operation on CMRA T
*)
Require Import iris.algebra.cmra.
Require Import iris.bi.updates.
Require Import iris.bi.embedding.
Require Import iris.bi.sbi.
Require Import skylabs.iris.extra.bi.own.

Class Ghostly (PROP : bi) := {
  #[global] ghostly_bibupd :: BiBUpd PROP;
  #[global] ghostly_embed :: Sbi PROP;
}.

Class HasUsualOwn (PROP : bi) `{ Ghostly PROP } (T : cmra) := {
  #[global] has_usual_own_own :: HasOwn PROP T;
  #[global] has_usual_own_upd :: HasOwnUpd PROP T;
  #[global] has_usual_own_valid :: HasOwnValid PROP T;
}.
