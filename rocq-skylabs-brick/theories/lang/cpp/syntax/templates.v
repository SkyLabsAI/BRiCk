(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.prelude.base.
Require Import skylabs.prelude.error.
Require Import skylabs.lang.cpp.syntax.core.
Require Export skylabs.lang.cpp.syntax.mcore.
Require Import skylabs.lang.cpp.syntax.decl.
Require Export skylabs.lang.cpp.syntax.translation_unit.
Require Export skylabs.lang.cpp.syntax.namemap.


(** ** Template TUs *)
(**
Template TUs house all templated code in a translation unit and relate
non-templated code induced by template application to the applied
template and its arguments.
*)
Record Mtranslation_unit : Type := {
  msymbols : Msymbol_table;
  mtypes : Mtype_table;
  maliases : Malias_table;	(* we eschew <<Gtypedef>> for now *)
  minstances : Minstance_table
}.
