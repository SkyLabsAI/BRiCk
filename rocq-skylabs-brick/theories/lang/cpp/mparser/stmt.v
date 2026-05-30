(*
 * Copyright (c) 2023-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import skylabs.lang.cpp.mparser.prelude.
Require Import skylabs.lang.cpp.mparser.expr.
Require Export skylabs.lang.cpp.parser.stmt.
Require Import skylabs.lang.cpp.syntax.typing.

(** ** Template-only derived variable declarations emitted by cpp2v *)

Definition Dvar (name : localname) (t : Mdecltype) (init : option MExpr) : MVarDecl :=
  Dvar name t (Einitializing_type t <$> init).
