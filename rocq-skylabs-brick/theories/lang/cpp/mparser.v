(*
 * Copyright (c) 2023-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import skylabs.lang.cpp.parser.reduction.
Require Export skylabs.lang.cpp.syntax.stmt. (* for [Sskip] *)
Require Import skylabs.lang.cpp.parser.name.
Require Import skylabs.lang.cpp.parser.type.
Require Import skylabs.lang.cpp.parser.expr.
Require Import skylabs.lang.cpp.parser.decl.
Require Export skylabs.lang.cpp.mparser.prelude.
Require Export skylabs.lang.cpp.mparser.type.
Require Export skylabs.lang.cpp.mparser.expr.
Require Export skylabs.lang.cpp.mparser.stmt.
Require Export skylabs.lang.cpp.mparser.tu.

Export translation_unit.

Include ParserName.
Include ParserType.
Include ParserExpr.
Include ParserDecl.

Definition Qconst_volatile : Mtype -> Mtype := Tqualified QCV.
Definition Qconst : Mtype -> Mtype := Tqualified QC.
Definition Qvolatile : Mtype -> Mtype := Tqualified QV.
