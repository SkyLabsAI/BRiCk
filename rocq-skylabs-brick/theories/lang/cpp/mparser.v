(*
 * Copyright (c) 2023-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bluerock.lang.cpp.parser.reduction.
Require Export bluerock.lang.cpp.syntax.stmt. (* for [Sskip] *)
Require Import bluerock.lang.cpp.parser.name.
Require Import bluerock.lang.cpp.parser.type.
Require Import bluerock.lang.cpp.parser.expr.
Require Import bluerock.lang.cpp.parser.decl.
Require Export bluerock.lang.cpp.mparser.prelude.
Require Export bluerock.lang.cpp.mparser.type.
Require Export bluerock.lang.cpp.mparser.expr.
Require Export bluerock.lang.cpp.mparser.stmt.
Require Export bluerock.lang.cpp.mparser.tu.

Export translation_unit.

Include ParserName.
Include ParserType.
Include ParserExpr.
Include ParserDecl.

Definition Qconst_volatile : Mtype -> Mtype := Tqualified QCV.
Definition Qconst : Mtype -> Mtype := Tqualified QC.
Definition Qvolatile : Mtype -> Mtype := Tqualified QV.
