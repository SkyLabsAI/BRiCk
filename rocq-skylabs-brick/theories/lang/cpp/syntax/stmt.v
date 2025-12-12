(*
 * Copyright (c) 2020-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bluerock.prelude.base.
Require Import bluerock.lang.cpp.syntax.core.
Require Import bluerock.prelude.bytestring.

Set Primitive Projections.

Export core(Stmt(..)).
Export core(VarDecl(..)).

Notation Stmt := Stmt.
Notation MStmt := Stmt (only parsing).

Notation VarDecl := VarDecl.
Notation MVarDecl := VarDecl (only parsing).

Definition Sskip : Stmt := Sseq nil.

