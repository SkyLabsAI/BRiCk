(*
 * Copyright (c) 2022 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require bluerock.lang.cpp.code_notations.
Require bluerock.lang.cpp.logic.wp_notations.
Require Export bluerock.lang.cpp.syntax.notations.

(* NOTE: we intentionally avoid [Export]ing [code_notations] since the printing-only
   notations might break existing clients. Clients can use [Import code_notations] to
   opt-in to the new [Expr]/[Stmt] notations.
 *)
Export type_notations.TypeNotationsInterface.
Export expr_notations.ExprNotationsInterface.
Export stmt_notations.StmtNotationsInterface.

Export wp_notations.
