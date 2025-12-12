(*
 * Copyright (c) 2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bluerock.prelude.bytestring.
Require Import bluerock.lang.cpp.parser.prelude.

#[local] Open Scope bs_scope.

Section stmt.
  Definition Sreturn_void : Stmt := Sreturn None.
  Definition Sreturn_val (e : Expr) : Stmt := Sreturn (Some e).
  Definition Sforeach (range ibegin iend : Stmt)
    (init : option Stmt) (cond : option Expr) (inc : option Expr)
    (decl body : Stmt) : Stmt :=
    Sseq (option_list init ++ [range; ibegin; iend; Sfor None cond inc (Sseq [decl; body])]).
End stmt.
