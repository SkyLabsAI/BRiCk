(*
 * Copyright (c) 2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bluerock.lang.cpp.syntax.prelude.
Require Export bluerock.lang.cpp.syntax.core.

#[local] Set Primitive Projections.

(** ** C++ with templates *)
Notation Mname := name (only parsing).
Notation Mglobname := globname (only parsing).
Notation Mobj_name := obj_name (only parsing).
Notation Mtype := type (only parsing).
Notation Mexprtype := exprtype (only parsing).
Notation Mdecltype := decltype (only parsing).
Notation MCast := Cast (only parsing).
Notation Moperator_impl := operator_impl (only parsing).
Notation MMethodRef := MethodRef (only parsing).
Notation MExpr := Expr (only parsing).
Notation Mfunction_type := function_type (only parsing).
Notation Mtemp_param := temp_param (only parsing).
Notation Mtemp_arg := temp_arg (only parsing).
Notation Matomic_name := atomic_name (only parsing).
Notation MBindingDecl := BindingDecl (only parsing).
Notation MVarDecl := VarDecl (only parsing).
Notation MStmt := Stmt (only parsing).
Notation Mfield_name := field_name.t (only parsing).
