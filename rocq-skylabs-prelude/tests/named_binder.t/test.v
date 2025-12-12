(*
 * Copyright (C) 2025 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bluerock.prelude.named_binder.

Require Import Stdlib.Strings.PrimString.

Set Printing All.
Ltac2 Eval Binder.name_binders Init.true '(fun (x : NamedBinder bool "test") => x = x).
Ltac2 Eval Binder.name_binders Init.true
  '(fun (x : NamedBinder bool "test") => @pair (NamedBinder bool "x") bool x true = (x, false)).
Ltac2 Eval Binder.name_binders Init.false
  '(fun (x : NamedBinder bool "test") => @pair (NamedBinder bool "x") bool x true = (x, false)).
