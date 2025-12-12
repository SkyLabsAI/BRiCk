(*
 * Copyright (c) 2020 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bluerock.prelude.base.

(** virtual addresses *)
Definition vaddr : Set := N.
Bind Scope N_scope with vaddr.

(** physical addresses *)
Definition paddr : Set := N.
Bind Scope N_scope with paddr.
