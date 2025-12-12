(*
 * Copyright (c) 2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bluerock.lang.cpp.parser.prelude.
Require Import bluerock.lang.cpp.parser.lang.

(** * Derived declaration helpers emitted by cpp2v *)

Module ParserDecl.

  Definition pure_virt (on : obj_name) : obj_name * option obj_name :=
    (on, None).
  Definition impl_virt (on : obj_name) : obj_name * option obj_name :=
    (on, Some on).

  (* This is used for base classes. *)
  Definition mkBase (on : classname) (li : LayoutInfo) : classname * LayoutInfo :=
    (on, li).

End ParserDecl.
