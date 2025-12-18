(*
 * Copyright (C) 2022-2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import skylabs.ltac2.extra.internal.init.
Require Import skylabs.ltac2.extra.internal.constr.

(** Minor extensions to [Ltac2.Fresh] *)
Module Fresh.
  Import Ltac2 Init.
  Export Ltac2.Fresh.

  Ltac2 for_ident (free : Free.t) (id : ident) : Free.t * ident :=
    let id := fresh free id in
    let free := Free.union free (Fresh.Free.of_ids [id]) in
    (free, id).

  Ltac2 for_name (free : Free.t) (name : name) : Free.t * ident :=
    let id := Option.default @_fresh name in
    for_ident free id.

  Ltac2 for_rel_decl (free : Free.t) (decl : Constr.Unsafe.RelDecl.t) :
      Free.t * ident :=
    let name := Constr.Unsafe.RelDecl.name decl in
    for_name free name.

End Fresh.
