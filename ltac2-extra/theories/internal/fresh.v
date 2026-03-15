(*
 * Copyright (C) 2022-2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import skylabs.ltac2.extra.internal.init.
Require Import skylabs.ltac2.extra.internal.constr.
Require Import skylabs.ltac2.extra.internal.string.

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

  Ltac2 for_ssr_ident (free : Free.t) (n : ident) : Free.t * ident option :=
    let ns := Ident.to_string n in
    let ns := if String.equal ns "_" then "__" else ns in
    let n' :=
      Option.bind (String.remove_prefix "_" ns) (fun ns =>
      Option.bind (String.remove_suffix "_" ns) (fun ns =>
      Some (Fresh.for_name free (Ident.of_string ns)))) in
    match n' with
    | Some (free, n') => (free, Some n')
    | None => (free, None)
    end.

End Fresh.
