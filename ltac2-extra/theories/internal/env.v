(*
 * Copyright (C) 2022-2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import skylabs.ltac2.extra.internal.plugin.
Require Ltac2.Ltac2.
Require Export skylabs.ltac2.extra.internal.init.

(** Minor extensions to [Ltac2.Env] *)
Module Env.
  Import Ltac2.
  Import Ltac2.List.
  Export Ltac2.Env.

  (** [path] is shorthand for [ident list]. *)
  Ltac2 Type path := ident list.

  Ltac2 Type exn ::= [ PathNotFound (path) ].

  (** [get_or_throw p] returns the result of [Env.get p] in case of success
      and otherwise fails with [PathNotFound p]. *)
  Ltac2 get_or_fail (p : path) :=
    match Env.get p with
    | Some r => r
    | None => Control.zero (PathNotFound p)
    end.

  (** [get_or_throw p] returns the result of [Env.get p] in case of success
      and otherwise throws (panics with) [PathNotFound p]. *)
  Ltac2 get_or_throw (p : path) :=
    match Env.get p with
    | Some r => r
    | None => Control.throw (PathNotFound p)
    end.

  (** [expand_fst p] returns the first result of [Env.expand p] in case that
      exists and otherwise throws [PathNotFound p]. *)
  Ltac2 expand_fst (p : path) :=
    match Env.expand p with
    | r :: _ => r
    | _ => Control.throw (PathNotFound p)
    end.
End Env.
