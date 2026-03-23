(*
 * Copyright (C) 2022-2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import skylabs.ltac2.extra.internal.init.

(** Some functions for [result] type *)
Module Result.
  Import Ltac2 Init.

  Ltac2 mret (x : 'a) : 'a result := Val x.

  Ltac2 bind x f :=
    match x with
    | Val x => f x
    | Err e => Err e
    end.

  Ltac2 or_else (x : 'a result) (y : unit -> 'a result) : 'a result :=
    match x with
    | Val x => Val x
    | Err _ => y ()
    end.

End Result.
