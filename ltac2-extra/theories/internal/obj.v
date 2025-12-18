(*
 * Copyright (C) 2022-2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import skylabs.ltac2.extra.internal.init.

(** Unsafe primitives to manipulate Ltac2 values (like OCaml's [Obj]). *)
Module Obj.
  Ltac2 @ external magic : 'a -> 'b :=
    "ltac2_extensions" "id".
End Obj.
