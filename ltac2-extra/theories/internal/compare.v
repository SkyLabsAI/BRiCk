(*
 * Copyright (C) 2026 Skylabs AI, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import skylabs.ltac2.extra.internal.init.

(** Minor extensions to [Ltac2.String] *)
Module Compare.
  Import Ltac2.

  Ltac2 compare_on (f : 'a -> 'b) (cmp : 'b -> 'b -> int) : 'a -> 'a -> int :=
    fun x y => cmp (f x) (f y).

End Compare.
