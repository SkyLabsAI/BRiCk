(*
 * Copyright (C) 2026 Skylabs AI, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.ltac2.extra.internal.init.

Module Identity.
  Import Ltac2 Init.

  Ltac2 bind (x : 'a) (f : 'a -> 'b) : 'b := f x.
  Ltac2 of_cps (ma : ('a, 'r) cps) : 'a := ma (fun a => a).

End Identity.
