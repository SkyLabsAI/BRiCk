(*
 * Copyright (C) 2026 Skylabs AI, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import skylabs.ltac2.extra.internal.init.

(** Some functions for [Std.reference]  *)
Module Reference.
  Import Ltac2 Init Std.

  Ltac2 equal (r0 : Std.reference) (r1 : Std.reference) : bool :=
    match r0, r1 with
    | VarRef n0, VarRef n1 => Ident.equal n0 n1
    | ConstRef n0, ConstRef n1 => Constant.equal n0 n1
    | IndRef i0, IndRef i1 => Ind.equal i0 i1
    | ConstructRef c0, ConstructRef c1 => Constructor.equal c0 c1
    | _, _ => false
    end.

End Reference.
