(*
 * Copyright (C) 2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import skylabs.ltac2.extra.internal.plugin.

Module TransparentState.
  Import Init.
  Export Ltac2.TransparentState.

  Ltac2 @ external inter : t -> t -> t :=
    "ltac2_extensions" "transparent_state_inter".

  Ltac2 @ external of_hint_db : ident -> t :=
    "ltac2_extensions" "transparent_state_of_db".
End TransparentState.
