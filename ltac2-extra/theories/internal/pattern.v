(*
 * Copyright (C) 2020-2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import skylabs.ltac2.extra.internal.init.
Require Import skylabs.ltac2.extra.internal.plugin.

Module Pattern.
  Import Ltac2.Ltac2.

  Ltac2 @ external pattern_to_message : pattern -> message :=
    "ltac2_extensions" "pattern_to_message".

  Ltac2 @ external lpattern_to_message : pattern -> message :=
    "ltac2_extensions" "lpattern_to_message".

End Pattern.
