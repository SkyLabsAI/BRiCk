(*
 * Copyright (C) 2022-2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import skylabs.ltac2.extra.internal.init.

(** Emitting Coq warnings. *)
Module Warnings.
  Import Ltac2 Init.

  (** Type of a warning, values can only be constructed via OCaml. *)
  Ltac2 Type t.

  Ltac2 @ external emit : t -> message -> unit :=
    "warnings" "emit_warning".
End Warnings.
