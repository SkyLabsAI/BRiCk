(*
 * Copyright (C) 2022-2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import skylabs.ltac2.extra.internal.init.

(** Coq options interface. *)
Module CoqOption.
  Import Ltac2 Init.

  Ltac2 Type t := [
    | BoolValue(bool)
    | IntValue(int option)
    | StringValue(string)
    | StringOptValue(string option)
  ].

  (** [get ls] returns the value of the Coq option described by [ls] (it can
      for example be [["Default"; "Proof"; "Mode"]]). *)
  Ltac2 @ external get : string list -> t option :=
    "br.CoqOptions" "get".
End CoqOption.
