(*
 * Copyright (C) 2022-2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import skylabs.ltac2.extra.internal.plugin.

(** Minor extensions to [Ltac2.Init] *)
Module Init.
  Import Ltac2.
  Export Ltac2.Init.

  (** For readability *)
  Ltac2 Type type := constr.
  Ltac2 Type term := constr.

  (** User-facing names *)
  Ltac2 Type name := ident option.

  (** Types for printing formats and functions. Examples:
      - Printers that do not terminate have type [('a,'r) kprintf] for any
        return type ['r].
      - [Printf.printf] has type [('a,unit) kprintf].
      - [Printf.fprintf] has type [('a,message) kprintf]. *)
  Ltac2 Type ('a,'r) kfmt := ('a,unit,message,'r) format.
  Ltac2 Type ('a,'r) kprintf := ('a,'r) kfmt -> 'a.

  (** Type of pretty-printers for type ['a], suited to format string [%a]. *)
  Ltac2 Type 'a pp := unit -> 'a -> message.

End Init.
