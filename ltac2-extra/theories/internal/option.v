(*
 * Copyright (C) 2022-2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import skylabs.ltac2.extra.internal.init.
Require Import skylabs.ltac2.extra.internal.constr.

(** Minor extensions to [Ltac2.Option] *)
Module Option.
  Import Ltac2 Init.
  Export Ltac2.Option.

  Ltac2 Type 'a t := 'a option.

  Ltac2 of_option_constr (of_a : constr -> 'a t) (c : constr) : 'a t t :=
    lazy_match! c with
    | None    => Some None
    | Some ?v => Option.bind (of_a v) (fun v => Some (Some v))
    | _       => None
    end.

  Ltac2 iter : ('a -> unit) -> 'a t -> unit := fun f o =>
    match o with
    | None   => ()
    | Some v => f v
    end.
End Option.
