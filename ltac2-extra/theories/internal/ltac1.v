(*
 * Copyright (C) 2022-2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import skylabs.ltac2.extra.internal.init.
Require Import skylabs.ltac2.extra.internal.constr.
Require Import skylabs.ltac2.extra.internal.string.
Require Import skylabs.ltac2.extra.internal.option.

(** Minor extensions to [Ltac2.Ltac1] *)
Module Ltac1.
  Import Ltac2 Init.
  Export Ltac2.Ltac1.

  (** [to_string v] attempts to build a string from an Ltac1 value, intended
      to be a Coq term representing a string (from [Coq.Strings.String]). *)
  Ltac2 to_string (v : t) : string option :=
    Option.bind (to_constr v) String.of_string_constr.

  Ltac2 to_option (to_a : constr -> 'a option) (v : t) : 'a option option :=
    Option.bind (to_constr v) (Option.of_option_constr to_a).

  Ltac2 to_bool (v : t) : bool option :=
    let to_bool_constr c :=
      lazy_match! c with
      | true  => Some true
      | false => Some false
      | _     => None
      end
    in
    Option.bind (to_constr v) to_bool_constr.
End Ltac1.
