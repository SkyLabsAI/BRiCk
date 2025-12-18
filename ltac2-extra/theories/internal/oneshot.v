(*
 * Copyright (C) 2022-2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import skylabs.ltac2.extra.internal.init.
Require Import skylabs.ltac2.extra.internal.printf.

(** Oneshots: a reference cell that can be set at most once. *)
Module Oneshot.
  Import Ltac2 Init Printf.

  Ltac2 Type exn ::= [ Already_set ].
  Ltac2 Type exn ::= [ Not_set ].

  Ltac2 Type 'a t := {
    get : unit -> 'a option;
    set : 'a -> unit;
  }.

  (** Get a oneshot's contents. *)
  Ltac2 get_opt (r : 'a t) : 'a option := r.(get) ().

  (** Get a oneshot's contents, or panic if the oneshot isn't set. *)
  Ltac2 get (r : 'a t) : 'a :=
    match get_opt r with Some x => x | None => Control.throw Not_set end.

  (** Set a oneshot, or panic if the oneshot is already set. *)
  Ltac2 set (r : 'a t) (y : 'a) : unit := r.(set) y.

  Ltac2 pp : 'a pp -> 'a t pp := fun pp _ r =>
    fprintf "(Oneshot %a)" (pp_option pp) (Oneshot.get_opt r).

  (** Create an empty oneshot *)
  Ltac2 create () : 'a t :=
    let r : 'a option Ref.ref := Ref.ref None in
    let get () := Ref.get r in
    let set y :=
      match Ref.get r with
      | None => Ref.set r (Some y)
      | Some _ => Control.throw Already_set
      end
    in
    { get := get; set := set }.

  (** Create a full oneshot *)
  Ltac2 init (x : 'a) : 'a t :=
    let get () := Some x in
    let set _ := Control.throw Already_set in
    { get := get; set := set }.
End Oneshot.
