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

  Ltac2 or_else (x : 'a option) (y : unit -> 'a option) : 'a option :=
    match x with
    | Some x => Some x
    | None => y ()
    end.

  Ltac2 to_list (x : 'a option) : 'a list :=
    match x with
    | Some x => [x]
    | None => []
    end.

  Ltac2 of_cps (mx : ('a, 'r) cps) : 'a option :=
    mx (fun x => Some x).

  Ltac2 mret (x : 'a) : 'a option := Some x.

  Module Ap.
    Import Ltac2 Constr Unsafe Printf.

    (** Starters *)
    Ltac2 _fmap (x : 'a) (k : 'a option -> 'k) : 'k :=
      k (Option.mret x).
    Ltac2 _start (mx : 'a option) (k : 'a option -> 'k) : 'k :=
      k mx.
    Ltac2 _choice (k : 'a option -> 'k) : 'k :=
      k None.

    (** Combinators *)
    Ltac2 _ap (mx : 'a option) (mf : ('a -> 'b) option) (k : 'b option -> 'k) : 'k :=
      k (Option.bind mf (fun f => Option.bind mx (fun x => Option.mret (f x)))).
    Ltac2 _bind (mx : 'a -> 'b option) (mf : 'a option) (k : 'b option -> 'k) : 'k :=
      k (Option.bind mf mx).
    Ltac2 _alt (mx : unit -> 'a option) (mx0 : 'a option) (k : 'a option -> 'k) : 'k :=
      k (Option.or_else mx0 mx).

    (** Finishers *)
    Ltac2 _done (x : 'a option) : 'a option := x.
    Ltac2 _to_option (x : 'a option) : 'a option := x.
    Ltac2 _to_result (e : unit -> exn) (x : 'a option) : 'a result :=
      match x with
      | Some x => Val x
      | None => Err (e ())
      end.

    Module Export Notations.
      Ltac2 Notation "_alt!" f(thunk(self)) := _alt f.
    End Notations.

  End Ap.

End Option.
