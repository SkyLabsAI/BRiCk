(*
 * Copyright (C) 2022-2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import skylabs.ltac2.extra.internal.init.

(** Some functions for [result] type *)
Module Result.
  Import Ltac2 Init.

  Ltac2 mret (x : 'a) : 'a result := Val x.

  Ltac2 bind x f :=
    match x with
    | Val x => f x
    | Err e => Err e
    end.

  Ltac2 or_else (x : 'a result) (y : unit -> 'a result) : 'a result :=
    match x with
    | Val x => Val x
    | Err _ => y ()
    end.

  Ltac2 of_cps (mx : ('a, 'r) cps) : 'a result :=
    mx (fun x => Val x).

  Module Ap.
    Import Ltac2 Constr Unsafe Printf.

    (** Starters *)
    Ltac2 fmap (x : 'a) (k : 'a result -> 'k) : 'k :=
      k (Result.mret x).
    Ltac2 start (mx : 'a result) (k : 'a result -> 'k) : 'k :=
      k mx.
    Ltac2 choice (k : 'a result -> 'k) : 'k :=
      k (Err Not_found).

    (** Combinators *)
    Ltac2 ap (mx : 'a result) (mf : ('a -> 'b) result) (k : 'b result -> 'k) : 'k :=
      k (Result.bind mf (fun f => Result.bind mx (fun x => Result.mret (f x)))).
    Ltac2 bind (mx : 'a -> 'b result) (mf : 'a result) (k : 'b result -> 'k) : 'k :=
      k (Result.bind mf mx).
    Ltac2 alt (mx : unit -> 'a result) (mx0 : 'a result) (k : 'a result -> 'k) : 'k :=
      k (Result.or_else mx0 mx).

    (** Finishers *)
    Ltac2 done (x : 'a result) : 'a result := x.
    Ltac2 to_result (x : 'a result) : 'a result := x.
    Ltac2 to_option (x : 'a result) : 'a option :=
      match x with
      | Val x => Some x
      | Err _ => None
      end.

    Module Export Notations.
      Ltac2 Notation "alt!" f(thunk(self)) := alt f.
    End Notations.

  End Ap.

End Result.
