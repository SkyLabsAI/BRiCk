(*
 * Copyright (C) 2026 Skylabs AI, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.ltac2.extra.internal.init.

(** This defines the interface of the continuation-passing-style monad.

    Generic monadic constructions can be defined in terms of Cps and specialized; for a monad [Foo],
    [Foo.bind x] turns [x : 'a foo] into [('a, 'r) cps] and for [x : ('a, 'r) cps], [x Foo.ret]
    creates a value of type ['a foo]. *)
Module Cps.
  Import Ltac2 Init.

  Ltac2 mret (x : 'a) : ('a, 'r) cps := fun ret => ret x.
  Ltac2 bind (mx : ('a, 'r) cps) (f : 'a -> ('b, 'r) cps) : ('b, 'r) cps := fun ret =>
      mx (fun x =>
      f x ret).
  Ltac2 map (f : 'a -> 'b) : ('a, 'r) cps -> ('b, 'r) cps :=
    fun ma ret => ma (fun a => ret (f a)).

  (** [Ap] provides an applicative-style interface for the CPS monad.

      The [Ap] interface can be used in one of two ways:

      1. With [f : 'a -> 'b -> 'c -> 'd], [ma : ('a, 'r) cps], [mb : ('b, 'r) cps],
         [mc : ('c, 'r) cps], one might want to write, as one would in Haskell,
         [f <$> ma <*> mb <*> mc] to apply [f] to the result of running each one of [ma], [mb],
         [mc]. With the [Ap] interface, one can write a similar series of applications as
         [_fmap f (_ap ma) (_ap mb) (_ap mc) _done]. [_done] can be replaced with [_to_option] or
         [_to_result] to return the result as [option] or [result] types instead of [cps].


      2. With the variables [ma : ('a, 'r) cps], [mf : 'a -> ('b, 'r) cps] and [mg : 'b -> ('c, 'r) cps],
         we may want to combine them as [ma >>= mf >>= mg]. The [Ap] interface instead allows us to
         write the following: [_start ma (_bind mf) (_bind mg) _done].
   *)

  Module Ap.
    Import Ltac2 Constr Unsafe Printf.

    Ltac2 Type ('a, 'r) acc := ('a, 'r) cps .

    (** Starters *)
    Ltac2 fmap (x : 'a) (k : ('a, 'r) cps -> 'k) : 'k :=
      k (Cps.mret x).
    Ltac2 start (mx : ('a, 'r) cps) (k : ('a, 'r) cps -> 'k) : 'k :=
      k mx.

    (** Combinators *)
    Ltac2 ap (mx : ('a, 'r) cps) (mf : ('a -> 'b, 'r) cps) (k : ('b, 'r) cps -> 'k) : 'k :=
      k  (fun ret =>
      mf (fun f =>
      mx (fun a =>
      ret (f a)))).
    Ltac2 bind (mx : 'a -> ('b, 'r) cps) (mf : ('a, 'r) cps) (k : ('b, 'r) cps -> 'k) : 'k :=
      k (Cps.bind mf mx).

    (** Finishers *)
    Ltac2 done (x : ('a, 'r) cps) : ('a, 'r) cps := x.
    Ltac2 to_option (x : ('a, 'r) cps) : 'a option := x (fun a => Some a).
    Ltac2 to_result (x : ('a, 'r) cps) : 'a result := x (fun a => Val a).

  End Ap.

End Cps.
