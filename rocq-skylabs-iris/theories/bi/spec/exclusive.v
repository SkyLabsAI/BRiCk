(*
 * Copyright (C) 2021-2022 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bluerock.iris.extra.bi.prelude.
Require Import bluerock.iris.extra.bi.observe.
Import ChargeNotation.

#[local] Set Primitive Projections.

(** * Spec building block: Exclusive tokens *)
(**
Overview:

- [ExclusiveN P], [ExclusiveTokenN P]

Exclusive tokens provide a "token" that can be owned by exactly one
entity. They can be be useful when you want to establish that only one
client can be in a particular state.
*)

(** [ExclusiveN P] states that there can be at most one [P a_1 ... a_N] *)
Notation Exclusive0 P := (Observe2 False P P).
Notation Exclusive1 P := (∀ a1 a2, Observe2 False (P a1) (P a2)).
Notation Exclusive2 P := (∀ a1 a2 b1 b2, Observe2 False (P a1 b1) (P a2 b2)).
Notation Exclusive3 P := (∀ a1 a2 b1 b2 c1 c2, Observe2 False (P a1 b1 c1) (P a2 b2 c2)).
Notation Exclusive4 P := (∀ a1 a2 b1 b2 c1 c2 d1 d2, Observe2 False (P a1 b1 c1 d1) (P a2 b2 c2 d2)).
Notation Exclusive5 P := (∀ a1 a2 b1 b2 c1 c2 d1 d2 e1 e2, Observe2 False (P a1 b1 c1 d1 e1) (P a2 b2 c2 d2 e2)).
Notation Exclusive6 P := (∀ a1 a2 b1 b2 c1 c2 d1 d2 e1 e2 f1 f2, Observe2 False (P a1 b1 c1 d1 e1 f1) (P a2 b2 c2 d2 e2 f2)).

(** [P] is an exclusive token. *)
Class ExclusiveToken {PROP : bi} {P : PROP} : Prop :=
{ #[global] token_timeless :: Timeless P
; #[global] token_excl :: Exclusive0 P
}.
Arguments ExclusiveToken {_} _.
Notation ExclusiveToken0 := ExclusiveToken.

(**
[P a] is an exclusive token for any [a].

NOTE the predicate is exclusive *independent* of [a]. If there is one
exclusive token per argument, then use [forall a, ExclusiveToken (P
a)].
*)
Class ExclusiveToken1 (PROP : bi) {A} {P : A -> PROP} : Prop :=
{ #[global] token1_timeless :: Timeless1 P
; #[global] token1_excl :: Exclusive1 P
}.
Arguments ExclusiveToken1 {_ _} _.

Class ExclusiveToken2 (PROP : bi) {A B} {P : A -> B -> PROP} : Prop :=
{ #[global] token2_timeless :: Timeless2 P
; #[global] token2_excl :: Exclusive2 P
}.
Arguments ExclusiveToken2 {_ _ _} _ : assert.

Class ExclusiveToken3 (PROP : bi) {A B C} {P : A -> B -> C-> PROP} : Prop :=
{ #[global] token3_timeless :: Timeless3 P
; #[global] token3_excl :: Exclusive3 P
}.
Arguments ExclusiveToken3 {_ _ _ _} _ : assert.

Class ExclusiveToken4 (PROP : bi) {A B C D} {P : A -> B -> C-> D -> PROP} : Prop :=
{ #[global] token4_timeless :: Timeless4 P
; #[global] token4_excl :: Exclusive4 P
}.
Arguments ExclusiveToken4 {_ _ _ _ _} _ : assert.

Class ExclusiveToken5 (PROP : bi) {A B C D E}
  {P : A -> B -> C-> D -> E -> PROP} : Prop :=
{ #[global] token5_timeless :: Timeless5 P
; #[global] token5_excl :: Exclusive5 P
}.
Arguments ExclusiveToken5 {_ _ _ _ _ _} _ : assert.

Class ExclusiveToken6 (PROP : bi) {A B C D E F}
  {P : A -> B -> C-> D -> E -> F -> PROP} : Prop :=
{ #[global] token6_timeless :: Timeless6 P
; #[global] token6_excl :: Exclusive6 P
}.
Arguments ExclusiveToken6 {_ _ _ _ _ _ _} _ : assert.

Ltac solve_exclusive := solve [intros; split; apply _].
