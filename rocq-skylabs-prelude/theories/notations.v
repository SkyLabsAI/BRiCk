(*
 * Copyright (c) 2020 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(** Alternative ASCII notations for stdpp. *)
Require Import stdpp.base.
Require Export bluerock.prelude.reserved_notation.

Infix "==" := (≡) (at level 70, no associativity, only parsing) : stdpp_scope.

Infix "==@{ A }" := (≡@{A})
  (at level 70, only parsing, no associativity) : stdpp_scope.

Notation "(==)" := (≡) (only parsing) : stdpp_scope.
Notation "( X ==.)" := ( X ≡.) (only parsing) : stdpp_scope.
Notation "(.== X )" := (.≡ X ) (only parsing) : stdpp_scope.
Notation "(==@{ A } )" := (≡@{ A } ) (only parsing) : stdpp_scope.

(** For now, no ASCII notation for [≢]. *)

Infix "∖" := difference (only parsing) : stdpp_scope.
Infix "\" := difference : stdpp_scope.
