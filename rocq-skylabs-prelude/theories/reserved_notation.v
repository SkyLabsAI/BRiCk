(*
 * Copyright (c) 2021-2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *
 *
 * Some of the following code is derived from code original to the
 * Iris project. That original code is
 *
 *	Copyright Iris developers and contributors
 *
 * and used according to the following license.
 *
 *	SPDX-License-Identifier: BSD-3-Clause
 *
 * Original Code:
 * https://gitlab.mpi-sws.org/iris/iris/-/blob/bbaf3eaf932b4540f5e8c51545930e8591e5cf14/iris/bi/notation.v
 *
 * Original Iris License:
 * https://gitlab.mpi-sws.org/iris/iris/-/blob/bbaf3eaf932b4540f5e8c51545930e8591e5cf14/LICENSE-CODE
 *)

(** Composition (compatible with SSR) *)
Reserved Notation "f \o g" (at level 50, format "f  \o '/ '  g").

(** CPS *)
Reserved Notation "'let*' x , .. , z := t 'in' f" (at level 200, x closed binder, z closed binder).
Reserved Notation "'let*' := t 'in' f" (at level 200).

(** Boolean ops (compatible with SSR) *)
Reserved Notation "~~ b" (at level 35, right associativity).
Reserved Infix "==>" (at level 55, right associativity).

Reserved Notation "[ && b1 & c ]" (at level 0).
Reserved Notation "[ && b1 , b2 , .. , bn & c ]"
  (at level 0, format "'[hv' [ && '['  b1 , '/'  b2 , '/'  .. , '/'  bn ']' '/ '  &  c ] ']'").

(** These conflict with AC/AU.
Reserved Infix "<<" (at level 35).	(** cf [≪] *)
Reserved Infix ">>" (at level 35).	(** cf [≫] *)
*)

Reserved Infix "`lor`" (at level 50, left associativity).
Reserved Infix "`land`" (at level 40, left associativity).
Reserved Infix "`ldiff`" (at level 40, left associativity).
Reserved Infix "\" (at level 40, left associativity).	(** cf [∖] *)

Reserved Notation "A -mon> B"
  (at level 99, B at level 200, right associativity).

(** Powers *)
Reserved Notation "x '^^{' o '}' n"
  (at level 30, o at level 1, right associativity,
   format "'[  ' x  '/' ^^{ o }  n ']'").
Reserved Infix "^^" (at level 30, right associativity).

(** Fancy updates *)
Reserved Notation "|={ E1 , E2 }=>? b P"
  (at level 99, b at level 9, E1, E2 at level 50, P at level 200,
   format "'[  ' |={ E1 , E2 }=>? b  '/' P ']'").
Reserved Notation "|={ E }=>? b P"
  (at level 99, b at level 9, E at level 50, P at level 200,
   format "'[  ' |={ E }=>? b  '/' P ']'").

(** ** Monads *)
(**
Recall
- \/ (right) at 85
- <*> (left), <$> (right) at 61
- >>= (right), ++ (right) at 60, +++ (?) at 60
- || (left), + (left) at 50
- && (left) at 40
*)
Reserved Infix ">>=" (at level 60, right associativity).
Reserved Infix ">>=@{ M }" (at level 60, right associativity).
Reserved Infix "<|>" (at level 60, right associativity).
Reserved Infix "<|>@{ F } " (at level 60, right associativity).

(** Variations on << <*> >> used by parsers *)
Reserved Infix "<*" (at level 60, right associativity).
Reserved Infix "*>" (at level 60, right associativity).

(* Compatible with letstar.v *)
Reserved Notation "'letM*' x , .. , z := t 'in' f" (at level 200, x closed binder, z closed binder).
Reserved Notation "'letM*' := t 'in' f" (at level 200).
Reserved Notation "'funM' x .. y => t" (at level 200, x binder, y binder, right associativity).

(** ** Iris big ops *)
(**
 * We stick with the levels and associativity used in Iris' big ops
 * notation. Compared to that notation, we:
 *
 * - add an optional break and indentation after binders
 * (significantly improving readability)
 *
 * - use [**], [/\], [\/], [ |-> ] instead of [∗], [∧], [∨], [↦]
 * (slightly improving typeability)
 *
 * TODO: Upstream the formatting box changes.
 *)

(** Big separating conjunction *)

Reserved Notation "'[**' 'list]' i |-> x ∈ l , P"
  (at level 200, l at level 10, i, x at level 1, right associativity,
   format "'[  ' [**  list]  i  |->  x  ∈  l ,  '/' P ']'").
Reserved Notation "'[**' 'list]' x ∈ l , P"
  (at level 200, l at level 10, x at level 1, right associativity,
   format "'[  ' [**  list]  x  ∈  l ,  '/' P ']'").

Reserved Notation "'[**' 'map]' k |-> x ∈ m , P"
  (at level 200, m at level 10, k, x at level 1, right associativity,
   format "'[  ' [**  map]  k  |->  x  ∈  m ,  '/' P ']'").
Reserved Notation "'[**' 'map]' x ∈ m , P"
  (at level 200, m at level 10, x at level 1, right associativity,
   format "'[  ' [**  map]  x  ∈  m ,  '/' P ']'").

Reserved Notation "'[**' 'set]' x ∈ X , P"
  (at level 200, X at level 10, x at level 1, right associativity,
   format "'[  ' [**  set]  x  ∈  X ,  '/'  P ']'").

Reserved Notation "'[**' 'mset]' x ∈ X , P"
  (at level 200, X at level 10, x at level 1, right associativity,
   format "'[  ' [**  mset]  x  ∈  X ,  '/' P ']'").

(** Big conjunction *)

Reserved Notation "'[/\' 'list]' i |-> x ∈ l , P"
  (at level 200, l at level 10, i, x at level 1, right associativity,
   format "'[  ' [/\  list]  i  |->  x  ∈  l ,  '/' P ']'").
Reserved Notation "'[/\' 'list]' x ∈ l , P"
  (at level 200, l at level 10, x at level 1, right associativity,
   format "'[  ' [/\  list]  x  ∈  l ,  '/' P ']'").

(** Big disjunction *)

Reserved Notation "'[\/' 'list]' i |-> x ∈ l , P"
  (at level 200, l at level 10, i, x at level 1, right associativity,
   format "'[  ' [\/  list]  i  |->  x  ∈  l ,  '/' P ']'").
Reserved Notation "'[\/' 'list]' x ∈ l , P"
  (at level 200, l at level 10, x at level 1, right associativity,
   format "'[  ' [\/  list]  x  ∈  l ,  '/' P ']'").

(** ** Comparisons *)

Reserved Infix "?=@{ A }" (at level 70, no associativity).
Reserved Infix "<@{ A }" (at level 70, no associativity).
Reserved Infix "<=@{ A }" (at level 70, no associativity).
Reserved Infix ">@{ A }" (at level 70, no associativity).
Reserved Infix ">=@{ A }" (at level 70, no associativity).
