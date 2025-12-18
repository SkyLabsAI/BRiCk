(*
 * Copyright (c) 2020-21 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Export skylabs.iris.extra.spec.notations.
Require Import skylabs.prelude.bytestring.


(** Member Functions *)
Reserved Notation "'\this' this wpp"
  (at level 10, this ident, wpp at level 200).

(** Arguments *)
Reserved Notation "'\args' ls X"
  (at level 10, X at level 200, right associativity,
   format "'[v' '[hv  ' '\args'     '/' ls  ']' '//' X ']'").

Reserved Notation "'\args{' x .. y '}' ls X"
  (at level 10, x binder, y binder, X at level 200, right associativity,
   format "'[v' '[hv  ' '\args{' x  ..  y '}'  '/' ls  ']' '//' X ']'").

Reserved Notation "'\arg' nm v X"
  (at level 10, nm at level 0, v at level 0, X at level 200, right associativity,
   format "'[v' '\arg'  nm  v  '//' X ']'").

Reserved Notation "'\arg{' x .. y } nm v X"
  (at level 10, nm at level 0, v at level 0, x binder, y binder, X at level 200, right associativity,
   format "'[v' '\arg{' x  ..  y '}'  nm  v  '//' X ']'").
