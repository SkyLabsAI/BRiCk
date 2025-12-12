(*
 * Copyright (C) 2021 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(*
 * Some of the following code is derived from code original to the
 * stdpp project. That original code is
 *
 *	Copyright stdpp developers and contributors
 *
 * and used according to the following license.
 *
 *	SPDX-License-Identifier: BSD-3-Clause
 *
 * Original stdpp License:
 * https://gitlab.mpi-sws.org/iris/stdpp/-/blob/54252fbc10eaa88941ec1e157ce2c2e575e42604/LICENSE
 *)
Require Import Stdlib.Unicode.Utf8.

(** Variants of [TCOr]/[TCAnd] for [Type]. *)
Inductive TCOrT (P1 P2 : Type) : Type :=
  | TCOrT_l : P1 → TCOrT P1 P2
  | TCOrT_r : P2 → TCOrT P1 P2.
Existing Class TCOrT.
#[global] Existing Instance TCOrT_l | 9.
#[global] Existing Instance TCOrT_r | 10.
#[global] Hint Mode TCOrT ! ! : typeclass_instances.

Inductive TCAndT (P1 P2 : Type) : Type := TCAndT_intro : P1 → P2 → TCAndT P1 P2.
Existing Class TCAndT.
#[global] Existing Instance TCAndT_intro.
#[global] Hint Mode TCAndT ! ! : typeclass_instances.
