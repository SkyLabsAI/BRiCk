(*
 * Copyright (c) 2023 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

(** This file exports BedRock derive extensions. *)

(* WARNING: importing [elpi.apps.derive] has the side effect of setting
   [Uniform Inductive Parameters], so each individual extension should
   instead use [bluerock.prelude.elpi.derive.common]. *)

Require Export bluerock.prelude.elpi.derive.eq_dec.
(*Test Uniform Inductive Parameters.*)
Require Export bluerock.prelude.elpi.derive.inhabited.
(*Test Uniform Inductive Parameters.*)
Require Export bluerock.prelude.elpi.derive.finite.
(*Test Uniform Inductive Parameters.*)
Require Export bluerock.prelude.elpi.derive.countable.
(*Test Uniform Inductive Parameters.*)
Require Export bluerock.prelude.elpi.derive.finite_type.
(*Test Uniform Inductive Parameters.*)
Require Export bluerock.prelude.elpi.derive.bitset.
(*Test Uniform Inductive Parameters.*)
Require Export bluerock.prelude.elpi.derive.lens.
(*Test Uniform Inductive Parameters.*)
