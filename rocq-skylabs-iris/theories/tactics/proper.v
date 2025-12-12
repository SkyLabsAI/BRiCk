(*
 * Copyright (C) 2021-2025 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import iris.algebra.ofe. (* f_contractive *)

(** Extends [iris.algebra.ofe.solve_contractive] to "solve_contractive by tac". *)
Tactic Notation "solve_contractive" "by" tactic3(tac) :=
  solve_proper_core ltac:(fun _ => first [ f_contractive | f_equiv | tac ]).

Tactic Notation "solve_contractive" "using" uconstr(lem) :=
  solve_proper_core ltac:(fun _ => first [by apply lem|f_contractive|f_equiv]).
Tactic Notation "solve_contractive" "using" uconstr(lem1) ","
    uconstr(lem2) :=
  solve_proper_core ltac:(fun _ =>
    first [by apply lem1|by apply lem2|f_contractive|f_equiv]
  ).
Tactic Notation "solve_contractive" "using" uconstr(lem1) ","
    uconstr(lem2) "," uconstr(lem3) :=
  solve_proper_core ltac:(fun _ =>
    first [by apply lem1|by apply lem2|by apply lem3|f_contractive|f_equiv]
  ).
Tactic Notation "solve_contractive" "using" uconstr(lem1) ","
    uconstr(lem2) "," uconstr(lem3) "," uconstr(lem4) :=
  solve_proper_core ltac:(fun _ =>
    first [by apply lem1|by apply lem2|by apply lem3|by apply lem4
      |f_contractive|f_equiv]
  ).
