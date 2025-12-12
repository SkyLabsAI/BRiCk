(*
 * Copyright (C) 2021-2022 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bluerock.prelude.telescopes.
Require Import bluerock.prelude.tactics.telescopes.

(** * Tactics for [Proper] instances *)
(**
Overview: [f_equiv_tidy] and [solve_proper_tidy] are alternatives to
their stdpp counterparts.

- They use [destruct_tele/=] to destroy telescopic arguments in
context, introduce universal quantifiers.

- They unfold [const] in the conclusion.

- They account for (some) higher-order goals. Specifically,
[f_equiv_tidy] unfolds [pointwise_relation] in context, and
[solve_proper_tidy] uses [trivial]. Thus they can solve goals like
[f1, f2 : T -> Prop, Hf : pointwise_relation T R f1 f2, x : T |-- R
(f1 x) (f2 x)] (where the [f_i] can take any number of arguments) but
they cannot apply such an [Hf] and then solve a higher-order subgoal
stated in terms of [pointwise_relation].

TODO: Revisit now that we bumped stdpp:

- [f_equiv] directly supports some higher-order goals

- [tele_arg] now uses a fixpoint representation which should make
[destruct_tele/=] unnecessary

*)

#[local] Ltac tidy_proper :=
  repeat lazymatch goal with
  | H : pointwise_relation _ _ _ _ |- _ => unfold pointwise_relation in H
  | |- pointwise_relation _ _ _ _ => intros ?
  | |- ∀ _, _ => intros ?
  | |- context [const _] => unfold const
  | t : tele_arg _ |- _ => destruct_tele/=
  end.

Ltac f_equiv_tidy := first [progress tidy_proper | f_equiv].

Ltac solve_proper_tidy_prepare :=
  solve_proper_prepare; tidy_proper.
Ltac solve_proper_tidy_core tac :=
  solve_proper_tidy_prepare;
  solve_proper_core ltac:(fun _ => first [f_equiv_tidy | tac ltac:(())]).
Ltac solve_proper_tidy :=
  solve_proper_tidy_core ltac:(fun _ => trivial).

(** Handy for higher-order functions, especially those involving implicit arguments. *)
Tactic Notation "solve_proper" "using" uconstr(lem) :=
  solve_proper_core ltac:(fun _ => first [by apply lem|f_equiv]).
Tactic Notation "solve_proper" "using" uconstr(lem1) ","
    uconstr(lem2) :=
  solve_proper_core ltac:(fun _ =>
    first [by apply lem1|by apply lem2|f_equiv]
  ).
Tactic Notation "solve_proper" "using" uconstr(lem1) ","
    uconstr(lem2) "," uconstr(lem3) :=
  solve_proper_core ltac:(fun _ =>
    first [by apply lem1|by apply lem2|by apply lem3|f_equiv]
  ).
Tactic Notation "solve_proper" "using" uconstr(lem1) ","
    uconstr(lem2) "," uconstr(lem3) "," uconstr(lem4) :=
  solve_proper_core ltac:(fun _ =>
    first [by apply lem1|by apply lem2|by apply lem3|by apply lem4|f_equiv]
  ).
