(*
 * Copyright (C) 2024 BlueRock Security, Inc.
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)

Require Import skylabs.elpi.extra.extra.

(** ** <<Unlocked>> *)
(**
Notation <<Unlocked>> computes the hidden body of module locked terms.

Example: <<Goal @C = Unlocked (@C).>> restates the unlocking lemma for
a module locked constant <<C>>.
*)

Module internal.
  Elpi Tactic Unlocked.tac.
  Elpi Accumulate File extra.Tactic.
  Elpi Accumulate lp:{{
    pred fatal i:term, i:string.
    fatal T Msg :-
      PP = coq.pp.box (coq.pp.hv 2) [
        coq.pp.str "Unlocked: ", coq.pp.str Msg, coq.pp.str ":", coq.pp.spc,
        {coq.term->pp T}
      ],
      coq.error.pp PP.

    pred show i:term.
    :if "DEBUG_UNLOCKED"
    show T :-
      PP = coq.pp.box (coq.pp.hv 2) [
        coq.pp.str "Unlocked:", coq.pp.spc,
        {coq.term->pp T},
      ],
      coq.say.pp PP,
      fail.
    show _.

    pred unlocked i:term, o:term.
    unlocked T Unlocked :- std.do! [
      Whence = "Unlocked",
      std.assert! (whd T [] HD Args) Whence,
      ( coq.env.global (const C) HD, coq.is_mlocked C _ Body _, !
      ; fatal HD "Expected module locked constant" ),
      std.assert! (unwind Body Args Unlocked) Whence,
      show Unlocked,
    ].

    :if "DEBUG_UNLOCKED"
    solve (goal _ _ _ _ [trm T] as G) _ :-
      PP = coq.pp.box (coq.pp.hv 2) [
        coq.pp.str "Unlocked (", {coq.term->pp T}, coq.pp.str ")", coq.pp.nl,
        {coq.goal->pp G},
      ],
      coq.say.pp PP,
      fail.
    solve (goal _ _ _ _ [trm T] as G) GL :- refine {unlocked T} G GL.
    solve _ _ :- coq.error "Usage: Unlocked.tac (def [arg ...])".
  }}.

  Section class.
    #[local] Set Typeclasses Unique Instances.
    #[local] Set Typeclasses Strict Resolution.
    Class Unlocked {A} (lhs : A) := rhs : A.
  End class.

  #[global] Hint Mode Unlocked - ! : typeclass_instances.
  #[global] Hint Opaque Unlocked : typeclass_instances.

  #[global] Hint Extern 0 (Unlocked ?T) =>
    elpi Unlocked.tac (T) : typeclass_instances.

  Module Notations.
    Notation Unlocked T := (_ :> (Unlocked T)) (only parsing).
  End Notations.
End internal.

Export internal.Notations.
