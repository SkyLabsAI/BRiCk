(*
 * Copyright (c) 2023 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import stdpp.decidable.

Require Import elpi.elpi.
Require Export bluerock.prelude.elpi.derive.common.

Require Import bluerock.prelude.elpi.basis.

Elpi Accumulate derive File bluerock.basis.elpi.

(***************************************************
 EqDecision
 ***************************************************)
(*For each supported derivation, two predicates:
   - [myderiv TyGR DerivGR] Maps [TyGR] to its generated derivation
   - [myderiv-done TyGR] We're done deriving [myderiv] for [TyGR].*)
Elpi Db derive.stdpp.eq_dec.db lp:{{
  pred eqdec o:gref, o:gref.
  pred eqdec-done o:gref.
}}.
#[superglobal] Elpi Accumulate derive.stdpp.eq_dec.db File bluerock.typeclass.elpi.
#[superglobal] Elpi Accumulate derive.stdpp.eq_dec.db lp:{{
  :name "eqdec-done.typeclass"
  eqdec-done GR :-
    typeclass "derive.stdpp.eq_dec.db" (before "eqdec-done.typeclass") (eqdec-done GR) {{ @EqDecision lp:{{global GR}} }} Bo_.
}}.
Elpi Accumulate derive Db derive.stdpp.eq_dec.db.

#[synterp] Elpi Accumulate derive lp:{{
  derivation _ _ (derive "eq_dec" (cl\ cl = []) true).
}}.

Elpi Accumulate derive lp:{{
  /* [derive.eqdec.main TyGR Prefix Clauses] creates a global instance
   * of type [EqDecision lp:{{global TyGR}}].
   * It works with any type supported by [solve_decision].
   *
   * Example of the generated Coq code:
   * | (* Inductive C : Set := FOO | BAR | BAZ. *)
   * | #[global] Instance C_eq_dec : EqDecision C. Proof. ... Defined.
   */
  namespace derive.eqdec {
    func main gref, string -> list prop.
    main TyGR Prefix Clauses :-
      InstanceName is Prefix ^ "eq_dec",
      derive-original-gref TyGR OrigGR, !,
      TyEqDecision = {{ EqDecision lp:{{global OrigGR}} }},
      std.assert-ok! (coq.elaborate-skeleton TyEqDecision _ ETyEqDecision) "[derive.eqdec] [TyEqDecision]",
      std.assert-ok! (coq.typecheck {{ lp:BoEqDecision : lp:ETyEqDecision }} _) "typechecking the [EqDecision t] instance failed",
      coq.ltac.collect-goals BoEqDecision [SealedGoal] [],
      coq.ltac.open (coq.ltac.call "solve_decision" []) SealedGoal [],
      coq.env.add-const InstanceName BoEqDecision ETyEqDecision @transparent! C,
      @global! => coq.TC.declare-instance (const C) 0,
      Clauses = [eqdec-done OrigGR, eqdec OrigGR (const C)],
      std.forall Clauses (x\
        coq.elpi.accumulate _ "derive.stdpp.eq_dec.db" (clause _ _ x)
      ).
    main _ _ _ :- usage.

    func usage.
    usage :- coq.error
"Usage: #[only(eq_dec)] derive T
where T is an inductive or a definition that unfolds to an inductive.

Example #1:
 Variant T := A | B | C.
 #[only(eq_dec)] derive T

Example #2:
  #[only(eq_dec)] derive
  Variant T := A | B | C.

Example #3:
  Variant _T := A | B | C.
  Definition T := _T.
  #[only(eq_dec)] derive T.".

  }

  derivation
    (indt T) Prefix ff                      % inputs
    (derive "eq_dec"                        % name (for dep1)
       (derive.eqdec.main (indt T) Prefix)  % code to run
       (eqdec-done (indt T))                % idempotency test
    ).
}}.
