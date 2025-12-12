(*
 * Copyright (c) 2023 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import stdpp.finite.

Require Import elpi.elpi.
Require Export bluerock.prelude.elpi.derive.common.

Require Import bluerock.prelude.prelude.
Require Import bluerock.prelude.elpi.basis.

Elpi Accumulate derive File bluerock.basis.elpi.

(***************************************************
 Finite
 ***************************************************)
Elpi Db derive.stdpp.finite.db lp:{{
  pred finite o:gref, o:gref.
  pred finite-done o:gref.
}}.
Elpi Accumulate derive.stdpp.finite.db File bluerock.typeclass.elpi.
#[superglobal] Elpi Accumulate derive.stdpp.finite.db lp:{{
  :name "finite-done.typeclass"
  finite-done GR :-
    typeclass "derive.stdpp.finite.db"
      (before "finite-done.typeclass") (finite-done GR) {{ @Finite lp:{{global GR}} _ }} Bo_.

}}.
Elpi Accumulate derive Db derive.stdpp.finite.db.

Elpi File derive.finite.elpi lp:{{
  namespace derive.finite {
     /* We want to process
      * [Variant ResType : Set := A | B | C (_ : option bool) | D (_ : bool) (_ : bool).]
      * into [A :: B :: (C <$> enum (option bool)) ++ (D <$> enum bool <*> enum bool).]
      */
      /*
      * [mk-finite-constructor.aux Constructor ConstrType InputList ResType OutputTerm]
      * will return in [OutputTerm] the list
      * [(Constructor <$> enum _ <*> enum _) ++ InputList], passing as many
      * arguments to [Constructor] as needed.
      *
      * - [Constructor] must have type [ConstrType] = [A1 -> A2 -> ... -> An
      *   -> ResType] (where [n] can be 0).
      * [A1 ... An] are [Finite].
      * - [InputList] must have type [list ResType].
      */
      pred mk-finite-constructor.aux i:term, i:term, i:term, i:term, o:term.
      mk-finite-constructor.aux C {{ lp:{{ArgTy}} -> lp:{{ResType}} }} IL Ty OTm :- std.do! [
        std.assert-ok! (coq.elaborate-skeleton {{ lp:{{C}} <$> enum lp:{{ArgTy}} }} _ EC) "",
        mk-finite-constructor.aux EC {{ list lp:{{ResType}} }} IL Ty OTm
      ].

      mk-finite-constructor.aux C {{ list (lp:{{ArgTy}} -> lp:{{ResType}}) }} IL Ty OTm :- std.do! [
        std.assert-ok! (coq.elaborate-skeleton {{ lp:{{C}} <*> (enum lp:{{ArgTy}}) }} _ EC) "",
        mk-finite-constructor.aux EC {{list lp:{{ResType}} }} IL Ty OTm
      ].
      % Use "foo" instead of "foo ++ nil"
      mk-finite-constructor.aux C {{ list lp:{{ResTy}} }} {{ [] }} ResTy' C :-
        std.assert-ok! (coq.unify-leq ResTy ResTy') "".
      mk-finite-constructor.aux C {{ list lp:{{ResTy}} }} IL ResTy' {{ lp:{{C}} ++ lp:{{IL}} }} :-
        std.assert-ok! (coq.unify-leq ResTy ResTy') "".
      mk-finite-constructor.aux C ResTy IL ResTy' {{ lp:{{C}} :: lp:{{IL}} }} :-
        std.assert-ok! (coq.unify-leq ResTy ResTy') "".
      mk-finite-constructor.aux C ResTy IL ResTy' _foo :-
        coq.error "mk-finite-constructor.aux failed on C = " C ", ResTy =" ResTy ", IL =" IL ", ResTy' = " ResTy'.

      pred mk-finite-constructor i:term, i:term, i:term, o:term.
      mk-finite-constructor Ctor InputList ResType OutTm :- std.do! [
        std.assert-ok! (coq.elaborate-skeleton Ctor OTy ECtor) "[mk-finite-constructor] failed to elaborate ctor",
        mk-finite-constructor.aux ECtor OTy InputList ResType OutTm
      ].

      pred mk-finite-constructors i:list term, i: term, o:term.
      mk-finite-constructors L T EL :- std.do! [
        mk-finite-constructors.aux L T L',
        std.assert-ok! (coq.elaborate-skeleton L' {{list lp:{{T}}}} EL) "[mk-finite-constructors] failed to typecheck",
      ].

      pred mk-finite-constructors.aux i:list term, i:term, o:term.
      mk-finite-constructors.aux [] _ {{ nil }}.
      mk-finite-constructors.aux (Ctor :: RestCtors) T CtorsValues :- std.do! [
        mk-finite-constructors.aux RestCtors T RestValues,
        mk-finite-constructor Ctor RestValues T CtorsValues
      ].

      func mk-finite string, list term, gref, gref -> constant.
      mk-finite InstanceName Ctors VariantGR OrigGR C :- std.do![
        VariantTy = global VariantGR,
        OriginalTy = global OrigGR,
        derive.finite.mk-finite-constructors Ctors VariantTy CtorList,
        std.assert-ok! (coq.elaborate-skeleton CtorList _ ECtorList) "[mk-finite] failed to elaborate ctors",

        % The Finite instance must be transparent, but proof obligations must be Qed-opaque.
        % Since `abstract` is not supported (https://github.com/LPCIC/coq-elpi/issues/376),
        % we create separate goals by hand.

        std.assert-ok! (coq.elaborate-skeleton {{ NoDup lp:{{ECtorList}} }} _ ETyNoDup) "[mk-finite] [TyNoDup]",
        std.assert-ok! (coq.typecheck {{ lp:{{BoNoDup}} : lp:{{ETyNoDup}} }} _) "typechecking [NoDup] failed",
        coq.ltac.collect-goals BoNoDup [SealedGoalNoDup] [],
        % TODO AUTO (FM-2732) : Elpi disables vm_compute here
        coq.ltac.open (coq.ltac.call "solve_finite_nodup" []) SealedGoalNoDup [],
        @using! "Type" =>
        coq.env.add-const {calc (InstanceName ^ "_subproof_nodup")} BoNoDup ETyNoDup @opaque! CNoDup,

        std.assert-ok! (coq.elaborate-skeleton {{ ∀ x : lp:{{OriginalTy}}, x ∈ lp:{{ECtorList}} }} _ ETyElemOf) "[mk-finite] [TyElemOf]",
        std.assert-ok! (coq.typecheck {{ lp:{{BoElemOf}} : lp:{{ETyElemOf}} }} _) "typechecking [ElemOf] failed",
        coq.ltac.collect-goals BoElemOf [SealedGoalElemOf] [],
        % TODO AUTO (FM-2732) : Elpi disables vm_compute here
        coq.ltac.open (coq.ltac.call "solve_finite_total" []) SealedGoalElemOf [],
        @using! "Type" =>
        coq.env.add-const {calc (InstanceName ^ "_subproof_elem_of")} BoElemOf ETyElemOf @opaque! CElemOf,

        std.assert-ok! (coq.elaborate-skeleton {{ Finite lp:{{OriginalTy}} }} _ ETyFinite) "[mk-finite] [TyFinite]",
        std.assert-ok! (coq.elaborate-skeleton
        {{ @Build_Finite _ _ lp:{{ECtorList}}
            lp:{{ global (const CNoDup) }} lp:{{ global (const CElemOf) }}}}
        _ EFiniteBody) "[mk-finite] [TyFinite]",

        coq.env.add-const InstanceName EFiniteBody
        ETyFinite @transparent! C,
        @global! => coq.TC.declare-instance (const C) 0
      ].
  }
}}.

#[phase="both"] Elpi Accumulate derive lp:{{
  dep1 "finite" "eq_dec".
}}.

#[synterp] Elpi Accumulate derive lp:{{
  derivation _ _ (derive "finite" (cl\ cl = []) true).
}}.

Elpi Accumulate derive File derive.finite.elpi.
Elpi Accumulate derive lp:{{
  namespace derive.finite {
    func main gref, string -> list prop.
    main TyGR Prefix Clauses :-
      bluerock.get-indt TyGR VariantI,
      derive-original-gref TyGR OrigGR, !,
      coq.env.indt VariantI _ _ _ _ Ctors _,
      std.map Ctors (c\ c'\ c' = global (indc c)) CTerms,
      FiniteName is Prefix ^ "finite",
      derive.finite.mk-finite FiniteName CTerms TyGR OrigGR C,
      Clauses = [finite-done OrigGR, finite OrigGR (const C)],
      std.forall Clauses (x\
        coq.elpi.accumulate _ "derive.stdpp.finite.db" (clause _ _ x)
      ).
    main _ _ _ :- usage.

    func usage.
    usage :- coq.error
"Usage: #[only(finite)] derive T
where T is an inductive or a definition that unfolds to an inductive.

Example #1:
 Variant T := A | B | C.
 #[only(finite)] derive T

Example #2:
  #[only(finite)] derive
  Variant T := A | B | C.

Example #3:
  Variant _T := A | B | C.
  Definition T := _T.
  #[only(finite)] derive T.".

  }

  derivation
    (indt T) Prefix ff
    (derive "finite"
      (derive.finite.main (indt T) Prefix)
      (finite-done (indt T))
    ).
}}.
