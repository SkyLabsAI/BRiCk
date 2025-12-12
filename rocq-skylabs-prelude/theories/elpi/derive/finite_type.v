(*
 * Copyright (c) 2023 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import stdpp.finite.

Require Import elpi.elpi.
Require Export bluerock.prelude.elpi.derive.common.
Require Export bluerock.prelude.elpi.derive.eq_dec.
Require Export bluerock.prelude.elpi.derive.finite.

Require Import bluerock.prelude.elpi.basis.
Elpi Accumulate derive File bluerock.basis.elpi.

(***************************************************
 Finite Types
 - [[ #[only(finite_type)] derive VariantType ]]
   Assembles pieces from finite.v to expose `to_N` and `of_N` functions on `VariantType`, together with laws.
   The encoding into `N` is derived automatically from the order of constructors of `VariantType`.
   Use an instance of `ToN` to override the default behavior.
 ***************************************************)
Class ToN (T : Type) (to_N : T -> N) : Prop := {}.
#[global] Hint Mode ToN + - : typeclass_instances.

Elpi Db derive.finite_type.db lp:{{
  pred finite-type-done o:gref.
  pred bitset-done o:gref.
}}.

Elpi File derive.finite_type.elpi lp:{{
  namespace derive.finite_type {
    pred mk-finite-prelim i:string, i:gref, i:gref.
    mk-finite-prelim TypeName TyGR OrigGR :- std.do! [
      %TODO: I'd like to be able to do a transparent ascription here, but
      %it doesn't seem like coq-elpi supports this (the following gives opaque ascription):
      %coq.locate-module-type "simple_finite_bitmask_type_intf" MTP,
      coq.env.begin-module TypeName none,

      coq.env.add-const "t" (global TyGR) _ @transparent! C,
      Ty = global (const C),

      eqdec OrigGR GrEqdec,
      std.assert-ok! (coq.elaborate-skeleton {{ EqDecision lp:{{ Ty }} }} _ ETyEqdec) "mk-finite-prelim: failed to check eq_dec",
      coq.env.add-const "t_eq_dec" (global GrEqdec) ETyEqdec @transparent! Ceq_dec,
      @global! => coq.TC.declare-instance (const Ceq_dec) 0,

      finite OrigGR GrFin,
      std.assert-ok! (coq.elaborate-skeleton {{ Finite lp:{{ Ty }} }} _ ETyFin) "mk-finite-prelim: failed to check finite",
      coq.env.add-const "t_finite" (global GrFin) ETyFin @transparent! Cfin,
      @global! => coq.TC.declare-instance (const Cfin) 0,
    ].

    func mk-simple-finite string, gref, gref.
    mk-simple-finite TypeName TyGR OrigGR :- std.do! [
      mk-finite-prelim TypeName TyGR OrigGR,
      coq.env.include-module-type {coq.locate-module-type "finite_type_mixin"} coq.inline.default,
      coq.env.end-module MP_,
    ].

    pred mk-finite i:string, i:gref, i:gref, i:term.
    mk-finite TypeName TyGR OrigGR ToN :- std.do! [
      mk-finite-prelim TypeName TyGR OrigGR,

      coq.locate "t" GRTy,
      Ty is global GRTy,
      coq.env.add-const "to_N" ToN {{ lp:Ty -> N }} @transparent! CtoN_,

      coq.env.include-module-type {coq.locate-module-type "finite_encoded_type_mixin"} coq.inline.default,
      coq.env.end-module MP_,
    ].
  }
}}.

Elpi Accumulate derive File derive.finite_type.elpi.
Elpi Accumulate derive.finite_type.db File bluerock.typeclass.elpi.
#[superglobal] Elpi Accumulate derive.finite_type.db lp:{{
  namespace derive.finite_type {
    pred to-N i:term, o:term.
    :name "to-N.typeclass"
    to-N T F :- typeclass "derive.finite_type.db"  (before "to-N.typeclass") (to-N T F) {{ @ToN lp:T lp:F }} Bo_.
  }
}}.


#[phase="both"] Elpi Accumulate derive lp:{{
  dep1 "finite_type" "finite". %finite implies eq_dec
  dep1 "finite_type_to_N" "finite". %finite implies eq_dec
}}.

#[synterp] Elpi Accumulate derive lp:{{
  namespace derive.finite_type {
    func main string, string, bool -> list prop.
    main TypeName _ UseToN CL :- std.do! [
      coq.env.begin-module TypeName none,
      if (UseToN is tt)
         (coq.env.include-module-type {coq.locate-module-type "finite_encoded_type_mixin"} coq.inline.default)
         (coq.env.include-module-type {coq.locate-module-type "finite_type_mixin"} coq.inline.default),
      coq.env.end-module MP_,
      CL = [done TypeName]
    ].

    pred done i:string.
  }

  derivation T Prefix (derive "finite_type" (derive.finite_type.main T Prefix ff) (derive.finite_type.done T)).
  derivation T Prefix (derive "finite_type_to_N" (derive.finite_type.main T Prefix tt) (derive.finite_type.done T)).
}}.

Elpi Accumulate derive Db derive.finite_type.db.
Elpi Accumulate derive lp:{{
  namespace derive.finite_type {
    func main gref, string, bool -> list prop.
    main TyGR _Prefix UseToN Clauses :-
      coq.gref->id TyGR TypeName,
      derive-original-gref TyGR OrigGR, !,
      if (UseToN is tt)
         (std.do! [
           derive.finite_type.to-N (global TyGR) ToN,
           derive.finite_type.mk-finite TypeName TyGR OrigGR ToN,
         ])
         (derive.finite_type.mk-simple-finite TypeName TyGR OrigGR),
      Clauses = [finite-type-done OrigGR],
      std.forall Clauses (x\
        coq.elpi.accumulate _ "derive.finite_type.db" (clause _ _ x)
      ).
    main _ _ _ _ :- usage.

    func usage.
    usage :- coq.error
"Usage: #[only(finite_type)] derive T
where T is an inductive or a definition that unfolds to an inductive.

Assembles pieces from finite.v to expose `to_N` and `of_N` functions on `VariantType`, together with laws.
The encoding into `N` is derived automatically from the order of constructors of `VariantType`.
Use an instance of the typeclass `ToN` and #[only(finite_type_to_N)] instead to override the default behavior.
".
  }

  derivation
    (indt T) Prefix tt
    (derive "finite_type"
      (derive.finite_type.main (indt T) Prefix ff)
      (finite-type-done (indt T))
    ).

  derivation
    (indt T) Prefix tt
    (derive "finite_type_to_N"
      (derive.finite_type.main (indt T) Prefix tt)
      (finite-type-done (indt T))
    ).

}}.
