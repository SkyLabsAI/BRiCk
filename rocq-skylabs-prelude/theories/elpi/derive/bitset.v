(*
 * Copyright (c) 2023 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import elpi.elpi.
Require Export bluerock.prelude.elpi.derive.common.

Require Import bluerock.prelude.prelude.
Require Import bluerock.prelude.elpi.basis.
Require Export bluerock.prelude.elpi.derive.finite_type.

(***************************************************
 Bitsets
 - [[ #[only(bitset)] derive VariantType ]]
   Assembles pieces from finite.v to expose `to_bits`, together with laws, on [gset VariantType].
   The encoding into bit indices is derived automatically from the order of constructors of `VariantType`
   (0 for the first constructor, 1 for the second, etc.).
   Add an instance of `ToBit` to override the default behavior.
 ***************************************************)
Class ToBit (T : Type) (to_bit : T -> N) : Prop := {}.
#[global] Hint Mode ToBit + - : typeclass_instances.

Elpi Db derive.bitset.db lp:{{
  pred finite-type-done o:gref.
  pred bitset-done o:gref.
}}.
Elpi Accumulate derive lp:{{
  namespace derive.bitset {
    pred mk-simple-bitset i:string, i:gref, i:gref.
    mk-simple-bitset Prefix TyGR OrigGR :- std.do! [
      derive.finite_type.mk-finite-prelim Prefix TyGR OrigGR,
      coq.env.include-module-type {coq.locate-module-type "simple_finite_bitmask_type_mixin"} coq.inline.default,
      coq.env.end-module MP,

      %TODO: at this point, remove the `TypeName_finite` instance, etc.
      %But coq-elpi doesn't seem to have an API for Remove Hints
      %(cf. https://bedrocksystems.atlassian.net/browse/FM-3019).

      %Module Prefix_set := simple_finite_bits TyGR.
      ModName is Prefix ^ "_set",
      coq.env.apply-module-functor ModName none {coq.locate-module "simple_finite_bits"} [MP] coq.inline.default _,
    ].

    pred mk-bitset i:string, i:gref, i:gref, i:term.
    mk-bitset Prefix TyGR OrigGR ToBit :- std.do! [
      derive.finite_type.mk-finite-prelim Prefix TyGR OrigGR,

      % locating "t" seems like a very bad idea. We could find literally anything if something goes wrong.
      coq.locate "t" GRTy,
      Ty is global GRTy,
      coq.env.add-const "to_bit" ToBit {{ lp:Ty -> N }} @transparent! CToBit_,

      coq.env.include-module-type {coq.locate-module-type "finite_bitmask_type_mixin"} coq.inline.default,
      coq.env.end-module MP,

      ModName is Prefix ^ "_set",
      coq.env.apply-module-functor ModName none {coq.locate-module "finite_bits"} [MP] coq.inline.default _,
    ].
  }
}}.

Elpi Accumulate derive Db derive.finite_type.db.

#[phase="both"]
Elpi Accumulate derive lp:{{
  dep1 "bitset" "finite". %finite implies eq_dec
  dep1 "bitset_to_bit" "finite". %finite implies eq_dec
}}.

#[synterp] Elpi Accumulate derive lp:{{
  namespace derive.bitset {
    func main string, string, bool -> list prop.
    main TypeName _ UseToBit CL :- std.do! [
      coq.env.begin-module TypeName none,
      if (UseToBit is tt)
         (std.do! [
           coq.env.include-module-type {coq.locate-module-type "finite_bitmask_type_mixin"} coq.inline.default,
           coq.env.end-module MP,
           ModName is TypeName ^ "_set",
           coq.env.apply-module-functor ModName none {coq.locate-module "finite_bits"} [MP] coq.inline.default _,
         ])
         (std.do! [
           coq.env.include-module-type {coq.locate-module-type "simple_finite_bitmask_type_mixin"} coq.inline.default,
           coq.env.end-module MP,
           ModName is TypeName ^ "_set",
           coq.env.apply-module-functor ModName none {coq.locate-module "simple_finite_bits"} [MP] coq.inline.default _,
         ]),
      CL = [done TypeName],
    ].

    pred done i:string.
  }

  derivation T Prefix (derive "bitset" (derive.bitset.main T Prefix ff) (derive.bitset.done T)).
  derivation T Prefix (derive "bitset_to_bit" (derive.bitset.main T Prefix tt) (derive.bitset.done T)).
}}.

Elpi Accumulate derive.bitset.db File bluerock.typeclass.elpi.
#[superglobal] Elpi Accumulate derive.bitset.db lp:{{
  namespace derive.bitset {
    pred to-bits i:term, o:term.
    :name "to-bits.typeclass"
    to-bits T F :- typeclass "derive.bitset.db"  (before "to-bits.typeclass") (to-bits T F) {{ @ToBit lp:T lp:F }} Bo_.
  }
}}.

Elpi Accumulate derive Db derive.bitset.db.

Elpi Accumulate derive lp:{{
  namespace derive.finset {
    func main gref, string, bool -> list prop.
    main TyGR _Prefix UseToBit Clauses :-
      derive-original-gref TyGR OrigGR,
      coq.gref->id TyGR TypeName,
      if (UseToBit is tt)
        (std.do! [
          derive.bitset.to-bits (global TyGR) ToBit,
          derive.bitset.mk-bitset TypeName TyGR OrigGR ToBit,
        ])
        (derive.bitset.mk-simple-bitset TypeName TyGR OrigGR), !,
      Clauses = [bitset-done TyGR],
      std.forall Clauses (x\
        coq.elpi.accumulate _ "derive.bitset.db" (clause _ _ x)
      ).
    main _ _ _ _ :- usage.

    func usage.
    usage :- coq.error
"Usage: #[only(bitset)] derive T
where T is an inductive or a definition that unfolds to an inductive.

Assembles pieces from finite.v to expose `to_bits`, together with laws, on [gset VariantType].
The encoding into bit indices is derived automatically from the order of constructors of `VariantType`
(0 for the first constructor, 1 for the second, etc.).
Add an instance of `ToBit` and use #[only(bitset_to_bit)] instead to override the default behavior.
".
  }

  derivation
    (indt T) Prefix tt
    (derive "bitset"
      (derive.finset.main (indt T) Prefix ff)
      (bitset-done (indt T))
    ).

  derivation
    (indt T) Prefix tt
    (derive "bitset_to_bit"
      (derive.finset.main (indt T) Prefix tt)
      (bitset-done (indt T))
    ).

}}.
