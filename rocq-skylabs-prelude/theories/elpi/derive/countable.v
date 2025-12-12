(*
 * Copyright (c) 2023 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import ssreflect.

Require Import stdpp.countable.

Require Import elpi.elpi.
Require Export bluerock.prelude.elpi.derive.common.
Require Export bluerock.prelude.elpi.derive.eq_dec.

Require Import bluerock.prelude.elpi.basis.

Elpi Accumulate derive File bluerock.basis.elpi.

(***************************************************
 Countable
 ***************************************************)
Elpi Db derive.stdpp.countable.db lp:{{
  pred countable o:gref, o:gref.
  pred countable-done o:gref.
}}.
Elpi Accumulate derive.stdpp.countable.db File bluerock.typeclass.elpi.
#[superglobal] Elpi Accumulate derive.stdpp.countable.db lp:{{

  :name "countable-done.typeclass"
  countable-done GR :-
    typeclass "derive.stdpp.countable.db"
      (before "countable-done.typeclass") (countable-done GR) {{ @Countable lp:{{global GR}} _ }} Bo_.
}}.

Elpi Accumulate derive Db derive.stdpp.countable.db.

(** This Gallina function is used at code generation time (not at runtime) to produce the
    positive associated to a particular value [a : T], given the list of all constructors [l : list T]. *)
#[local] Fixpoint lookup_from_ctorlist `{EqDecision T} (p : positive) (l : list T) (a : T) : positive :=
  match l with
  | [] => p
  | a' :: l' => if bool_decide (a = a') then p else lookup_from_ctorlist (p + 1)%positive l' a
  end.

(** TODO: This generic decoding function is used in generated [Countable] instances but isn't efficient.
    It would be better to replace it by a table that's built at code generation time. *)
#[local] Fixpoint decode_from_encode `{EqDecision T} (encode : T -> positive) (l : list T) (x : positive) : option T :=
  match l with
  | [] => None
  | a :: l' => if bool_decide (encode a = x) then Some a else decode_from_encode encode l' x
  end.

(** This needs to be exported for use by callers of Deriving but shouldn't be otherwise used outside this module.*)
Ltac derive_solve_countable := by case. (** TODO: [abstract] *)

Elpi File derive.countable.elpi lp:{{
  namespace derive.countable {
    /*
    [mk-countable CtorList Name T] assumes that type [T] has
    constructors [CtorList] and generates a global instance [Name : Countable T].
    */
    pred ctor-to-positive i:term, i:term, o:term.
    ctor-to-positive CtorList K Pos :- std.do! [
      T = {{ @lookup_from_ctorlist _ _ 1%positive lp:CtorList lp:K }},
      std.assert-ok! (coq.elaborate-skeleton T _ EPos) "asdfasdf",
      coq.reduction.vm.norm EPos _ Pos,
    ].

    pred rty i:term, i:term, i:list term, i:list term, o:term.
    rty RTy _ _ _ RTy.

    pred to-positive-branch i:term, i:term, i:term, i:list term, i:list term, o:term.
    to-positive-branch CtorList K _Kty _Vars _VarsTys PosEncoding :- std.do![
      ctor-to-positive CtorList K PosEncoding
    ].

    pred to-positive i:term, i:term, i:term, i:term, o:term.
    to-positive CtorList S Ty RTy Match :-
      coq.build-match S Ty (rty RTy) (to-positive-branch CtorList) Match.

    func mk-countable list term, string, gref, gref -> constant.
    mk-countable Ctors Name VariantGR OrigGR C :- std.do![
      bluerock.elpi-list->list Ctors CtorList,
      std.assert-ok! (coq.elaborate-skeleton CtorList _ ECtorList) "[mk-countable] failed to elaborate ctors",
      VariantTy = global VariantGR,
      Encode = {{ fun (x : lp:VariantTy) => lp:{{ { to-positive ECtorList {{ x }} VariantTy {{ positive }} } }} }},
      Decode = {{ @decode_from_encode lp:VariantTy _ lp:Encode lp:CtorList }},
      Lem = {{ forall x : lp:VariantTy, lp:Decode (lp:Encode x) = Some x }},
      std.assert-ok! (coq.elaborate-skeleton Lem _ ELem) "[mk-countable] failed to elaborate lem",
      std.assert-ok! (coq.typecheck {{ lp:Bo : lp:ELem }} _) "[mk-countable] failed to typecheck lem",
      coq.ltac.collect-goals Bo [SealedGoal] [],
      coq.ltac.open (coq.ltac.call "derive_solve_countable" []) SealedGoal [],
      eqdec OrigGR GrEqdec,
      EqDec = global GrEqdec,
      Inst = {{ @Build_Countable lp:VariantTy lp:EqDec lp:Encode lp:Decode lp:Bo }},
      std.assert-ok!
        (coq.elaborate-skeleton Inst _ EInst)
        "[mk-countable] failed to elaborate instance",
      coq.env.add-const Name EInst {{ @Countable lp:{{global OrigGR}} lp:EqDec }} ff C,
      @global! => coq.TC.declare-instance (const C) 0, %%TODO: previously level 5; was there a reason?
    ].
  }
}}.

#[phase="both"] Elpi Accumulate derive lp:{{
  dep1 "countable" "eq_dec".
}}.

#[synterp] Elpi Accumulate derive lp:{{
  derivation _ _ (derive "countable" (cl\ cl = []) true).
}}.

Elpi Accumulate derive File derive.countable.elpi.
Elpi Accumulate derive lp:{{
  namespace derive.countable {
    func main gref, string -> list prop.
    main TyGR Prefix Clauses :-
      bluerock.get-indt TyGR VariantI,
      derive-original-gref TyGR OrigGR, !,
      coq.env.indt VariantI _ _ _ _ Ctors _,
      std.map Ctors (c\ c'\ c' = global (indc c)) CTerms,
      CountableName is Prefix ^ "countable",
      derive.countable.mk-countable CTerms CountableName TyGR OrigGR C,
      Clauses = [countable-done TyGR, countable TyGR (const C)],
      std.forall Clauses (x\
        coq.elpi.accumulate _ "derive.stdpp.countable.db" (clause _ _ x)
      ).
    main _ _ _ :- usage.

    func usage.
    usage :- coq.error
"Usage: #[only(countable)] derive T
where T is an inductive or a definition that unfolds to an inductive.

Example #1:
 Variant T := A | B | C.
 #[only(countable)] derive T

Example #2:
  #[only(countable)] derive
  Variant T := A | B | C.

Example #3:
  Variant _T := A | B | C.
  Definition T := _T.
  #[only(countable)] derive T.".

  }

  derivation
    (indt T) Prefix ff
    (derive "countable"
      (derive.countable.main (indt T) Prefix)
      (countable-done (indt T))
    ).
}}.
