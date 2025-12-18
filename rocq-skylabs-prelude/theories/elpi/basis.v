(*
 * Copyright (C) 2022-2023 BlueRock Security, Inc.
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)

Require Import elpi.elpi.

(*Export this tactic to [typeclass] use sites.*)
Ltac try_typeclasses_eauto := try typeclasses eauto.

Elpi File skylabs.typeclass.elpi lp:{{

  %% typeclass Db Grafting Done Typeclass Bo
  %% Solve for Bo in (Bo : Typeclass), accumulating Done into Db at Grafting if successful.
  pred typeclass i:string, i:grafting, i:prop, i:term, o:term.
    typeclass Db Grafting Done Typeclass Bo :- std.do! [
      std.assert-ok! (coq.typecheck {{ lp:Bo : lp:Typeclass }} _) "[typeclass] typechecking an instance failed",
      coq.ltac.collect-goals Bo [SealedGoal] [],
      coq.ltac.open (coq.ltac.call "try_typeclasses_eauto" []) SealedGoal [],
      coq.elpi.accumulate library Db (clause _ Grafting Done),
    ].
}}.

Elpi File skylabs.basis.elpi lp:{{

  %%% Option utilities

  pred option.app! i:option A, i:A -> prop.
  option.app! O F :- std.omap O (x\ _\ F x, !) _.

  %%% List utilities

  :index (1 1 1)
  pred list.map3 i:list A, i:list B, i:list C, i:(A -> B -> C -> D -> prop), o:list D.
  list.map3 [_|_] [] _ _ _ :- list.map3.aux.
  list.map3 [_|_] _ [] _ _ :- list.map3.aux.
  list.map3 [] [_|_] _ _ _ :- list.map3.aux.
  list.map3 _ [_|_] [] _ _ :- list.map3.aux.
  list.map3 [] _ [_|_] _ _ :- list.map3.aux.
  list.map3 _ [] [_|_] _ _ :- list.map3.aux.
  list.map3 [] [] [] _ [].
  list.map3 [A|AS] [B|BS] [C|CS] F [D|DS] :- F A B C D, list.map3 AS BS CS F DS.
  list.map3.aux :- coq.error "list.map3 lengths don't agree".

  pred list.app! i:list A, i:(pred i:A).
  list.app! L F :- std.map L (x\ _\ F x, !) _.

  pred list.app2! i:list A, i:list B, i:(pred i:A, i:B).
  list.app2! L1 L2 F :- std.map2 L1 L2 (x\ y\ _\ F x y, !) _.

  %%% Coq options

  /*
  [coq.do-with-option! Option Val Ps] runs [Ps] under Coq option
  [Option := Val], and then restores the option's original value.
  Panics if the option does not exist or is incompatible with [Val].
  */
  pred coq.with-option! i:list string, i:coq.option, i:list prop.
  coq.with-option! O V Ps :- std.do! [
    coq.option.get O W, !,
    coq.option.set O V,
    std.do! Ps,
    coq.option.set O W,
  ].

  /*
  [coq.with-option-unset! Option Ps] runs [Ps] with the Coq boolean
  option [Option] unset, and then restures the option's original
  value. Panics if the option does not exist or isn't boolean.
  */
  pred coq.with-option-unset! i:list string, i:list prop.
  coq.with-option-unset! O Ps :- coq.with-option! O (coq.option.bool ff) Ps.

  %%% Elaboration

  pred br.check-evar-free i:term, o:diagnostic.
  br.check-evar-free T D :- std.do! [
    coq.ltac.collect-goals T Goals Shelved,
    if (Goals = [], Shelved = []) (D = ok) (
      D = error {check-evar-free.msg T Goals Shelved}
    ),
  ].

  /*
  [check-evar-free.msg T Goals Shelved Msg] constructs a more or less
  readable error message [Msg] for a term [T] with uninstantiated
  EVars [Goals], [Shelved].
  */
  namespace check-evar-free {

    % A Coq name
    pred pp-name i:name, o:coq.pp.
    pp-name Name PP :- std.do! [
      PP = coq.pp.str {coq.name->id Name},
    ].

    % Any Elpi term
    pred pp-any i:any, o:coq.pp.
    pp-any Any PP :- std.do! [
      PP = coq.pp.str {term_to_string Any},
    ].

    % Any Elpi term (with marker "Oops!" meaning fix these pretty-printers)
    pred pp-oops i:any, o:coq.pp.
    pp-oops Any PP :- std.do! [
      PP = coq.pp.glue [
        coq.pp.str "Oops!", coq.pp.spc,
        {pp-any Any},
      ],
    ].

    % A context entry
    pred pp-goal-ctx-entry i:prop, o:coq.pp.
    pp-goal-ctx-entry (decl _ Name Ty) PP :- !, std.do! [
      pp-goal-ctx-entry.box [
        {pp-name Name}, coq.pp.str " :", coq.pp.spc,
        {coq.term->pp Ty},
      ] PP,
    ].
    pp-goal-ctx-entry (def _ Name Ty Body) PP :- !, std.do! [
      pp-goal-ctx-entry.box [
        {pp-name Name}, coq.pp.str " :", coq.pp.spc,
        {coq.term->pp Ty}, coq.pp.str " :=", coq.pp.spc,
        {coq.term->pp Body}
      ] PP,
    ].
    pp-goal-ctx-entry Entry PP :- std.do! [
      pp-goal-ctx-entry.box [
        {pp-oops Entry},
      ] PP,
    ].
    pred pp-goal-ctx-entry.box i:list coq.pp, o:coq.pp.
    pp-goal-ctx-entry.box PPs PP :- PP = coq.pp.box (coq.pp.hov 2) PPs.

    % A goal context
    pred pp-goal-ctx i:goal-ctx, o:coq.pp.
    pp-goal-ctx Ctx PP :- std.do! [
      /*
      Undocumented (but consistent with Coq contexts): The context is
      backwards.
      */
      std.rev Ctx Decls,
      Sep = coq.pp.glue [coq.pp.str ",", coq.pp.spc],
      std.intersperse Sep {std.map Decls pp-goal-ctx-entry} PPs,
      PP = coq.pp.box (coq.pp.hov 0) PPs,
    ].

    % An EVar
    pred pp-evar i:term, i:term, o:coq.pp.
    pp-evar EVar Ty PP :- std.do! [
      PP = coq.pp.glue [
        {coq.term->pp EVar}, coq.pp.str ": uninstantiated with type", coq.pp.spc,
        {coq.term->pp Ty},
      ],
    ].

    % A goal
    pred pp-goal i:goal, o:coq.pp.
    pp-goal (goal [] _Raw Ty Evar _Args) PP :- !, std.do! [
      pp-goal.box [
        {pp-evar Evar Ty},
      ] PP,
    ].
    pp-goal (goal Ctx _Raw Ty EVar _Args) PP :- !, Ctx => std.do! [
      pp-goal.box [
        {pp-evar EVar Ty}, coq.pp.spc,
        coq.pp.str "in context", coq.pp.brk 1 2,
        {pp-goal-ctx Ctx},
      ] PP,
    ].
    pp-goal Goal PP :- pp-goal.fallback Goal PP.

    pred pp-goal.box i:list coq.pp, o:coq.pp.
    pp-goal.box PPs PP :-
      PP = coq.pp.box (coq.pp.hov 2) [
        coq.pp.str "- ",
        coq.pp.glue PPs,
      ].

    pred pp-goal.fallback i:any, o:coq.pp.
    pp-goal.fallback ElpiTerm PP :- std.do! [
      pp-goal.box [
        {pp-oops ElpiTerm},
      ] PP,
    ].

    % A sealed goal
    pred pp-sealed-goal i:sealed-goal, o:coq.pp.
    pp-sealed-goal (nabla G) PP :- !, (pi x\ pp-sealed-goal (G x) PP).
    pp-sealed-goal (seal G) PP :- !, pp-goal G PP.
    pp-sealed-goal Sealed PP :- pp-goal.fallback Sealed PP.

    pred msg i:term, i:list sealed-goal, i:list sealed-goal, o:string.
    msg T Goals Shelved Msg :- std.do! [
      Brk = coq.pp.brk 0 0,
      PPT = coq.pp.box (coq.pp.v 2) [
        coq.pp.str "The following term contains unresolved evars:", Brk,
        {coq.term->pp T},
      ],
      std.map {std.append Goals Shelved} pp-sealed-goal PPG,
      std.intersperse Brk [PPT | [coq.pp.str "Specifically," | PPG]] PPs,
      coq.pp->string (coq.pp.box (coq.pp.v 0) PPs) Msg,
    ].

  }

  % Variant of [coq.elaborate-skeleton] that outputs evar-free terms on success.
  pred br.elaborate-skeleton i:term, o:term, o:term, o:diagnostic.
  br.elaborate-skeleton T ETy E D :- std.do-ok! D [
    coq.elaborate-skeleton T ETy E,
    br.check-evar-free ETy,
    br.check-evar-free E,
  ].

  % Variant of [coq.elaborate-ty-skeleton] that outputs an evar-free term on success.
  pred br.elaborate-ty-skeleton i:term, o:sort, o:term, o:diagnostic.
  br.elaborate-ty-skeleton T U E D :- std.do-ok! D [
    coq.elaborate-ty-skeleton T U E,
    br.check-evar-free E,
  ].

  %%% Terms tagged with phantom types

  /*
  See [typeabbrev bs] in ./elpi_bytestring.v for an example.
  */

  kind tm type -> type.
  type tm term -> tm A.

  pred tm->term i:tm A, o:term.
  tm->term (tm T) T.

  pred tm->string i:tm A, o:string.
  tm->string (tm T) S :- coq.term->string T S.

  %%% Debugging

  pred debug i:string, i:string, i:list any.
 :if "DEBUG"
  debug Prefix Msg L :-
    Prefix' is "DEBUG " ^ Prefix,
    coq.say Prefix' Msg L.
  debug _Prefix _Msg _L :- !.

  namespace skylabs {
    % get-indt VariantGR Indt: Indt is the body of Inductive type VariantGR.
    % Fails if VariantGR isn't a gref for an inductive, possibly wrapped in a
    % constant.
    pred get-indt i:gref, o:inductive.
    get-indt (indt Inductive) Inductive.
    get-indt (const C) Ind :- std.do! [
      coq.env.const C (some (global Def)) _,
      get-indt Def Ind
    ].

    % get-ctors VariantName Ctors: Ctors is the list of constructors of the Inductive
    % type VariantName. Fails if VariantName isn't an inductive.
    pred get-ctors i:string, o:list constructor.
    get-ctors VariantName Ctors :- std.do![
      coq.locate VariantName VariantGR,
      get-indt VariantGR VariantI,
      coq.env.indt VariantI _ _ _ _ Ctors _
    ].

    % Convenience function for extracting boolean Coq options
    pred get-boolopt i:string, o:bool.
    get-boolopt _ tt :- get-option "all" tt.
    get-boolopt Opt B :- get-option Opt B.
    get-boolopt _ ff :- !.

    pred elpi-list->list i:list term, o:term.
    elpi-list->list L EL :- std.do! [
      elpi-list->list.aux L L',
      std.assert-ok! (coq.elaborate-skeleton L' _ EL) "elpi-list->list: failed to typecheck",
    ].

    pred elpi-list->list.aux i:list term, o:term.
    elpi-list->list.aux [] {{ nil }}.
    elpi-list->list.aux (T :: Rest) {{ cons lp:T lp:Rest' }} :- elpi-list->list.aux Rest Rest'.

    pred list->elpi-list i:term, o:list term.
    list->elpi-list CoqList ElpiList :- std.do! [
      % Check that we actually have a [list A] - for some A
      std.assert-ok! (coq.elaborate-skeleton CoqList {{list _}} ElaboratedCoqList)
                     "[lst->elpi-list: failed to typecheck",

      % Do the conversion from Coq-list to elpi-list
      list->elpi-list.aux ElaboratedCoqList ElpiList,
    ].

    pred list->elpi-list.aux i:term, o:list term.
    list->elpi-list.aux {{nil}} [].
    list->elpi-list.aux {{cons lp:A lp:CoqAs}} (A :: ElpiAs) :-
      list->elpi-list.aux CoqAs ElpiAs.

    pred using-context i:(list string), i:prop.
    using-context [] P :- P.
    using-context [NM | CTX] P :-
      @using! NM => using-context CTX P.
  }
}}.
