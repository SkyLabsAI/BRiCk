(*
 * Copyright (C) 2024 BlueRock Security, Inc.
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)

Require Import skylabs.elpi.extra.extra.

Elpi Command LocateAll.
#[synterp] Elpi Accumulate lp:{{
  main-synterp [str S, int _, int _] L :- coq.locate-all S L.
  main-synterp _ _.
}}.
#[interp] Elpi Accumulate lp:{{
  main-interp [str S, int WantS, int WantI] LS :-
    coq.locate-all S LI, std.length LS HaveS, std.length LI HaveI,
    (WantS = HaveS, WantI = HaveI, !,
      (coq.say "synterp found" HaveS "items:" LS "
interp found" HaveI "items:" LI);
      (coq.say "synterp found" HaveS "items:" LS "
interp found" HaveI "items:" LI)).
  main-interp _ _ :- coq.error "usage: SynterpLocate ID WantS WantI".
}}.
Elpi Export LocateAll.

Module Type DOGS. End DOGS.
Module Dogs. End Dogs.
Definition cats := 34.
Notation bunnies := cats.	(* BUG: This abbreviation is _not_ locatable as such *)
Notation ferrets := (cats + cats).

(** Synterp can locate modules and module types *)
LocateAll DOGS 1 1.
LocateAll Dogs 1 1.

(** Synterp cannot locate globals and abbreviations *)
LocateAll cats 0 1.
LocateAll bunnies 0 1.	(* BUG: <<loc-gref>> not <<loc-abbreviation>> *)
LocateAll ferrets 0 1.	(* <<loc-abbreviation>> *)
