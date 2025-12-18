(*
 * Copyright (C) 2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

Require Export skylabs.elpi.extra.prelude.

(** [Elpi.Db.AddPred] is a vernacular command that can be used to declare a new
    predicate in an existing elpi database. See [usage] below for instructions
    and examples. 

    Elpi 1.20 and onwards require predicates to be declared before clauses for
    it are accumulated. 
*)

Elpi Command AddPred.

Elpi Accumulate lp:{{
  usage :- coq.error
"Elpi AddPred database predicate_name \"<Mode1>:<Type1>\" .. \"<ModeN>:<TypeN>\".

Example: Elpi AddPred my.db my.predicate \"i:(list string)\" \"o:prop\".
".

  pred parse-mode i:string o:argument_mode.
  parse-mode "i" in :- !.
  parse-mode "o" out :- !.
  parse-mode _ _ :- usage.

  pred parse-string i:(list argument) o:(string -> list argument -> prop).
  parse-string [str S|Args] K :- !, K S Args.
  parse-string _ _ :- usage.

  pred parse-sig i:(list argument) o:(list (pair argument_mode string) -> list argument -> prop).
  parse-sig [str S|Args] K :- !, std.do! [
    rex.split ":" S L,
    (L = [PreMode,Type], !; usage),
    parse-mode PreMode Mode,
    parse-sig Args Sig \ Args \
    K [pr Mode Type|Sig] Args
  ].
  parse-sig [] K :- !, K [] [].
  parse-sig _ _ :- usage.

  main Args :- std.do![
    parse-string Args Db \ Args \
    parse-string Args Pred \ Args \
    parse-sig Args Sig \ Args \ std.do! [
      (Args = [], !; usage), 
      std.assert! (@global! => coq.elpi.add-predicate Db _ Pred Sig) "Elpi.Db.AddPred"
    ]
  ].
}}.

