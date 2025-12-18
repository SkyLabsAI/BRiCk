(*
 * Copyright (C) 2022-2024 BlueRock Security, Inc.
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)

Require Import skylabs.elpi.extra.extra.

(** Test Elpi attribute parsing *)

Elpi Command TestAttr.
Elpi Accumulate File extra.Command.

Fail Elpi Query lp:{{ attr.get-error E }}.	(** Not running *)
Fail Elpi Query lp:{{ attr.get-value V }}.	(** Not running *)
Fail Elpi Query lp:{{ attr.get-name N }}.	(** Not running *)
Fail Elpi Query lp:{{ attr.get-path P }}.	(** Not running *)
Fail Elpi Query lp:{{ attr.continue-parsing A F O }}.	(** Not running *)

Elpi Accumulate lp:{{

  % Defaults

  pred flage o:bool.	flage ff.
  pred flagb o:bool.	flagb ff.
  pred flags o:string.	flags "S".
  pred flagm o:option string.	flagm none.

  % Attribute parsers

  pred parse i:string, o:list prop.
  parse "e" [flage tt] :- attr.is-no-value.
  parse "b" [flagb B] :- attr.is-bool B.
  parse "s" [flags S] :- attr.is-nonempty-string S.
  parse "m" O :- attr.is-map parsem O.

  pred parsem i:string, o:list prop.
  parsem "v" [flagm (some S)] :- attr.is-string S.

  % Test harness

  kind val type.
  type val bool -> bool -> string -> option string -> val.

  pred have o:val.
  have (val E B S M) :- flage E, flagb B, flags S, flagm M.

  pred want i:int, o:val.
  want 0 (val ff ff "S" none).	% defaults
  want 1 (val tt tt "X" (some "Y")).	% some options
  want 2 (val ff ff "S2" none).	% shadowing
  want 3 (val ff ff "S" (some "V2")).	% shadowing

  main [int N] :-
    attr.parse (msg\ coq.error msg) parse _ Opts,
    Opts => std.do! [
      (want N Want; coq.error N "out of range"), have Have,
      if (Want = Have) true (coq.error "want" Want "have" Have),
    ].
  main _ :- coq.error "usage: TestAttr n".

}}.
Elpi Export TestAttr.

Fail #[e=cats] TestAttr -1.	(** expects no value *)
Fail #[b=cats] TestAttr -1.	(** expects boolean *)
Fail #[cats=dogs] TestAttr -1.	(** unexpected *)
Fail #[m(cats=dogs)] TestAttr -1.	(** unexpected *)

TestAttr 0.	(** test defaults *)
#[e, b, s="X", m(v=Y)] TestAttr 1.	(** test setting options *)
#[s="S1", s="S2"] TestAttr 2.	(** test shadowing: rightmost wins *)
#[m(v=V1), m(v=V2)] TestAttr 3.	(** test shadowing: rightmost wins *)
#[m(v=V1, v=V2)] TestAttr 3.	(** test shadowing: rightmost wins *)
#[m(v=V0), m(v=V1, v=V2)] TestAttr 3.	(** test shadowing: rightmost wins *)
#[m(v=V0, v=V1), m(v=V2)] TestAttr 3.	(** test shadowing: rightmost wins *)
