(*
 * Copyright (C) 2024 BlueRock Security, Inc.
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)

From skylabs_tests.elpi.extra Extra Dependency "test.elpi" as test.
Require Import Stdlib.Lists.List.
Require Import Stdlib.NArith.BinNat.
Require Import skylabs.elpi.extra.extra.

Elpi Program test lp:{{ }}.
Elpi Accumulate File extra.Program.
Elpi Accumulate File test.

Elpi Accumulate lp:{{
  pred no_diag o:diag.	% Fails

  pred no_msg.msg o:string.	% Fails
  pred no_msg o:diag.
  no_msg (diag.error no_msg.msg).

  pred some_message o:diag.
  some_message (diag.error ((=) "Some message")).

  pred u.diag i:any, i:any, o:diag.
  u.diag A B diag.ok :- A = B, !.
  u.diag _ _ (diag.error ((=) "not equal")).

  pred u.diagnostic i:any, i:any, o:diagnostic.
  u.diagnostic A B ok :- A = B, !.
  u.diagnostic _ _ (error "not equal").
}}.

(* TODO: This should be a CRAM test. Output matters. *)

Fail Elpi Query lp:{{ diag.asserts! no_diag "Expect no diagnostic" }}.
Fail Elpi Query lp:{{ diag.asserts! no_msg "Expect no message" }}.
Fail Elpi Query lp:{{ diag.asserts! some_message "Expect some message" }}.

Elpi Query lp:{{ diag.asserts! (diag.lift! (u.diagnostic 1 1)) "test" }}.
Elpi Query lp:{{ std.assert-ok! (diag.lower! (u.diag 1 1)) "test" }}.

Fail Elpi Query lp:{{ diag.asserts! (diag.lift! (u.diagnostic 1 2)) "Expect not equal" }}.
Fail Elpi Query lp:{{ std.assert-ok! (diag.lower! (u.diag 1 2)) "Expect not equal" }}.
