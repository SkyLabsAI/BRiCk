(*
 * Copyright (C) 2024 BlueRock Security, Inc.
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)

From skylabs_tests.elpi.extra Extra Dependency "test.elpi" as test.
Require Import skylabs.elpi.extra.extra.

Elpi Program test lp:{{ }}.
Elpi Accumulate File extra.Program.
Elpi Accumulate File test.

Elpi Accumulate lp:{{
  pred fill-true i:term, o:term.
  fill-true _ {{ True }}.
}}.

Succeed Elpi Query lp:{{
  det (coq.copy-prod-context (x\ y\ fill-true x y) {{ forall x : nat, False }} T),
  check {{ forall x : nat, True }} T
}}.

Succeed Elpi Query lp:{{ std.assert-err! true (coq.error "unreachable") }}.
Fail Elpi Query lp:{{ std.assert-err! fail fail }}.

Succeed Elpi Query lp:{{ guard! true true }}.
Succeed Elpi Query lp:{{ guard! fail fail }}.
