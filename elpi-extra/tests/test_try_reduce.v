(*
 * Copyright (C) 2024 BlueRock Security, Inc.
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)

From skylabs_tests.elpi.extra Extra Dependency "test.elpi" as test.
Require Import skylabs.elpi.extra.extra.

Definition redex : nat := 0.

Elpi Command test.
Elpi Accumulate File extra.Command.
Elpi Accumulate File test.

Succeed Elpi Query lp:{{
  det (coq.ltac.try-red {{ redex }} T diag.ok),
  check {{ 0 }} T
}}.

Succeed Elpi Query lp:{{
  det (coq.ltac.try-red {{ fun x : nat => x }} T diag.ok),
  check {{ fun x : nat => x }} T
}}.
