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

Succeed Elpi Query lp:{{ det (bool.to_term tt T), check {{ true }} T }}.
Succeed Elpi Query lp:{{ det (bool.to_term ff T), check {{ false }} T }}.
