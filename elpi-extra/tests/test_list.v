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

Import ListNotations.

#[local] Open Scope N_scope.
#[local] Open Scope list_scope.

Definition my_list : list N := [4; 5; 6].

Fail Elpi Query lp:{{ list.of_term {{ true }} int.of_N L }}.
Succeed Elpi Query lp:{{ det (list.of_term {{ @nil N }} int.of_N L), check [] L }}.
Succeed Elpi Query lp:{{ det (list.of_term {{ my_list }} int.of_N L), check [4, 5, 6] L }}.

Fail Elpi Query lp:{{ list.as_term [-1] {{ N }} int.as_N T }}.
Succeed Elpi Query lp:{{ det (list.as_term [] {{ N }} int.as_N T), check {{ @nil N }} T }}.
Succeed Elpi Query lp:{{ det (list.as_term [1, 2, 3] {{ N }} int.as_N T), check {{ [1; 2; 3] }} T }}.

Fail Elpi Query lp:{{ list.of_term {{ my_list }} badof-fail L }}.
Succeed Elpi Query lp:{{ det (list.of_term {{ my_list }} badof-nondet L), check [1, 1, 1] L }}.

Fail Elpi Query lp:{{ list.as_term [1] {{ N }} badas-fail T }}.
Succeed Elpi Query lp:{{ det (list.as_term [42] {{ N }} badas-nondet T), check {{ [1] }} T }}.
