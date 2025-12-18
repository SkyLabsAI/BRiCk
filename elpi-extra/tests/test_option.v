(*
 * Copyright (C) 2024 BlueRock Security, Inc.
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)

From skylabs_tests.elpi.extra Extra Dependency "test.elpi" as test.
Require Import Stdlib.NArith.BinNat.
Require Import skylabs.elpi.extra.extra.

Elpi Program test lp:{{ }}.
Elpi Accumulate File extra.Program.
Elpi Accumulate File test.

#[local] Open Scope N_scope.

Definition my_opt : option N := Some 42.

Fail Elpi Query lp:{{ option.of_term {{ true }} int.of_N O }}.
Succeed Elpi Query lp:{{ det (option.of_term {{ @None N }} int.of_N O), check none O }}.
Succeed Elpi Query lp:{{ det (option.of_term {{ my_opt }} int.of_N O), check (some 42) O }}.

Fail Elpi Query lp:{{ option.as_term (some (-1)) {{ N }} int.as_N T }}.
Succeed Elpi Query lp:{{ det (option.as_term none {{ N }} int.as_N T), check {{ @None N }} T }}.
Succeed Elpi Query lp:{{ det (option.as_term (some 3) {{ N }} int.as_N T), check {{ Some 3 }} T }}.

Fail Elpi Query lp:{{ option.of_term {{ my_opt }} badof-fail O }}.
Succeed Elpi Query lp:{{ det (option.of_term {{ my_opt }} badof-nondet O), check (some 1) O }}.

Fail Elpi Query lp:{{ option.as_term (some 1) {{ N }} badas-fail T }}.
Succeed Elpi Query lp:{{ det (option.as_term (some 42) {{ N }} badas-nondet T), check {{ Some 1 }} T }}.
