(*
 * Copyright (C) 2024-2025 BlueRock Security, Inc.
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)

From skylabs_tests.elpi.extra Extra Dependency "test.elpi" as test.
Require Import Stdlib.NArith.BinNat.
Require Import Stdlib.ZArith.BinInt.
Require Import skylabs.elpi.extra.extra.

Elpi Program test lp:{{ }}.
Elpi Accumulate File extra.Program.
Elpi Accumulate File test.

Definition my_pair : N * Z := (1%N, (-1)%Z).

Fail Elpi Query lp:{{ pair.of_prod {{ true }} int.of_N int.of_Z _ }}.
Succeed Elpi Query lp:{{
  det (pair.of_prod {{ my_pair }} int.of_N int.of_Z P),
  check (pr 1 -1) P
}}.
Fail Elpi Query lp:{{ pair.of_prod {{ my_pair }} badof-fail int.of_Z _ }}.
Fail Elpi Query lp:{{ pair.of_prod {{ my_pair }} int.of_N badof-fail _ }}.

Fail Elpi Query lp:{{ pair.as_prod (pr -1 -1) {{ N }} {{ Z }} int.as_N int.as_Z _ }}.
Succeed Elpi Query lp:{{
  det (pair.as_prod (pr 1 -1) {{ N }} {{ Z }} int.as_N int.as_Z T),
  check {{ @pair N Z 1%N (-1)%Z }} T
}}.
Fail Elpi Query lp:{{ pair.as_prod (pr 1 -1) {{ N }} {{ Z }} badas-fail int.as_Z _ }}.
Fail Elpi Query lp:{{ pair.as_prod (pr 1 -1) {{ N }} {{ Z }} int.as_N badas-fail _ }}.
Elpi Query lp:{{
  det (pair.as_prod (pr 1 -1) {{ N }} {{ Z }} badas-nondet int.as_Z T),
  check {{ @pair N Z 1%N (-1)%Z }} T
}}.

Fail Elpi Query lp:{{ pair.as_prod_typecheck (pr -1 -1) int.as_N int.as_Z _ }}.
Succeed Elpi Query lp:{{
  det (pair.as_prod_typecheck (pr 1 -1) int.as_N int.as_Z T),
  check {{ @pair N Z 1%N (-1)%Z }} T
}}.
Fail Elpi Query lp:{{ pair.as_prod_typecheck (pr 1 -1) {{ N }} {{ Z }} badas-fail int.as_Z _ }}.
Fail Elpi Query lp:{{ pair.as_prod_typecheck (pr 1 -1) {{ N }} {{ Z }} int.as_N badas-fail _ }}.
Elpi Query lp:{{
  det (pair.as_prod_typecheck (pr 1 -1) badas-nondet int.as_Z T),
  check {{ @pair N Z 1%N (-1)%Z }} T
}}.
