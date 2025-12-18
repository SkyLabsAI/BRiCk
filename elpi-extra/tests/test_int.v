(*
 * Copyright (C) 2024 BlueRock Security, Inc.
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)

From skylabs_tests.elpi.extra Extra Dependency "test.elpi" as test.
Require Import Stdlib.Init.Byte.
Require Import Stdlib.PArith.BinPos.
Require Import Stdlib.NArith.BinNat.
Require Import Stdlib.ZArith.BinInt.
Require Import skylabs.elpi.extra.extra.

Elpi Program test lp:{{ }}.
Elpi Accumulate File extra.Program.
Elpi Accumulate File test.

Parameter opaque : N.
Definition numeral : N := 42.
Definition computable : N := numeral + numeral.
Definition noncomputable : N := numeral + opaque.

Succeed Elpi Query lp:{{ det (int.of_pos {{ 42%positive }} N), check 42 N }}.
Succeed Elpi Query lp:{{ det (int.of_N {{ 42%N }} N), check 42 N }}.
Succeed Elpi Query lp:{{ det (int.of_Z {{ 42%Z }} N), check 42 N }}.
Succeed Elpi Query lp:{{ det (int.of_Z {{ (-42)%Z }} N), check -42 N }}.

Succeed Elpi Query lp:{{ det (int.of_N {{ numeral }} N), check 42 N }}.
Succeed Elpi Query lp:{{ det (int.of_N {{ computable }} N), check 84 N }}.	(* Elpi TODO *)
Fail Elpi Query lp:{{ int.of_N {{ opaque_N }} N }}.
Fail Elpi Query lp:{{ int.of_N {{ noncomputable }} N }}.

Fail Elpi Query lp:{{ int.as_pos -1 T }}.
Fail Elpi Query lp:{{ int.as_pos 0 T }}.
Succeed Elpi Query lp:{{ det (int.as_pos 42 T), check {{ 42%positive }} T }}.

Fail Elpi Query lp:{{ int.as_N -1 T }}.
Succeed Elpi Query lp:{{ det (int.as_N 0 T), check {{ 0%N }} T }}.
Succeed Elpi Query lp:{{ det (int.as_N 42 T), check {{ 42%N }} T }}.

Succeed Elpi Query lp:{{ det (int.as_Z -3 T), check {{ (-3)%Z }} T }}.
Succeed Elpi Query lp:{{ det (int.as_Z 0 T), check {{ 0%Z }} T }}.
Succeed Elpi Query lp:{{ det (int.as_Z 42 T), check {{ 42%Z }} T }}.

Fail Elpi Query lp:{{ int.as_byte -1 T }}.
Succeed Elpi Query lp:{{ det (int.as_byte 0 T), check {{ Byte.x00 }} T }}.
Succeed Elpi Query lp:{{ det (int.as_byte 255 T), check {{ Byte.xff }} T }}.
Fail Elpi Query lp:{{ int.as_byte 256 T }}.

(** Term wrappers *)

Fail Elpi Query lp:{{ int.pos.of_term {{ true }} _ }}.
Elpi Query lp:{{
  det (int.pos.of_term {{ 42%positive }} N),
  det (int.pos.to_int N V),
  check 42 V
}}.
Elpi Query lp:{{
  det (int.pos.of_int 42 N),
  det (int.pos.to_term N T),
  check {{ 42%positive }} T
}}.

Fail Elpi Query lp:{{ int.N.of_term {{ true }} _ }}.
Elpi Query lp:{{
  det (int.N.of_term {{ 42%N }} N),
  det (int.N.to_int N V),
  check 42 V
}}.
Elpi Query lp:{{
  det (int.N.of_int 42 N),
  det (int.N.to_term N T),
  check {{ 42%N }} T
}}.

Fail Elpi Query lp:{{ int.Z.of_term {{ true }} _ }}.
Elpi Query lp:{{
  det (int.Z.of_term {{ 42%Z }} Z),
  det (int.Z.to_int Z V),
  check 42 V
}}.
Elpi Query lp:{{
  det (int.Z.of_int 42 Z),
  det (int.Z.to_term Z T),
  check {{ 42%Z }} T
}}.

Fail Elpi Query lp:{{ int.byte.of_term {{ true }} _ }}.
Elpi Query lp:{{
  det (int.byte.of_term {{ " "%byte }} B),
  det (int.byte.to_int B V),
  check 32 V
}}.
Elpi Query lp:{{
  det (int.byte.of_int 32 B),
  det (int.byte.to_term B T),
  check {{ " "%byte }} T
}}.
