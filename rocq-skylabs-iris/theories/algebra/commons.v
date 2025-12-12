(*
 * Copyright (c) 2025 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import iris.algebra.excl.
Require Import iris.algebra.frac.
Require Import iris.algebra.numbers.
Require Import iris.algebra.lib.mono_nat.

Require Import iris.base_logic.lib.own.

Require Import bluerock.iris.extra.algebra.excl_auth.
Require Import bluerock.iris.extra.algebra.frac_auth.

(** A collection of commonly used CMRAs that should be available everywhere. *)

Module br.
  Module ghost.

    Class G (Σ : gFunctors) : Set := brG {

      excl_inG : inG Σ (exclR unitO)

    ; frac_inG : inG Σ fracR

    ; nat_inG : inG Σ natR
    ; mono_nat_inG : inG Σ mono_natR

    ; auth_nat_inG : inG Σ (authR natUR)

    ; excl_auth_unit_inG : inG Σ (excl_authR unitO)
    ; excl_auth_bool_inG : inG Σ (excl_authR boolO)
    ; excl_auth_nat_inG : inG Σ (excl_authR natO)
    ; excl_auth_N_inG : inG Σ (excl_authR NO)
    ; excl_auth_Z_inG : inG Σ (excl_authR ZO)

    ; frac_auth_agree_N_inG : inG Σ (frac_authR (agreeR NO))

    }.

    Definition Σ : gFunctors := #[

      GFunctor (exclR unitO)

    ; GFunctor fracR

    ; GFunctor natR
    ; GFunctor mono_natR

    ; GFunctor (authR natUR)

    ; GFunctor (excl_authR unitO)
    ; GFunctor (excl_authR boolO)
    ; GFunctor (excl_authR natO)
    ; GFunctor (excl_authR NO)
    ; GFunctor (excl_authR ZO)

    ; GFunctor (frac_authR (agreeR NO))

    ].

    #[global] Instance subG {Σ'} : subG Σ Σ' -> G Σ'.
    Proof. solve_inG. Qed.
  End ghost.
End br.
