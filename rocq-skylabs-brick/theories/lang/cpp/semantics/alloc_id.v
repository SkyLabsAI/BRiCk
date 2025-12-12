(*
 * Copyright (c) 2020-2025 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bluerock.prelude.base.

(** ** Allocation IDs.
    We use them to model pointer provenance, following Cerberus.
 *)
Record alloc_id := MkAllocId { alloc_id_car : N }.

#[global] Instance MkAllocId_inj : Inj (=) (=) MkAllocId.
Proof. by intros ?? [=]. Qed.
#[global] Instance alloc_id_eq_dec : EqDecision alloc_id.
Proof. solve_decision. Qed.
#[global] Instance alloc_id_countable : Countable alloc_id.
Proof. by apply: (inj_countable' alloc_id_car MkAllocId) => -[?]. Qed.
