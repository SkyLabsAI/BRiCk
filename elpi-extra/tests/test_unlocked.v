(*
 * Copyright (C) 2024 BlueRock Security, Inc.
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)

Require Import skylabs.elpi.extra.unlocked.

Module locked_nat.
  Axiom body : nat.
  Axiom unlock : body = 1.
End locked_nat.

Goal Unlocked locked_nat.body = 1.
Proof. reflexivity. Qed.

Goal locked_nat.body = Unlocked locked_nat.body.
Proof. exact locked_nat.unlock. Qed.
