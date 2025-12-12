(*
 * Copyright (c) 2020-2022 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import iris.algebra.ofe.
Require Export bluerock.prelude.wrap.

Canonical Structure WrapNO {SI:sidx} {Phant} := leibnizO (WrapN Phant).
