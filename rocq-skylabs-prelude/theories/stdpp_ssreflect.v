(*
 * The following code is derived from code original to the
 * Iris project. That original code is
 *
 *	Copyright Iris developers and contributors
 *
 * and used according to the following license.
 *
 *	SPDX-License-Identifier: BSD-3-Clause
 *
 * Original Iris License:
 * https://gitlab.mpi-sws.org/iris/iris/-/blob/26ebf1eed7d99a02683996e1b06c5f28870bf0a0/LICENSE-CODE
 *)

(* Load both ssreflect and stdpp, using the same settings as Iris. *)
Require Export Stdlib.ssr.ssreflect.
Require Export stdpp.prelude.
#[global] Open Scope general_if_scope.
#[global] Set SsrOldRewriteGoalsOrder. (* See Coq issue #5706 *)
Ltac done := stdpp.tactics.done.

(** Iris itself and many dependencies still rely on this coercion. *)
Coercion Z.of_nat : nat >-> Z.

#[global] Hint Mode Equiv ! : typeclass_instances.
