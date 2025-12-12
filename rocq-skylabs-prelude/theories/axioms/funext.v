(*
 * Copyright (c) 2022 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(*
Re-export functional extensionality axiom; this is a well-understood consistent
extension of Rocq.
*)

Require Export Stdlib.Logic.FunctionalExtensionality.
Require Import bluerock.prelude.base.

Ltac funext := apply: functional_extensionality.
Ltac funext_dep := apply: functional_extensionality_dep.

Lemma funext_equiv {A B C} (f : A -> B -> C) a1 a2 :
  (f a1 = f a2) <-> ∀ b : B, f a1 b = f a2 b.
Proof.
  split. by move->.
  move=>?. by funext.
Qed.
