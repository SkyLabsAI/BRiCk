(*
 * Copyright (C) 2021 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Export stdpp.propset.
 
(** * Small extensions to [stdpp.sets]. *)

Definition π_set {D : Type} {F : D -> Type} (P : forall d, propset (F d))
    : propset (forall d : D, F d) :=
  {[ p | forall d, (p d) ∈ (P d) ]}.

Lemma propset_singleton_equiv {A} (x : A) :
  {[ y | y = x ]} ≡ ({[ x ]} : propset A).
Proof. set_solver. Qed.
Lemma propset_singleton_equiv_unit {A} (x : A) :
  {[ e | ∃ _ : (), e = x ]} ≡@{propset A} {[ x ]}.
Proof. set_solver. Qed.
