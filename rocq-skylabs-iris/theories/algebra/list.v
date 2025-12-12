(*
 * Copyright (C) 2023 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Export iris.algebra.list.

Section ofe.
  Context {SI : sidx} {A : ofe}.
  Implicit Types l k : list A.
  Lemma dist_Forall2 n l k : l ≡{n}≡ k ↔ Forall2 (≡{n}≡) l k.
  Proof. done. Qed.
End ofe.
