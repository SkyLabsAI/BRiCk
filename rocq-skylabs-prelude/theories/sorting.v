(*
 * Copyright (C) 2026 SkyLabs AI, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Export stdpp.sorting.
Require Export skylabs.prelude.base.

(** * Small extensions to [stdpp.sorting]. *)

Section merge_sort.
  Context {A} (R : relation A) `{∀ x y, Decision (R x y)}.
  #[local] Opaque merge_sort.

  (** Sorting with a total, transitive, antisymmetric relation gives a
  canonical representative of each permutation class. No [EqDecision A]
  or comparison function is required. *)
  #[global] Instance merge_sort_proper `{!Transitive R, !AntiSymm (=) R, !Total R} :
    Proper ((≡ₚ) ==> (=)) (merge_sort R).
  Proof.
    intros l1 l2 Hl.
    apply (StronglySorted_unique R);
      last by rewrite !merge_sort_Permutation.
    all: exact: StronglySorted_merge_sort.
  Qed.
End merge_sort.
