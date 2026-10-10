Require Import skylabs.prelude.sorting.

#[local] Set Default Proof Using "Type*".

Section permutation_rewriting.
  Context {A} (R : relation A) `{∀ x y, Decision (R x y)}.
  Context `{!Transitive R, !AntiSymm (=) R, !Total R}.

  (** Rewriting a permutation under sorting uses the new instance, including
  for abstract types without an equality decision or a comparator. *)
  Example merge_sort_app_commute (l1 l2 : list A) :
    merge_sort R (l1 ++ l2) = merge_sort R (l2 ++ l1).
  Proof. by rewrite (comm (R := (≡ₚ)) app l1 l2). Qed.
End permutation_rewriting.
