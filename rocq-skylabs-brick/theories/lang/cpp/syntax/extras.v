(*
 * Copyright (c) 2024-2025 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bluerock.prelude.compare.
Require Import bluerock.lang.cpp.syntax.prelude.
Require Import bluerock.lang.cpp.syntax.core.
Require Import bluerock.lang.cpp.syntax.compare.

Definition by_tag_comparison {T} (f : T -> positive)
  : Comparison (fun a b => Pos.compare (f a) (f b)).
Proof.
  constructor; intros *; apply numbers.positive_comparison.
Qed.

Definition by_prim_tag_comparison {T} (f : T -> _)
  : Comparison (fun a b => PrimInt63.compare (f a) (f b)).
Proof. constructor; intros *; [ apply PString.char63_compare_antisym | eapply PString.char63_compare_trans ]. Qed.

Lemma by_prim_tag_leibniz : ∀ {T : Type} (f : T → _),
    (forall x y, match PrimInt63.compare (f x) (f y) with
            | Eq => x = y
            | _ => True
            end) →
    LeibnizComparison (λ a b : T, PrimInt63.compare (f a) (f b)).
Proof. intros. red. intros. specialize (H a b). rewrite H0 in H. done. Qed.

#[global] Instance function_qualifiers_comparison : Comparison function_qualifiers.compare.
Proof. apply by_prim_tag_comparison. Qed.

#[global] Instance function_qualifiers_leibniz_cmp : LeibnizComparison function_qualifiers.compare.
Proof. apply by_prim_tag_leibniz. compute. by destruct x, y; compute. Qed.

#[global] Instance function_quailfiers_eq_dec : EqDecision function_qualifiers.t :=
  LeibnizComparison.from_comparison.

#[global] Instance atomic_name__eq_dec : EqDecision (atomic_name_ type) :=
  LeibnizComparison.from_comparison.
