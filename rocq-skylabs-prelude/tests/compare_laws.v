Require Import skylabs.prelude.base.

(** A library can provide all core comparison classes using only [base]. *)
Module CoreInstances.
  #[local] Instance unit_compare : Compare unit := fun _ _ => Eq.
  #[local] Instance unit_comparison : Comparison (compare (A:=unit)).
  Proof. constructor; intros; done. Qed.
  #[local] Instance unit_leibniz : LeibnizComparison (compare (A:=unit)).
  Proof. intros [] []; done. Qed.
End CoreInstances.

Require Import skylabs.prelude.compare.

#[local] Set Default Proof Using "Type*".

Example closed_compare_simpl : compare 1%nat 2%nat = Lt.
Proof. simpl. lazymatch goal with |- Lt = Lt => reflexivity end. Qed.

Module QuotientOrder.
  (** Payloads are ignored: comparison equality is strictly coarser than [=]. *)
  #[local] Instance key_compare : Compare (Z * bool) := compare_on fst.
  #[local] Instance key_comparison : Comparison (compare (A:=Z * bool)) := _.

  Example equal_keys_distinct_values :
    compare.eq (0%Z, true) (0%Z, false) /\ (0%Z, true) <> (0%Z, false).
  Proof. split; [reflexivity | discriminate]. Qed.

  Example substitute_equivalent_key (x y z : Z * bool) (Hxy : compare.eq x y) :
    compare.le x z <-> compare.le y z.
  Proof. by rewrite Hxy. Qed.

  Example quotient_order_transitive (x y z : Z * bool) :
    compare.le x y -> compare.le y z -> compare.le x z.
  Proof. intros Hxy Hyz. by transitivity y. Qed.

  Example lists_with_equal_keys : compare.eq [(0%Z, true)] [(0%Z, false)].
  Proof. reflexivity. Qed.

  (** Neither lexicographic nor list comparison laws require Leibniz equality. *)
  Example product_comparison_laws :
    Comparison (compare (A:=(Z * bool) * (Z * bool))) := _.
  Example list_comparison_laws : Comparison (compare (A:=list (Z * bool))) := _.
  Example sum_comparison_laws : Comparison (compare (A:=((Z * bool) + (Z * bool))%type)) := _.
  Example option_comparison_laws : Comparison (compare (A:=option (Z * bool))) := _.
  Example strict_order_antisymmetry : AntiSymm (=) (compare.lt (A:=Z * bool)) := _.
End QuotientOrder.

Module LeibnizOrder.
  (** Common numeric and container instances work without extra declarations. *)
  Example unit_partial_order : PartialOrder (compare.le (A:=unit)) := _.
  Example boolean_partial_order : PartialOrder (compare.le (A:=bool)) := _.
  Example numeric_partial_order : PartialOrder (compare.le (A:=nat)) := _.
  Example numeric_sum_leibniz : LeibnizComparison (compare (A:=(nat + nat)%type)) := _.
  Example numeric_option_leibniz : LeibnizComparison (compare (A:=option nat)) := _.
  Example numeric_list_leibniz : LeibnizComparison (compare (A:=list nat)) := _.

  #[local] Instance comparison_list_decision : EqDecision (list nat) :=
    LeibnizComparison.from_compare.

  Example unequal_lists : bool_decide ([1; 2]%nat = [1; 3]%nat) = false.
  Proof. vm_compute. reflexivity. Qed.
  Example equal_lists : bool_decide ([1; 2]%nat = [1; 2]%nat) = true.
  Proof. vm_compute. reflexivity. Qed.
End LeibnizOrder.

Module OverrideComparison.
  #[local] Instance indiscrete_nat_compare : Compare nat := fun _ _ => Eq.
  #[local] Instance indiscrete_nat_comparison : Comparison (compare (A:=nat)).
  Proof. constructor; intros; done. Qed.

  (** Native laws must not be attached to a replacement operational instance. *)
  Example replacement_is_not_leibniz : True.
  Proof.
    assert_fails (assert (H : LeibnizComparison (compare (A:=nat)))
      by typeclasses eauto).
    exact I.
  Qed.
End OverrideComparison.

Module ComparatorInference.
  Inductive NoCompare := Foo | Bar.

  (** Missing instances must fail instead of inventing recursive lexicographic layers. *)
  Example missing_comparator : True.
  Proof.
    let cmp := open_constr:(_ : NoCompare -> NoCompare -> comparison) in
      assert_fails (assert (H : Comparison cmp) by typeclasses eauto);
      unify cmp (fun (_ _ : NoCompare) => Eq).
    let cmp := open_constr:(_ : NoCompare -> NoCompare -> comparison) in
      assert_fails (assert (H : LeibnizComparison cmp) by typeclasses eauto);
      unify cmp (fun (_ _ : NoCompare) => Eq).
    let cmp := open_constr:(_ : nat -> nat -> comparison) in
      assert_fails (assert (H : Comparison cmp) by typeclasses eauto);
      assert_fails (assert (H : LeibnizComparison cmp) by typeclasses eauto);
      unify cmp Nat.compare.
    exact I.
  Qed.

  Example inferred_numeric_factory : EqDecision nat := LeibnizComparison.from_compare.
  Example lexicographic_laws : Comparison (lex_compare (compare (A:=nat)) (compare (A:=nat))) := _.
  (** Leibniz equality of either pointwise component suffices. *)
  Example lexicographic_left :
    LeibnizComparison (lex_compare (compare (A:=nat)) (fun _ _ => Eq)) := _.
  Example lexicographic_right :
    LeibnizComparison (lex_compare (fun _ _ => Eq) (compare (A:=nat))) := _.
End ComparatorInference.
