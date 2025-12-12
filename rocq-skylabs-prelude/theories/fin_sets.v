(*
 * Copyright (C) 2020-2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Export stdpp.fin_sets.
Require Import bluerock.prelude.base.
Require Import bluerock.prelude.sets.
Require Import bluerock.prelude.list.
Require Import bluerock.prelude.list_numbers.

(** * Small extensions to [stdpp.fin_sets]. *)
#[local] Set Default Proof Using "Type*".

Section finset.
  Context `{FinSet A C}.
  Implicit Types X Y : C.

  Lemma set_not_elem_of x X `{Decision (x ∈ X)} : ¬ (x ∉ X) ↔ x ∈ X.
  Proof. apply dec_stable_iff. Qed.

  Lemma set_not_Forall (P : A -> Prop) `{Hdec : !∀ x, Decision (P x)} X :
    ¬ set_Forall P X <-> exists x, x ∈ X /\ ¬ P x.
  Proof.
    rewrite set_Forall_elements. split.
    - rewrite/Decision in Hdec. move=>/neg_Forall_Exists_neg-/(_ Hdec)/Exists_exists.
      intros (x & ?%elem_of_elements & ?). by exists x.
    - intros (x & ?%elem_of_elements & ?). move/Forall_forall. auto.
  Qed.

  (** Witnesses for non-disjoint finite sets *)
  Lemma set_not_disjoint X Y `{!∀ x, Decision (x ∈ Y)} :
    ¬ X ## Y <-> exists x, x ∈ X /\ x ∈ Y.
  Proof.
    rewrite set_disjoint_not_Forall_1 set_not_Forall.
    f_equiv=>x. by rewrite set_not_elem_of.
  Qed.

  (* The right-hand side computes nicely on closed goals (at least on [gset]. *)
  Lemma set_elem_of_bool_decide x X :
    x ∈ X <-> bool_decide (x ∈ elements X) = true.
  Proof. by rewrite -elem_of_elements bool_decide_eq_true. Qed.
  Lemma not_set_elem_of_bool_decide x X :
    x ∉ X <-> bool_decide (x ∈ elements X) = false.
  Proof. by rewrite set_elem_of_bool_decide; case_bool_decide. Qed.

  Section elements.
    #[global] Instance list_to_set_elements_cancel :
      Cancel (≡@{C}) list_to_set elements | 100 := list_to_set_elements.

    #[global] Instance elements_inj : Inj (≡) (=) (elements (C := C)) | 100.
    Proof. apply (cancel_inj (f := list_to_set)). Qed.

    Lemma elements_set_equiv_1 (x y : C) :
      elements x = elements y -> x ≡ y.
    Proof. by move /(inj elements _ _). Qed.

    #[global] Instance elements_mono :
      Proper (subseteq ==> subseteq) (elements (C := C)).
    Proof. move=>x y Heq. set_solver. Qed.

    #[global] Instance elements_perm :
      Proper (equiv ==> Permutation) (elements (C := C)) | 100.
    Proof. move=>x y Heq. set_solver. Qed.

    Section elements_leibniz.
      Context `{!LeibnizEquiv C}.

      Lemma elements_set_equiv_L (x y : C) :
        elements x = elements y <-> x = y.
      Proof.
        split; last by [move->].
        by move /(inj elements _ _) /(leibniz_equiv _ _).
      Qed.

      #[global] Instance list_to_set_elements_cancel_L :
        Cancel (=@{C}) list_to_set elements := list_to_set_elements_L.
      #[global] Instance elements_leibniz_inj :
        Inj (=) (=) (elements (C := C)) | 0.
      Proof. apply (cancel_inj (f := list_to_set)). Qed.
    End elements_leibniz.
  End elements.

  #[global] Instance list_to_set_mono :
    Proper (subseteq ==> subseteq) (list_to_set (C := C)).
  Proof. move=>x y Heq. set_solver. Qed.
  (* [Proper]ness of [list_to_set] wrt *)
  (* [list_to_set_perm] and [list_to_set_perm_L] already exists. *)

  (** [size] *)
  Lemma size_empty_iff_L `{!LeibnizEquiv C} X : size X = 0 ↔ X = ∅.
  Proof. unfold_leibniz. apply size_empty_iff. Qed.
End finset.

#[global] Instance : Params (@list_to_set) 5 := {}.

(** [set_seq] *)
Section set_seq.
  Lemma size_set_seq `{FinSet nat C} start len :
    size (set_seq (C:=C) start len) = len.
  Proof.
    revert start; induction len as [|n IH]=>start; csimpl.
    { by rewrite size_empty. }
    rewrite size_union.
    - by rewrite size_singleton IH.
    - rewrite disjoint_singleton_l elem_of_set_seq. lia.
  Qed.

  Lemma elements_set_seq `{FinSet nat C} start count :
    elements (C:=C) (set_seq start count) ≡ₚ seq start count.
  Proof.
    revert start. induction count as [|n IH]=>i; csimpl; first by rewrite elements_empty.
    rewrite elements_union_singleton; first by rewrite IH.
    generalize (set_seq_S_start_disjoint (C:=C) i n). by rewrite disjoint_singleton_l.
  Qed.
End set_seq.

(** The [set_map] operation *)

Section set_map_functorial.
  Context `{FinSet A SA}.

  Lemma set_map_id (X : SA) :
    set_map id X ≡ X.
  Proof. by rewrite /set_map list_fmap_id list_to_set_elements. Qed.

  Lemma set_map_id_L `{!LeibnizEquiv SA} (X : SA) :
    set_map id X = X.
  Proof. unfold_leibniz. by rewrite set_map_id. Qed.

  Section compose.
    Context `{FinSet B SB}.
    Context `{Set_ C SC}.

    Context (f : A -> B) `{!Inj eq eq f} (g : B -> C).

    Lemma set_map_compose (X : SA) :
      set_map (C := SB) (D := SC) g (set_map f X) ≡ set_map (g ∘ f) X.
    Proof.
      rewrite /set_map elements_list_to_set -?list_fmap_compose //.
      apply /NoDup_fmap /NoDup_elements.
    Qed.

    Lemma set_map_compose_L `{!LeibnizEquiv SC} (X : SA) :
      set_map (C := SB) (D := SC) g (set_map f X) = set_map (g ∘ f) X.
    Proof. unfold_leibniz. apply /set_map_compose. Qed.
  End compose.
End set_map_functorial.

Section set_map.
  Context `{FinSet A C, Set_ B D}.
  #[local] Notation set_map := (set_map (C := C) (D := D)).

  #[global] Instance set_map_inj (f : A -> B) `{!Inj eq eq f} :
    Inj (≡) (≡) (set_map f) | 50.
  Proof. rewrite /Inj. set_solver. Qed.

  #[global] Instance set_map_inj_L (f : A -> B) `{!Inj eq eq f}
    `{!LeibnizEquiv C, !LeibnizEquiv D} :
    Inj eq eq (set_map f).
  Proof. rewrite /Inj. set_solver. Qed.

  Lemma set_map_disjoint (f : A → B) (X Y : C) :
    (∀ x y, f x = f y → x ∈ X → y ∈ Y → False) →
    set_map f X ## set_map f Y.
  Proof. set_solver. Qed.
  Lemma set_map_disjoint_singleton_l (f : A → B) (x : A) (Y : C) :
    (∀ y, f x = f y → y ∉ Y) → {[f x]} ## set_map f Y.
  Proof. set_solver. Qed.
  Lemma set_map_disjoint_singleton_r (f : A → B) (x : A) (Y : C) :
    (∀ y, f x = f y → y ∉ Y) → set_map f Y ## {[f x]}.
  Proof. set_solver. Qed.

  Lemma set_map_ext (f g : A -> B) (X : C)
    (Hext : ∀ x, x ∈ X → f x = g x) :
    set_map f X =@{D} set_map g X.
  Proof.
    rewrite /set_map. f_equiv. apply list_fmap_ext.
    intros i x ?%elem_of_list_lookup_2. exact /Hext /elem_of_elements.
  Qed.
End set_map.

(* Note: this instance seems to not match [λ x, set_map f x]. *)
#[global] Instance set_map_cancel
    `{FinSet A SA} `{FinSet B SB} `{!LeibnizEquiv SB}
    (f : A -> B) (g : B -> A) `{!Cancel eq f g} :
  Cancel eq (set_map (C := SA) f) (set_map (C := SB) g).
Proof.
  intros X. have ? : Inj eq eq g by exact: cancel_inj.
  rewrite -{2}(set_map_id_L X) set_map_compose_L.
  (* setoid_rewrite (cancel right.of_nova right.to_nova). *)
  apply set_map_ext => x Hin. exact: cancel.
Qed.

Section set_map.
  Context `{FinSet A C, FinSet B D}.
  #[local] Notation set_map := (set_map (C := C) (D := D)).

  Lemma set_map_empty_iff (f : A -> B) X :
    set_map f X ≡ ∅ <-> X ≡ ∅.
  Proof.
    split; first last.
    - move=>->. by rewrite set_map_empty.
    - rewrite -!size_empty_iff.
      pattern X. apply set_ind; clear X; first by intros ?? ->.
      { by rewrite size_empty. }
      intros x X Hni IH.
      rewrite set_map_union set_map_singleton.
      rewrite (comm union) size_union_alt.
      intros Hsz.
      assert (size (set_map f X) = 0) as Hsz0 by lia.
      exfalso. move: Hsz. rewrite Hsz0 /=.
      have {Hsz0} IH := IH Hsz0; rewrite (size_empty_inv _ IH).
      by rewrite set_map_empty difference_empty size_singleton.
  Qed.

  Lemma set_map_empty_iff_L `{!LeibnizEquiv C, !LeibnizEquiv D}
      (f : A -> B) X :
    set_map f X = ∅ <-> X = ∅.
  Proof. unfold_leibniz. exact: set_map_empty_iff. Qed.

  Lemma set_map_nonempty_iff_L `{!LeibnizEquiv C, !LeibnizEquiv D}
    (f : A -> B) X :
    set_map f X <> ∅ <-> X <> ∅.
  Proof. by rewrite set_map_empty_iff_L. Qed.

  Lemma set_Forall_set_map `{!LeibnizEquiv C}
    (P : B -> Prop) (f : A -> B) X :
    set_Forall P (set_map f X) <-> set_Forall (P ∘ f) X.
  Proof.
    unfold set_map.
    rewrite -{2}(list_to_set_elements_L X).
    induction (elements X) as [| x X' IHX']; cbn; split; intros Hforall;
      try apply set_Forall_empty.
    all: pose (set_Forall_union_inv_1 _ _ _ Hforall).
    all: pose (set_Forall_union_inv_2 _ _ _ Hforall).
    all: rename select (set_Forall _ {[_]}) into Hsingleton.
    all: apply set_Forall_singleton in Hsingleton.
    all: apply set_Forall_union; intuition auto.
    all: by apply set_Forall_singleton.
  Qed.

  Lemma size_map_inj (f : A -> B) `{!Inj (=) (=) f} (X : C) :
    size (set_map f X) = size X.
  Proof.
    pattern X. apply set_ind; clear X.
    { by intros X1 X2 ->. }
    { by rewrite set_map_empty !size_empty. }
    intros x X Hx IH.
    rewrite set_map_union !size_union.
    - by rewrite set_map_singleton !size_singleton IH.
    - intros y ->%elem_of_singleton. by apply Hx.
    - clear IH. rewrite set_map_singleton. intros y ->%elem_of_singleton.
      intros (y & Hy & He)%elem_of_map_1. by simplify_eq.
  Qed.
End set_map.

(** An [mbind]-like operator for sets, but taking [f : A → list B], like stdlib's
[concat_map].
Contrast with [set_bind] (added in stdpp after we added [set_concat_map]. *)
Section set_concat_map.
  Context `{FinSet A C} `{FinSet B D}.

  Definition set_concat_map (f : A → list B) (xs : C) : D :=
    list_to_set (elements xs ≫= f).
  Implicit Types (a x : A) (b y : B) (f : A → list B) (xs : C).

  Lemma set_concat_map_empty f :
    set_concat_map f ∅ ≡ ∅.
  Proof. set_solver. Qed.

  #[global] Instance set_concat_map_perm_proper :
    Proper (pointwise_relation _ Permutation ==> equiv ==> equiv) set_concat_map.
  Proof. solve_proper. Qed.

  #[global] Instance set_concat_map_mono :
    Proper (pointwise_relation _ (⊆) ==> (⊆) ==> (⊆)) set_concat_map.
  Proof. solve_proper. Qed.

  Lemma elem_of_set_concat_map f b xs :
    b ∈ set_concat_map f xs ↔ ∃ x, x ∈ xs ∧ b ∈ f x.
  Proof. set_solver. Qed.

  #[global] Instance set_unfold_set_concat_map f b xs P Q :
    (∀ x, SetUnfoldElemOf x xs (P x)) → (∀ x, SetUnfoldElemOf b (f x) (Q x)) →
    SetUnfoldElemOf b (set_concat_map f xs) (∃ x, P x ∧ Q x).
  Proof. constructor. rewrite elem_of_set_concat_map. set_solver. Qed.

  Lemma set_concat_map_union f xs1 xs2 :
    set_concat_map f (xs1 ∪ xs2) ≡
    set_concat_map f xs1 ∪ set_concat_map f xs2.
  Proof. set_solver. Qed.

  Lemma set_concat_map_singleton f a :
    set_concat_map f {[ a ]} ≡ list_to_set $ f a.
  Proof. set_solver. Qed.

  Section set_concat_map_leibniz.
    Context `{!LeibnizEquiv C} `{!LeibnizEquiv D}.

    Lemma set_concat_map_empty_L f :
      set_concat_map f ∅ = ∅.
    Proof. unfold_leibniz. apply set_concat_map_empty. Qed.
    Lemma set_concat_map_union_L f bs1 bs2 :
      set_concat_map f (bs1 ∪ bs2) =
      set_concat_map f bs1 ∪ set_concat_map f bs2.
    Proof. unfold_leibniz. apply set_concat_map_union. Qed.
    Lemma set_concat_map_singleton_L f a :
      set_concat_map f {[ a ]} = list_to_set $ f a.
    Proof. unfold_leibniz. apply set_concat_map_singleton. Qed.
  End set_concat_map_leibniz.
End set_concat_map.

#[global] Instance set_concat_map_params :
  Params (@set_concat_map) 8 := {}.

(** Pairwise disjointness *)
Section fin_set.
  Context `{FinSet C D, Disjoint C, !RelDecision (##@{C})}.
  Implicit Types Xs Ys : D.

  #[global] Instance fin_set_pairwise_disjoint_dec : RelDecision (##ₚ@{D}).
  Proof. rewrite/RelDecision. apply _. Defined.

  (** Witnesses for non-pairwise disjoint finite sets *)
  Lemma not_pairwise_disjoint Xs Ys :
    ¬ Xs ##ₚ Ys <-> exists X Y, X ∈ Xs /\ Y ∈ Ys /\ ¬ (X = Y \/ X ## Y).
  Proof.
    rewrite/pairwise_disjoint/set_pairwise_disjoint.
    rewrite set_not_Forall. f_equiv=>X. split.
    - intros (? & (Y & ? & ?)%set_not_Forall); last by apply _. by exists Y.
    - intros (Y & ? & ? & ?). split; first done. rewrite set_not_Forall. by exists Y.
  Qed.
End fin_set.

Section set_rangeZ.
  #[local] Open Scope Z_scope.

  Definition set_rangeZ `{!Singleton Z C, !Union C, !Empty C} (i j : Z) : C :=
    list_to_set (rangeZ i j).

  Section dom_rangeZ.
    Context `{!ElemOf Z D, !Empty D, !Singleton Z D, !Union D}.

    Lemma elem_of_set_rangeZ `{!SemiSet Z D} x i j : x ∈ (set_rangeZ i j : D) <-> (i ≤ x < j).
    Proof.
      by rewrite /set_rangeZ elem_of_list_to_set elem_of_rangeZ.
    Qed.

    Lemma size_set_rangeZ `{!Intersection D, !Difference D, !Elements Z D, !FinSet Z D} i j :
      size (set_rangeZ i j : D) = Z.to_nat (j - i).
    Proof.
      have ? := NoDup_rangeZ i j.
      by rewrite /set_rangeZ size_list_to_set // -(inj_iff N.of_nat) [N.of_nat _]lengthN_rangeZ Z_nat_N.
    Qed.

  End dom_rangeZ.

End set_rangeZ.
