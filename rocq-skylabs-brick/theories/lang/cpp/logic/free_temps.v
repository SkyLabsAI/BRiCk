(*
 * Copyright (c) 2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
(** Definitions for the semantics
 *)
Require Import skylabs.prelude.base.

Require Import stdpp.coPset.
Require Import iris.bi.monpred.
Require Import skylabs.iris.extra.proofmode.proofmode.
Require Import iris.proofmode.classes.

Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.semantics.
Require Import skylabs.lang.cpp.logic.pred.
Require Import skylabs.lang.cpp.logic.heap_pred.
Require Import skylabs.lang.cpp.logic.translation_unit.
Require Import skylabs.iris.extra.bi.errors.

#[local] Set Primitive Projections.

Declare Scope free_scope.
Delimit Scope free_scope with free.
Reserved Infix "|*|" (at level 30).
Reserved Infix ">*>" (at level 30).

Module FreeTemps.

    (* BEGIN FreeTemps.t *)
    Inductive t : Set :=
    | id (* = fun x => x *)
    | delete (ty : decltype) (p : ptr) (* = delete_val ty p *)
            (* ^^ this type has qualifiers but is otherwise a runtime type *)
    | delete_va (va : list (type * ptr)) (p : ptr)
    | seq (f g : t) (* = fun x => f $ g x *)
    | par (f g : t) (* = fun x => Exists Qf Qg, f Qf ** g Qg ** (Qf -* Qg -* x) *)
    .
    (* END FreeTemps.t *)

    (*
    Fixpoint seq (f g : t) : t :=
      match f with
      | seq_ f f' => seq_ f (seq f' g)
      | id => g
      | _ => match g with
            | id => f
            | _ => seq_ f g
            end
      end.
    Lemma seq_idL a : seq id a = a.
    Proof. done. Qed.
    Lemma seq_idR a : seq a id = a.
    Proof. induction a; simpl; intros; eauto. rewrite IHa2. done. Qed.
    Lemma seq_assoc : forall a b c, seq (seq a b) c = seq a (seq b c).
    Proof.
      induction a; simpl; intros; eauto.
    *)

    #[local] Declare Scope free_scope.
    Module Import notations.
      Bind Scope free_scope with t.
      Notation "1" := id : free_scope.
      Infix ">*>" := seq : free_scope.
      Infix "|*|" := par : free_scope.
    End notations.
    #[local] Open Scope free_scope.

    Inductive t_equiv : Equiv t :=
    | refl l : l ≡ l
    | sym l r : l ≡ r -> r ≡ l
    | trans a b c : a ≡ b -> b ≡ c -> a ≡ c

  (*
    | delete_ref ty p : delete (Tref ty) p ≡ delete (Trv_ref ty) p
  *)

    | seqA x y z : x >*> (y >*> z) ≡ (x >*> y) >*> z
    | seq_id_unitL l : 1 >*> l ≡ l
    | seq_id_unitR l : l >*> 1 ≡ l
    | seq_proper_ : ∀ {a b}, a ≡ b -> ∀ {c d}, c ≡ d -> a >*> c ≡ b >*> d

    | parC l r : l |*| r ≡ r |*| l
    | parA x y z : x |*| (y |*| z) ≡ (x |*| y) |*| z
    | par_id_unitL l : 1 |*| l ≡ l
    | par_proper_ : ∀ {a b}, a ≡ b -> ∀ {c d}, c ≡ d -> a |*| c ≡ b |*| d
    .
    Notation t_eq := (≡@{t}) (only parsing).
    Existing Instance t_equiv.

    Fixpoint seq_canon (a b : t) {struct a} : t :=
      match a , b with
      | id , b => b
      | a , id => a
      | seq x y , b => seq_canon x (seq_canon y b)
      | _ , _ => seq a b
      end.

    (* assume that this is canonical *)
    Parameter ptr_cmp : ptr -> ptr -> comparison.
    Print comparison.

    Parameter t_cmp : forall (a b : t), comparison.
    (* This is just the canonical construction
      match a , b with
      | id , id => Eq
      | id , _ => Lt
      | delete _ _ , id => Gt
      | delete ty p , delete ty' p' => _
      | delete _ _ , _ => Lt
      | delete_va _ _ , (id | delete _ _) => Gt
      | delete_va tys p , delete_va tys' p' => _
      | delete_va _ _ , _ => Lt
      | seq _ _ , (id | delete _ _ | delete_va _ _) => Gt
      | seq l r , seq l' r' => _
      | seq _ _ , _ => Lt
      | par _ _ , (id | delete _ _ | delete_va _ _ | seq _ _) => Lt
      | par l r , par l' r' => _
      end.
      *)

    Fixpoint gather_pars (a : t) : list t :=
      match a with
      | id => []
      | par a b => gather_pars a ++ gather_pars b
      | _ => [a]
      end.

    Require stdpp.sorting.
    Fixpoint list_to_t (ls : list t) : t :=
      match ls with
      | nil => id
      | l :: nil => l
      | l :: ls => par l (list_to_t ls)
      end.

    (* NOTE: I can assume that [a] and [b] are canonical, so
      I need to merge them using the canonical ordering.
    *)
    Instance X: forall a b : t, Decision (t_cmp a b = Lt).
    Admitted.
    Definition par_canon (a b : t) : t :=
      list_to_t $ @sorting.merge_sort t (fun a b => t_cmp a b = Lt) _ (gather_pars a ++ gather_pars b).

    Fixpoint canon (a : t) {struct a} : t :=
      match a with
      | seq a b => seq_canon (canon a) (canon b)
      | par a b => par_canon (canon a) (canon b)
      | _ => a
      end.

    Lemma seq_canon_unitL a : seq_canon id a = a.
    Proof. Admitted.
    Lemma seq_canon_unitR a : seq_canon a id = a.
    Proof. Admitted.

    Lemma seq_canon_is_id a : forall b, seq_canon a b = id -> a = id /\ b = id.
    Proof.
      induction a; simpl; intros.
      { destruct b; simpl; intros; eauto; try congruence. }
      { destruct b; congruence. }
      { destruct b; congruence. }
      { destruct b; try congruence;
          apply IHa1 in H; destruct H; apply IHa2 in H0; destruct H0; congruence. }
      { destruct b; congruence. }
    Qed.

    Lemma canon_canonical : forall a b : t, a ≡ b -> canon a = canon b.
    Proof. (*
      induction 1; simpl; eauto.
      { (* trans *) etrans; eauto. }
      { (* seqA *)
        generalize (canon x), (canon y), (canon z). clear.
        induction t0; simpl; eauto.
        { destruct t0; simpl; eauto; solve [ destruct t0; simpl; eauto ]. }
        { destruct t0; simpl; eauto; solve [ destruct t0; simpl; eauto ]. }
        { intros.
          case_match.
          { apply seq_canon_is_id in H.  destruct H.  subst. rewrite seq_canon_unitR.  done. }
          { case_match; simpl in *; subst; eauto; rewrite -IHt0_1; f_equal.
            { destruct t1; inversion H; subst; eauto. rewrite seq_canon_unitR. done. }
            { destruct t1; inversion H; subst; eauto. }
            { destruct t1; inversion H; subst; eauto; rewrite -IHt0_2; f_equal. }
            { destruct t1; inversion H; subst; eauto. } }
          { destruct t0; simpl in *; subst; eauto; try (rewrite -IHt0_1 -IHt0_2; f_equal; f_equal);
              destruct t1; inversion H; subst; eauto. }
          { destruct t0; simpl in *; subst; eauto; try (rewrite -IHt0_1 -IHt0_2; f_equal; f_equal);
              destruct t1; inversion H; subst; eauto. }
          { destruct t0; simpl in *; subst; eauto; try (rewrite -IHt0_1 -IHt0_2; f_equal; f_equal);
              destruct t1; inversion H; subst; eauto. } }
        admit. }
      { rewrite seq_canon_unitR. done. }
      { by f_equal. }
      { (* parC -- this is problematic because there is no canonical ordering to the unit elements without a total ordering on [ptr] *)
        admit.
      }
      { (* parA *)
        admit.
      }
      { admit. } *)
    Admitted.

    Lemma canon_equiv f : FreeTemps.canon f ≡ f.
    Proof. Admitted.

    #[local] Opaque FreeTemps.canon.
    #[global] Instance canon_proper : Proper ((≡) ==> eq) FreeTemps.canon.
    Proof. Admitted.


    #[global] Instance t_dec : EqDecision t.
    Admitted.

    Class IsCanonical (free : t) : Prop :=
      is_canon : Is_true (bool_decide (free = canon free)).

    #[global] Instance id_IsCanonical : IsCanonical id.
    Proof. Admitted.

    Lemma IsCanonical_canonical f : ProofIrrel (FreeTemps.IsCanonical f).
    Proof. apply Is_true_pi. Qed.

    Lemma K_ext {T} : forall (K : forall x : FreeTemps.t, FreeTemps.IsCanonical x -> T),
      forall free1 free2 pf1 pf2, free1 ≡ free2 -> K free1 pf1 = K free2 pf2.
    Proof.
      clear.
      intros.
      assert (free1 = FreeTemps.canon free1).
      { clear -pf1. eapply bool_decide_unpack. apply pf1. }
      assert (free2 = FreeTemps.canon free2).
      { clear -pf2. eapply bool_decide_unpack. apply pf2. }
      apply FreeTemps.canon_canonical in H.
      unfold FreeTemps.IsCanonical in *.
      assert (free1 = free2).
      { by rewrite H0 H -H1. }
      revert H1. revert H. revert pf2.
      destruct H2.
      intros.
      by rewrite (Is_true_pi _ pf1 pf2).
    Qed.

    #[global] Instance canon_IsCanonical free : IsCanonical (canon free).
    Proof. Admitted.

    #[global] Existing Instance t_equiv.
    #[global] Instance t_equivalence : Equivalence t_eq :=
      Build_Equivalence _ refl sym trans.

    #[global] Instance seq_assoc : Assoc equiv seq := seqA.
    #[global] Instance seq_left_id : LeftId equiv id seq := seq_id_unitL.
    #[global] Instance seq_right_id : RightId equiv id seq := seq_id_unitR.
    #[global] Instance seq_proper : Proper (t_eq ==> t_eq ==> t_eq) seq := @seq_proper_.

    #[global] Instance par_comm : Comm equiv par := parC.
    #[global] Instance par_left_id : LeftId equiv id par := par_id_unitL.
    #[global] Instance par_right_id : RightId equiv id par.
    Proof. intros x. by rewrite comm left_id. Qed.
    #[global] Instance par_proper : Proper (t_eq ==> t_eq ==> t_eq) par := @par_proper_.
End FreeTemps.
Export FreeTemps.notations.
Notation FreeTemps := FreeTemps.t.
Notation FreeTemp := FreeTemps.t (only parsing).
