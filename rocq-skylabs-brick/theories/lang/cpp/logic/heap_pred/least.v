(*
 * Copyright (c) 2023 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bluerock.lang.cpp.logic.heap_pred.prelude.

Section with_cpp.
  Context `{Σ : cpp_logic} {σ : genv}.

  Section leastR.
    Context {A : ofe}.
    Class RepMonoPred (F : (A -> Rep) -> (A -> Rep)) : Prop :=
    { rep_mono_pred : ∀ Φ Ψ : A → Rep,
        NonExpansive Φ → NonExpansive Ψ →
        □ (Forall (p : ptr) (x : A), p |-> Φ x -* p |-> Ψ x) -∗
        Forall (x : A) (p : ptr), p |-> F Φ x -* p |-> F Ψ x
    ; rep_mono_pred_ne : ∀ Φ : A → Rep, NonExpansive Φ → NonExpansive (F Φ) }.

    Definition leastR (F : (A -> Rep) -> (A -> Rep)) : A -> Rep :=
      fun x => Forall Φ : A -n> Rep, (□ Forall (x0 : A), pureR (Forall (p : ptr), p |-> F Φ x0 -* p |-> Φ x0)) -* Φ x.

    #[global] Instance leastR_ne n :
      Proper (pointwise_relation (A -> Rep) (pointwise_relation A (dist n)) ==> dist n ==> dist n) leastR.
    Proof. solve_proper. Qed.
    #[global] Instance leastR_proper :
      Proper (pointwise_relation (A -> Rep) (pointwise_relation A (≡)) ==> (≡) ==> (≡)) leastR.
    Proof. solve_proper. Qed.

    Theorem leastR_fold (F : (A -> Rep) -> (A -> Rep)) {RMP : RepMonoPred F} a :
      F (leastR F) a |-- leastR F a.
    Proof.
      rewrite /leastR/=. constructor=>p.
      rewrite monPred_at_forall.
      iIntros "H" (fx).
      rewrite monPred_at_wand.
      iIntros (? ?) "Hi".
      rewrite monPred_at_intuitionistically {2}/pureR /as_Rep/=.
      iDestruct "Hi" as "#Hi".
      simpl.
      iDestruct ("Hi" $! a j) as "Hj".
      rewrite !INTERNAL._at_eq. iApply "Hj"; iClear "Hj".
      inversion H; clear H; subst.
      iDestruct (rep_mono_pred _ fx with "[#]") as "X".
      2:{
        iSpecialize ("X" $! a j).
        rewrite !INTERNAL._at_eq.
        iApply "X".
        unshelve instantiate (1:=OfeMor (λ x : A, Forall Φ : A -n> Rep, □ (Forall x0 : A, pureR (Forall p : ptr, p |-> F Φ x0 -* p |-> Φ x0)) -* Φ x)); first solve_proper.
        iApply "H". }
      { iIntros "!>" (??). (* iSpecialize ("Hi" $! x p). *)
        rewrite !INTERNAL._at_eq /=.
        iIntros "X".
        rewrite monPred_at_forall.
        iSpecialize ("X" $! fx).
        rewrite monPred_at_wand.
        iSpecialize ("X" $! p eq_refl).
        iApply "X".
        rewrite monPred_at_intuitionistically.
        iModIntro.
        rewrite monPred_at_forall. eauto. }
    Qed.

    Theorem leastR_unfold (F : (A -> Rep) -> (A -> Rep)) {RMP : RepMonoPred F} a :
      leastR F a |-- F (leastR F) a.
    Proof.
      rewrite /leastR. constructor=>p.
      iIntros "X".
      unshelve iApply ("X" $! (OfeMor (F (leastR F)))).
      { eapply rep_mono_pred_ne; solve_proper. }
      rewrite /pureR/as_Rep/=.
      iIntros "!>" (??).
      iApply (rep_mono_pred (F (leastR F)) (leastR F) with "[#]").
      { eapply rep_mono_pred_ne; solve_proper. }
      iIntros "!>" (??). rewrite leastR_fold. eauto.
    Qed.


(*
    Theorem leastR_ind (F : (A -> Rep) -> (A -> Rep)) P `{!NonExpansive P} :
          □ (Forall (p : ptr) (y : A), p |-> F P y -* p |-> P y)
      |-- Forall (p : ptr) x, p |-> leastR F x -* p |-> P x.
    Proof.
      iIntros "#HP" (??) "H".
      rewrite /leastR _at_forall.
      unshelve iSpecialize ("H" $! (OfeMor P)); simpl.
      { refine _. }
      rewrite !_at_wand !_at_intuitionistically !_at_forall.
      iApply "H".
      iIntros "!>" (?). rewrite _at_pureR.
      iIntros (?); iApply "HP".
    Qed.
*)

    Theorem leastR_ind (F : (A -> Rep) -> (A -> Rep)) (P : ptr -> A -> mpred) {_ : forall p, NonExpansive (P p)} (p : ptr) x :
          □ (Forall (p : ptr) (y : A), p |-> F (fun x => as_Rep (fun p => P p x)) y -* P p y)
      |-- p |-> leastR F x -* P p x.
    Proof.
      iIntros "#HP H".
      rewrite /leastR _at_forall.
      unshelve iSpecialize ("H" $! (OfeMor (fun x => as_Rep (fun p => P p x)))); simpl.
      { rewrite /as_Rep/=. intro.
        red; intros. red; intros. simpl.
        constructor. intros.
        simpl. apply H. auto. }
      rewrite !_at_wand !_at_intuitionistically !_at_forall.
      rewrite _at_as_Rep.
      iApply "H".
      iIntros "!>" (?). rewrite _at_pureR.
      iIntros (?). rewrite _at_as_Rep; iApply "HP".
    Qed.

    Lemma leastR_indR (F : (A -> Rep) -> (A -> Rep)) (P : A -> Rep) {_ : NonExpansive P} x :
          □ (pureR $ Forall (p : ptr) (y : A), p |-> F P y -* p |-> P y)
      |-- leastR F x -* P x.
    Proof.
      constructor=>p.
      rewrite -!INTERNAL._at_eq.
      rewrite _at_intuitionistically. setoid_rewrite _at_wand.
      iIntros "#HP".
      rewrite (INTERNAL._at_eq p (P x)).
      iApply (leastR_ind _ (fun p x => P x p)).
      rewrite _at_pureR.
      iModIntro; iIntros (??).
      iIntros "X".
      rewrite -INTERNAL._at_eq. iApply "HP".
      rewrite /as_Rep/=.
      (* this should be provable *)
    Abort.

    #[global] Instance leastR_timeless F :
      (forall fx, Timeless1 fx -> Timeless1 (F fx)) ->
      Timeless1 (leastR F).
    Proof.
      intros. red. iIntros "X".
    Abort. (* unprovable *)

  End leastR.

End with_cpp.
