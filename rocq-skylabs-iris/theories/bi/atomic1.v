(*
 * Copyright (c) 2021 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *
 *
 * Some of the following code is derived from code original to the
 * Iris project. That original code is
 *
 *	Copyright Iris developers and contributors
 *
 * and used according to the following license.
 *
 *	SPDX-License-Identifier: BSD-3-Clause
 *
 * Original Code:
 * https://gitlab.mpi-sws.org/iris/iris/-/blob/5bb93f57729a8cc7d0ffeaab769cd24728e51a38/iris/bi/lib/atomic.v
 *
 * Original Iris License:
 * https://gitlab.mpi-sws.org/iris/iris/-/blob/5bb93f57729a8cc7d0ffeaab769cd24728e51a38/LICENSE-CODE
 *)

Require Import stdpp.coPset.
Require Import stdpp.namespaces.
Require Import iris.bi.lib.fixpoint_mono.
Require Import iris.proofmode.coq_tactics.
Require Import bluerock.iris.extra.proofmode.proofmode.
Require Import iris.proofmode.reduction.
Require Import iris.prelude.options.
Require Import iris.bi.lib.atomic.

Require Export bluerock.iris.extra.bi.laterable.
Require Import bluerock.iris.extra.bi.telescopes.

(** Conveniently split a conjunction on both assumption and conclusion. *)
Local Tactic Notation "iSplitWith" constr(H) :=
  iApply (bi.and_parallel with H); iSplit; iIntros H.

Section definition.
  Context `{BiFUpd PROP} {TA TB : tele}.
  Implicit Types
    (Eo Ei : coPset) (* outer/inner masks *)
    (α : TA → PROP) (* atomic pre-condition *)
    (P : PROP) (* abortion condition *)
    (β : TA → TB → PROP) (* atomic post-condition *)
    (Φ : TA → TB → PROP) (* post-condition *)
  .

  (** atomic1_acc as the "introduction form" of atomic updates: An accessor
      that can be aborted back to [P]. *)
  (** Main extension compared to [atomic_acc]:
    This one can make a step---having a later---for the COMMIT case,i.e.
      ▷ (∀.. y, β x y ={Ei, Eo}=∗ Φ x y)

    This means that the client of this spec can make a step before applying the
    closing COMMIT [fupd], and the prover the spec needs to take an actual step
    when COMMITing.
    Consider the example of an AU1 (atomic update) that takes a step.
    - As a client of an AU spec, which has the form `AU1 ⊢ wp`, the client
      applies the spec and has to prove the `AU1`. In proving those, the client
      has a later in the goal of the COMMIT [fupd], which allows them to strip
      later from resources in the context, including resources that were
      obtained by opening the invariants around the AU.
      This stripping of laters is done before actually COMMITing.
    - As the prover of the same AU spec `AU1 ⊢ wp`, the prover assumes the
      AU1 and proves the `wp`. Then the prover needs to apply the COMMIT [fupd]
      to finish. But the COMMIT [fupd] is under a later, so the prover needs to
      have the `wp` takes an actual step to strip that later before COMMITing.
      This also demonstrates one you cannot prove an AU1 spec for a `wp` that
      does not take a step.

    Note that we can also add a later to the ABORT case:
      ▷ (α x ={Ei, Eo}=∗ P)

    But that means the the prover has to show the implementation takes at least
    a step every time the abort is used. While this is not unreasonable, it
    restricts the set of implementations that can be proven with this spec. We
    therefore choose not to support it here. *)
  Definition atomic1_acc Eo Ei α P β Φ : PROP :=
    (|={Eo, Ei}=> ∃.. x, α x ∗
          ((α x ={Ei, Eo}=∗ P) ∧ ▷ (∀.. y, β x y ={Ei, Eo}=∗ Φ x y))
    )%I.

  (* atomic1_acc is more restricted than atomic_acc : ACCC ⊢ ACCC1.
    The direction of implication may look perplexing, but this really gives us
    what we want: a AU1 spec implies a AU spec, that is
      (AU1 -∗ wp) ⊢ (AU -∗ wp)
  *)
  Lemma atomic_acc_atomic1_acc Eo Ei α P β Φ :
    atomic_acc Eo Ei α P β Φ -∗ atomic1_acc Eo Ei α P β Φ.
  Proof.
    rewrite /atomic1_acc /atomic_acc.
    iIntros "AS". iMod "AS" as (x) "[Hα Hclose]".
    iModIntro. iExists x. iFrame "Hα". iSplit.
    - iIntros "Hα". iDestruct "Hclose" as "[Hclose _]".
      iApply "Hclose". done.
    - iIntros "!>" (y) "Hβ". iDestruct "Hclose" as "[_ Hclose]".
      iApply "Hclose". done.
  Qed.

  Lemma atomic1_acc_wand Eo Ei α P1 P2 β Φ1 Φ2 :
    ((P1 -∗ P2) ∧ ▷ (∀.. x y, Φ1 x y -∗ Φ2 x y)) -∗
    (atomic1_acc Eo Ei α P1 β Φ1 -∗ atomic1_acc Eo Ei α P2 β Φ2).
  Proof.
    iIntros "HP12 AS". iMod "AS" as (x) "[Hα Hclose]".
    iModIntro. iExists x. iFrame "Hα". iSplit.
    - iIntros "Hα". iDestruct "Hclose" as "[Hclose _]".
      iApply "HP12". iApply "Hclose". done.
    - iIntros "!>" (y) "Hβ". iDestruct "Hclose" as "[_ Hclose]".
      iApply "HP12". iApply "Hclose". done.
  Qed.

  Lemma atomic1_acc_mask Eo Ed α P β Φ :
    atomic1_acc Eo (Eo∖Ed) α P β Φ ⊣⊢ ∀ E, ⌜Eo ⊆ E⌝ → atomic1_acc E (E∖Ed) α P β Φ.
  Proof.
    iSplit; last first.
    { iIntros "Hstep". iApply ("Hstep" with "[% //]"). }
    iIntros "Hstep" (E HE).
    iApply (fupd_mask_frame_acc with "Hstep"); first done.
    iIntros "Hstep". iDestruct "Hstep" as (x) "[Hα Hclose]".
    iIntros "!> Hclose'".
    iExists x. iFrame. iSplitWith "Hclose".
    - iIntros "Hα". iApply "Hclose'". iApply "Hclose". done.
    - iIntros "!>" (y) "Hβ". iApply "Hclose'". iApply "Hclose". done.
  Qed.

  Lemma atomic1_acc_mask_weaken Eo1 Eo2 Ei α P β Φ :
    Eo1 ⊆ Eo2 →
    atomic1_acc Eo1 Ei α P β Φ -∗ atomic1_acc Eo2 Ei α P β Φ.
  Proof.
    iIntros (HE) "Hstep".
    iMod fupd_mask_subseteq as "Hclose1"; first done.
    iMod "Hstep" as (x) "[Hα Hclose2]". iIntros "!>". iExists x.
    iFrame. iSplitWith "Hclose2".
    - iIntros "Hα". iMod ("Hclose2" with "Hα") as "$". done.
    - iIntros "!>" (y) "Hβ". iMod ("Hclose2" with "Hβ") as "$". done.
  Qed.

  (** atomic1_update as a fixed-point of the equation
   AU = atomic1_acc α AU β Q
  *)
  Context Eo Ei α β Φ.

  Definition atomic1_update_pre (Ψ : () → PROP) (_ : ()) : PROP :=
    atomic1_acc Eo Ei α (Ψ ()) β Φ.

  Local Instance atomic1_update_pre_mono : BiMonoPred atomic1_update_pre.
  Proof.
    constructor.
    - iIntros (P1 P2 ??) "#HP12". iIntros ([]) "AU".
      iApply (atomic1_acc_wand with "[HP12] AU").
      iSplit; last by eauto. iApply "HP12".
    - intros ??. solve_proper.
  Qed.

  Definition atomic1_update_def :=
    bi_greatest_fixpoint atomic1_update_pre ().

End definition.

(** Seal it *)
Definition atomic1_update_aux : seal (@atomic1_update_def). Proof. by eexists. Qed.
Definition atomic1_update := atomic1_update_aux.(unseal).
Global Arguments atomic1_update {PROP _ TA TB}.
Definition atomic1_update_eq : @atomic1_update = _ := atomic1_update_aux.(seal_eq).

Global Arguments atomic1_acc {PROP _ TA TB} Eo Ei _ _ _ _ : simpl never.
Global Arguments atomic1_update {PROP _ TA TB} Eo Ei _ _ _ : simpl never.

(** Notation: Atomic updates *)
Notation "'AU1' '<<' ∀ x1 .. xn , α '>>' @ Eo , Ei '<<' ∃ y1 .. yn , β , 'COMM' Φ '>>'" :=
  (atomic1_update (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
                 (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
                 Eo Ei
                 (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn, α%I) ..)
                 (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn,
                         tele_app (TT:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
                         (λ y1, .. (λ yn, β%I) .. )
                        ) .. )
                 (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn,
                         tele_app (TT:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
                         (λ y1, .. (λ yn, Φ%I) .. )
                        ) .. )
  )
  (at level 20, Eo, Ei, α, β, Φ at level 200, x1 binder, xn binder, y1 binder, yn binder,
   format "'[   ' 'AU1'  '<<'  ∀  x1  ..  xn ,  α  '>>'  '/' @  Eo ,  Ei  '/' '[   ' '<<'  ∃  y1  ..  yn ,  β ,  '/' COMM  Φ  '>>' ']' ']'") : bi_scope.

Notation "'AU1' '<<' ∀ x1 .. xn , α '>>' @ Eo , Ei '<<' β , 'COMM' Φ '>>'" :=
  (atomic1_update (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
                 (TB:=TeleO)
                 Eo Ei
                 (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn, α%I) ..)
                 (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn, tele_app (TT:=TeleO) β%I) .. )
                 (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn, tele_app (TT:=TeleO) Φ%I) .. )
  )
  (at level 20, Eo, Ei, α, β, Φ at level 200, x1 binder, xn binder,
   format "'[   ' 'AU1'  '<<'  ∀  x1  ..  xn ,  α  '>>'  '/' @  Eo ,  Ei  '/' '[   ' '<<'  β ,  '/' COMM  Φ  '>>' ']' ']'") : bi_scope.

Notation "'AU1' '<<' α '>>' @ Eo , Ei '<<' ∃ y1 .. yn , β , 'COMM' Φ '>>'" :=
  (atomic1_update (TA:=TeleO)
                 (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
                 Eo Ei
                 (tele_app (TT:=TeleO) α%I)
                 (tele_app (TT:=TeleO) $
                       tele_app (TT:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
                                (λ y1, .. (λ yn, β%I) ..))
                 (tele_app (TT:=TeleO) $
                       tele_app (TT:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
                                (λ y1, .. (λ yn, Φ%I) ..))
  )
  (at level 20, Eo, Ei, α, β, Φ at level 200, y1 binder, yn binder,
   format "'[   ' 'AU1'  '<<'  α  '>>'  '/' @  Eo ,  Ei  '/' '[   ' '<<'  ∃  y1  ..  yn ,  β ,  '/' COMM  Φ  '>>' ']' ']'") : bi_scope.

Notation "'AU1' '<<' α '>>' @ Eo , Ei '<<' β , 'COMM' Φ '>>'" :=
  (atomic1_update (TA:=TeleO) (TB:=TeleO) Eo Ei
                 (tele_app (TT:=TeleO) α%I)
                 (tele_app (TT:=TeleO) $ tele_app (TT:=TeleO) β%I)
                 (tele_app (TT:=TeleO) $ tele_app (TT:=TeleO) Φ%I)
  )
  (at level 20, Eo, Ei, α, β, Φ at level 200,
   format "'[   ' 'AU1'  '<<'  α  '>>'  '/' @  Eo ,  Ei  '/' '[   ' '<<'  β ,  '/' COMM  Φ  '>>' ']' ']'") : bi_scope.

(** Notation: Atomic accessors *)
Notation "'AACC1' '<<' ∀ x1 .. xn , α 'ABORT' P '>>' @ Eo , Ei '<<' ∃ y1 .. yn , β , 'COMM' Φ '>>'" :=
  (atomic1_acc (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
              (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
              Eo Ei
              (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                    λ x1, .. (λ xn, α%I) ..)
              P%I
              (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                    λ x1, .. (λ xn,
                      tele_app (TT:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
                      (λ y1, .. (λ yn, β%I) .. )
                     ) .. )
              (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                    λ x1, .. (λ xn,
                      tele_app (TT:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
                      (λ y1, .. (λ yn, Φ%I) .. )
                     ) .. )
  )
  (at level 20, Eo, Ei, α, P, β, Φ at level 200, x1 binder, xn binder, y1 binder, yn binder,
   format "'[     ' 'AACC1'  '[   ' '<<'  ∀  x1  ..  xn ,  α  '/' ABORT  P  '>>'  ']' '/' @  Eo ,  Ei  '/' '[   ' '<<'  ∃  y1  ..  yn ,  β ,  '/' COMM  Φ  '>>' ']' ']'") : bi_scope.

Notation "'AACC1' '<<' ∀ x1 .. xn , α 'ABORT' P '>>' @ Eo , Ei '<<' β , 'COMM' Φ '>>'" :=
  (atomic1_acc (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
              (TB:=TeleO)
              Eo Ei
              (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                        λ x1, .. (λ xn, α%I) ..)
              P%I
              (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                        λ x1, .. (λ xn, tele_app (TT:=TeleO) β%I) .. )
              (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                        λ x1, .. (λ xn, tele_app (TT:=TeleO) Φ%I) .. )
  )
  (at level 20, Eo, Ei, α, P, β, Φ at level 200, x1 binder, xn binder,
   format "'[     ' 'AACC1'  '[   ' '<<'  ∀  x1  ..  xn ,  α  '/' ABORT  P  '>>'  ']' '/' @  Eo ,  Ei  '/' '[   ' '<<'  β ,  '/' COMM  Φ  '>>' ']' ']'") : bi_scope.

Notation "'AACC1' '<<' α 'ABORT' P '>>' @ Eo , Ei '<<' ∃ y1 .. yn , β , 'COMM' Φ '>>'" :=
  (atomic1_acc (TA:=TeleO)
              (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
              Eo Ei
              (tele_app (TT:=TeleO) α%I)
              P%I
              (tele_app (TT:=TeleO) $
                        tele_app (TT:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
                        (λ y1, .. (λ yn, β%I) ..))
              (tele_app (TT:=TeleO) $
                        tele_app (TT:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
                        (λ y1, .. (λ yn, Φ%I) ..))
  )
  (at level 20, Eo, Ei, α, P, β, Φ at level 200, y1 binder, yn binder,
   format "'[     ' 'AACC1'  '[   ' '<<'  α  '/' ABORT  P  '>>'  ']' '/' @  Eo ,  Ei  '/' '[   ' '<<'  ∃  y1  ..  yn ,  β ,  '/' COMM  Φ  '>>' ']' ']'") : bi_scope.

Notation "'AACC1' '<<' α 'ABORT' P '>>' @ Eo , Ei '<<' β , 'COMM' Φ '>>'" :=
  (atomic1_acc (TA:=TeleO)
              (TB:=TeleO)
              Eo Ei
              (tele_app (TT:=TeleO) α%I)
              P%I
                 (tele_app (TT:=TeleO) $ tele_app (TT:=TeleO) β%I)
                 (tele_app (TT:=TeleO) $ tele_app (TT:=TeleO) Φ%I)
  )
  (at level 20, Eo, Ei, α, P, β, Φ at level 200,
   format "'[     ' 'AACC1'  '[   ' '<<'  α  '/' ABORT  P  '>>'  ']' '/' @  Eo ,  Ei  '/' '[   ' '<<'  β ,  '/' COMM  Φ  '>>' ']' ']'") : bi_scope.

(** Lemmas about AU *)
Section lemmas.
  Context `{BiFUpd PROP} {TA TB : tele}.
  Implicit Types (α : TA → PROP) (β Φ : TA → TB → PROP) (P : PROP).

  Local Existing Instances atomic1_update_pre_mono atomic_update_pre_mono.

  (* Can't be in the section above as that fixes the parameters *)
  Global Instance atomic1_acc_ne Eo Ei n :
    Proper (
        pointwise_relation TA (dist n) ==>
        dist n ==>
        pointwise_relation TA (pointwise_relation TB (dist n)) ==>
        pointwise_relation TA (pointwise_relation TB (dist n)) ==>
        dist n
    ) (atomic1_acc (PROP:=PROP) Eo Ei).
  Proof. solve_proper. Qed.

  Global Instance atomic1_update_ne Eo Ei n :
    Proper (
        pointwise_relation TA (dist n) ==>
        pointwise_relation TA (pointwise_relation TB (dist n)) ==>
        pointwise_relation TA (pointwise_relation TB (dist n)) ==>
        dist n
    ) (atomic1_update (PROP:=PROP) Eo Ei).
  Proof.
    rewrite atomic1_update_eq /atomic1_update_def /atomic1_update_pre. solve_proper.
  Qed.

  (* AU implies AU1 *)
  Lemma atomic_update_atomic1_update Eo Ei α β Φ :
    atomic_update Eo Ei α β Φ ⊢ atomic1_update Eo Ei α β Φ.
  Proof.
    rewrite atomic.atomic_update_unseal atomic1_update_eq /atomic1_update_def /=.
    iIntros "HAU".
    iApply (greatest_fixpoint_coiter _ (λ _, atomic.atomic_update_def Eo Ei α β Φ)); last done.
    iIntros "!> *". rewrite {1}/atomic.atomic_update_def /= greatest_fixpoint_unfold.
    by iApply atomic_acc_atomic1_acc.
  Qed.

  Lemma atomic1_update_mask Eo Ed α β Φ :
    atomic1_update Eo (Eo∖Ed) α β Φ ⊣⊢ ∀ E, ⌜Eo ⊆ E⌝ → atomic1_update E (E∖Ed) α β Φ.
  Proof.
    iSplit; last first.
    { iIntros "AU". iApply ("AU" with "[% //]"). }
    rewrite atomic1_update_eq {2}/atomic1_update_def /=.
    iIntros "AU" (E HE).
    iApply (greatest_fixpoint_coiter _ (λ _, atomic1_update_def Eo (Eo ∖ Ed) α β Φ)); last done.
    iIntros "!>" ([]).
    rewrite {1}/atomic1_update_def /= greatest_fixpoint_unfold.
    rewrite /atomic1_update_pre atomic1_acc_mask.
    iIntros "AAC". by iApply "AAC".
  Qed.

  Lemma atomic1_update_mask_weaken Eo1 Eo2 Ei α β Φ :
    Eo1 ⊆ Eo2 →
    atomic1_update Eo1 Ei α β Φ ⊢ atomic1_update Eo2 Ei α β Φ.
  Proof.
    rewrite atomic1_update_eq {2}/atomic1_update_def /=.
    iIntros (Heo) "HAU".
    iApply (greatest_fixpoint_coiter _ (λ _, atomic1_update_def Eo1 Ei α β Φ)); last done.
    iIntros "!> *". rewrite {1}/atomic1_update_def /= greatest_fixpoint_unfold.
    iApply atomic1_acc_mask_weaken. done.
  Qed.

  (** The elimination form: an atomic accessor *)
  Lemma aupd1_aacc Eo Ei α β Φ :
    atomic1_update Eo Ei α β Φ ⊢
    atomic1_acc Eo Ei α (atomic1_update Eo Ei α β Φ) β Φ.
  Proof using Type*.
    rewrite atomic1_update_eq {1}/atomic1_update_def /=. iIntros "HUpd".
    iPoseProof (greatest_fixpoint_unfold_1 with "HUpd") as "HUpd". done.
  Qed.

  (* This lets you eliminate atomic updates with iMod. *)
  Global Instance elim_mod_aupd1 φ Eo Ei E α β Φ Q Q' :
    (∀ R, ElimModal φ false false (|={E,Ei}=> R) R Q Q') →
    ElimModal (φ ∧ Eo ⊆ E) false false
              (atomic1_update Eo Ei α β Φ)
              (∃.. x, α x ∗
                       (α x ={Ei,E}=∗ atomic1_update Eo Ei α β Φ) ∧
                       ▷ (∀.. y, β x y ={Ei,E}=∗ Φ x y))
              Q Q'.
  Proof.
    intros ?. rewrite /ElimModal /= =>-[??]. iIntros "[AU Hcont]".
    iPoseProof (aupd1_aacc with "AU") as "AC".
    iMod (atomic1_acc_mask_weaken with "AC"); first done.
    iApply "Hcont". done.
  Qed.

  Lemma aupd1_intro P Q α β Eo Ei Φ :
    Affine P → Persistent P →
    (P ∗ Q ⊢ atomic1_acc Eo Ei α Q β Φ) →
    P ∗ Q ⊢ atomic1_update Eo Ei α β Φ.
  Proof.
    rewrite atomic1_update_eq {1}/atomic1_update_def /=.
    iIntros (?? HAU) "[#HP HQ]".
    iApply (greatest_fixpoint_coiter _ (λ _, Q)); last done. iIntros "!>" ([]) "HQ".
    iApply HAU. by iFrame.
  Qed.

  Lemma aacc1_intro Eo Ei α P β Φ :
    Ei ⊆ Eo → ⊢ (∀.. x, α x -∗
    ((α x ={Eo}=∗ P) ∧ ▷ (∀.. y, β x y ={Eo}=∗ Φ x y)) -∗
    atomic1_acc Eo Ei α P β Φ).
  Proof.
    iIntros (? x) "Hα Hclose".
    iMod fupd_mask_subseteq as "Hclose'"; last iModIntro; first set_solver.
    iExists x. iFrame. iSplitWith "Hclose".
    - iIntros "Hα". iMod "Hclose'" as "_". iApply "Hclose". done.
    - iIntros "!>" (y) "Hβ". iMod "Hclose'" as "_". iApply "Hclose". done.
  Qed.

  (* This lets you open invariants etc. when the goal is an atomic accessor. *)
  Global Instance elim_acc_aacc1 {X} E1 E2 Ei (α' β' : X → PROP) γ' α β Pas Φ :
    ElimAcc (X:=X) True (fupd E1 E2) (fupd E2 E1) α' β' γ'
            (atomic1_acc E1 Ei α Pas β Φ)
            (λ x', atomic1_acc E2 Ei α (β' x' ∗ (γ' x' -∗? Pas))%I β
                (λ.. x y, β' x' ∗ (γ' x' -∗? Φ x y))
            )%I.
  Proof.
    (* FIXME: Is there any way to prevent maybe_wand from unfolding?
       It gets unfolded by env_cbv in the proofmode, ideally we'd like that
       to happen only if one argument is a constructor. *)
    iIntros (_) "Hinner >Hacc". iDestruct "Hacc" as (x') "[Hα' Hclose]".
    iMod ("Hinner" with "Hα'") as (x) "[Hα Hclose']".
    iMod (fupd_mask_subseteq) as "Hclose''"; last iModIntro; first done.
    iExists x. iFrame. iSplitWith "Hclose'".
    - iIntros "Hα". iMod "Hclose''" as "_".
      iMod ("Hclose'" with "Hα") as "[Hβ' HPas]".
      iMod ("Hclose" with "Hβ'") as "Hγ'".
      iModIntro. destruct (γ' x'); iApply "HPas"; done.
    - iIntros "!>" (y) "Hβ". iMod "Hclose''" as "_".
      iMod ("Hclose'" with "Hβ") as "Hβ'".
      (* FIXME: Using ssreflect rewrite does not work, see Coq bug #7773. *)
      rewrite ->!tele_app_bind. iDestruct "Hβ'" as "[Hβ' HΦ]".
      iMod ("Hclose" with "Hβ'") as "Hγ'".
      iModIntro. destruct (γ' x'); iApply "HΦ"; done.
  Qed.

  (* Everything that fancy updates can eliminate without changing, atomic
  accessors can eliminate as well.  This is a forwarding instance needed becuase
  atomic1_acc is becoming opaque. *)
  Global Instance elim_modal_acc p q φ P P' Eo Ei α Pas β Φ :
    (∀ Q, ElimModal φ p q P P' (|={Eo,Ei}=> Q) (|={Eo,Ei}=> Q)) →
    ElimModal φ p q P P'
              (atomic1_acc Eo Ei α Pas β Φ)
              (atomic1_acc Eo Ei α Pas β Φ).
  Proof. intros Helim. apply Helim. Qed.

  Lemma aacc1_aacc {TA' TB' : tele} E1 E1' E2 E3
        α P β Φ
        (α' : TA' → PROP) P' (β' Φ' : TA' → TB' → PROP) :
    E1' ⊆ E1 →
    atomic1_acc E1' E2 α P β Φ ⊢
    (∀.. x, α x -∗ atomic1_acc E2 E3 α' (α x ∗ (P ={E1}=∗ P')) β'
            (λ.. x' y', (α x ∗ (P ={E1}=∗ Φ' x' y'))
                    ∨ ∃.. y, β x y ∗ (Φ x y ={E1}=∗ Φ' x' y'))) -∗
    atomic1_acc E1 E3 α' P' β' Φ'.
  Proof.
    iIntros (?) "Hupd Hstep".
    iMod (atomic1_acc_mask_weaken with "Hupd") as (x) "[Hα Hclose]"; first done.
    iMod ("Hstep" with "Hα") as (x') "[Hα' Hclose']".
    iModIntro. iExists x'. iFrame "Hα'". iSplit.
    - iIntros "Hα'". iDestruct "Hclose'" as "[Hclose' _]".
      iMod ("Hclose'" with "Hα'") as "[Hα Hupd]".
      iDestruct "Hclose" as "[Hclose _]".
      iMod ("Hclose" with "Hα"). iApply "Hupd". auto.
    - iIntros "!>" (y') "Hβ'". iDestruct "Hclose'" as "[_ Hclose']".
      iMod ("Hclose'" with "Hβ'") as "Hres".
      (* FIXME: Using ssreflect rewrite does not work, see Coq bug #7773. *)
      rewrite ->!tele_app_bind. iDestruct "Hres" as "[[Hα HΦ']|Hcont]".
      + (* Abort the step we are eliminating *)
        iDestruct "Hclose" as "[Hclose _]".
        iMod ("Hclose" with "Hα") as "HP".
        iApply "HΦ'". done.
      + (* Complete the step we are eliminating *)
        iDestruct "Hclose" as "[_ Hclose]".
        iDestruct "Hcont" as (y) "[Hβ HΦ']".
        iMod ("Hclose" with "Hβ") as "HΦ".
        iApply "HΦ'". done.
  Qed.

  Lemma aacc1_aupd {TA' TB' : tele} E1 E1' E2 E3
        α β Φ
        (α' : TA' → PROP) P' (β' Φ' : TA' → TB' → PROP) :
    E1' ⊆ E1 →
    atomic1_update E1' E2 α β Φ ⊢
    (∀.. x, α x -∗ atomic1_acc E2 E3 α' (α x ∗ (atomic1_update E1' E2 α β Φ ={E1}=∗ P')) β'
            (λ.. x' y', (α x ∗ (atomic1_update E1' E2 α β Φ ={E1}=∗ Φ' x' y'))
                    ∨ ∃.. y, β x y ∗ (Φ x y ={E1}=∗ Φ' x' y'))) -∗
    atomic1_acc E1 E3 α' P' β' Φ'.
  Proof.
    iIntros (?) "Hupd Hstep". iApply (aacc1_aacc with "[Hupd] Hstep"); first done.
    iApply aupd1_aacc; done.
  Qed.

  Lemma aacc1_aupd_commit {TA' TB' : tele} E1 E1' E2 E3
        α β Φ
        (α' : TA' → PROP) P' (β' Φ' : TA' → TB' → PROP) :
    E1' ⊆ E1 →
    atomic1_update E1' E2 α β Φ ⊢
    (∀.. x, α x -∗ atomic1_acc E2 E3 α' (α x ∗ (atomic1_update E1' E2 α β Φ ={E1}=∗ P')) β'
            (λ.. x' y', ∃.. y, β x y ∗ (Φ x y ={E1}=∗ Φ' x' y'))) -∗
    atomic1_acc E1 E3 α' P' β' Φ'.
  Proof.
    iIntros (?) "Hupd Hstep". iApply (aacc1_aupd with "Hupd"); first done.
    iIntros (x) "Hα". iApply atomic1_acc_wand; last first.
    { iApply "Hstep". done. }
    (* FIXME: Using ssreflect rewrite does not work, see Coq bug #7773. *)
    iSplit; first by eauto. iIntros "!>" (??) "?". rewrite ->!tele_app_bind. by iRight.
  Qed.

  Lemma aacc1_aupd_abort {TA' TB' : tele} E1 E1' E2 E3
        α β Φ
        (α' : TA' → PROP) P' (β' Φ' : TA' → TB' → PROP) :
    E1' ⊆ E1 →
    atomic1_update E1' E2 α β Φ ⊢
    (∀.. x, α x -∗ atomic1_acc E2 E3 α' (α x ∗ (atomic1_update E1' E2 α β Φ ={E1}=∗ P')) β'
            (λ.. x' y', α x ∗ (atomic1_update E1' E2 α β Φ ={E1}=∗ Φ' x' y'))) -∗
    atomic1_acc E1 E3 α' P' β' Φ'.
  Proof.
    iIntros (?) "Hupd Hstep". iApply (aacc1_aupd with "Hupd"); first done.
    iIntros (x) "Hα". iApply atomic1_acc_wand; last first.
    { iApply "Hstep". done. }
    (* FIXME: Using ssreflect rewrite does not work, see Coq bug #7773. *)
    iSplit; first by eauto. iIntros "!>" (??) "?". rewrite ->!tele_app_bind. by iLeft.
  Qed.

End lemmas.

(** This adds a few TC instances that are not automatically inferred. *)
  Section atomic.
  Context `{BiFUpd PROP} {TA TB : tele}.
  Implicit Types (α : TA → PROP).
  Implicit Types (β Φ : TA → TB → PROP).

  Global Instance aacc1_proper Eo Ei :
    Proper (
      pointwise_relation TA (≡) ==>
      (≡) ==>
      pointwise_relation TA (pointwise_relation TB (≡)) ==>
      pointwise_relation TA (pointwise_relation TB (≡)) ==>
      (≡)
    ) (atomic1_acc (PROP:=PROP) Eo Ei).
  Proof. solve_proper. Qed.

  Global Instance aacc1_mono' Eo Ei :
    Proper (
      pointwise_relation TA (≡) ==>
      (⊢) ==>
      pointwise_relation TA (pointwise_relation TB (flip (⊢))) ==>
      pointwise_relation TA (pointwise_relation TB (⊢)) ==>
      (⊢)
    ) (atomic1_acc (PROP:=PROP) Eo Ei).
  Proof.
    intros α1 α2 Hα P1 P2 HP β1 β2 Hβ Φ1 Φ2 HΦ. rewrite/atomic1_acc.
    repeat f_equiv; by rewrite ?Hα ?Hβ ?HP.
  Qed.

  Global Instance aacc1_flip_mono' Eo Ei :
    Proper (
      pointwise_relation TA (≡) ==>
      flip (⊢) ==>
      pointwise_relation TA (pointwise_relation TB (⊢)) ==>
      pointwise_relation TA (pointwise_relation TB (flip (⊢))) ==>
      flip (⊢)
    ) (atomic1_acc (PROP:=PROP) Eo Ei).
  Proof. repeat intro. by rewrite -aacc1_mono'. Qed.

  Global Instance aupd1_proper Eo Ei :
    Proper (
      pointwise_relation TA (≡) ==>
      pointwise_relation TA (pointwise_relation TB (≡)) ==>
      pointwise_relation TA (pointwise_relation TB (≡)) ==>
      (≡)
    ) (atomic1_update (PROP:=PROP) Eo Ei).
  Proof.
    rewrite atomic1_update_eq /atomic1_update_def /atomic1_update_pre.
    solve_proper.
  Qed.

  Global Instance aupd1_mono' Eo Ei :
    Proper (
      pointwise_relation TA (≡) ==>
      pointwise_relation TA (pointwise_relation TB (flip (⊢))) ==>
      pointwise_relation TA (pointwise_relation TB (⊢)) ==>
      (⊢)
    ) (atomic1_update (PROP:=PROP) Eo Ei).
  Proof.
    rewrite atomic1_update_eq /atomic1_update_def /atomic1_update_pre.
    solve_proper.
  Qed.

  Global Instance aupd1_flip_mono' Eo Ei :
    Proper (
      pointwise_relation TA (≡) ==>
      pointwise_relation TA (pointwise_relation TB (⊢)) ==>
      pointwise_relation TA (pointwise_relation TB (flip (⊢))) ==>
      flip (⊢)
    ) (atomic1_update (PROP:=PROP) Eo Ei).
  Proof. repeat intro. by rewrite -aupd1_mono'. Qed.

  (* TODO: this is duplicated from bluerock.lib.aupd. This should be cleaned up
    once we unify AU/AC with AU1/AC1. *)
  (** Learn from an atomic precondition. (To use the bound variables
    [x], pick [P := ∃ x, P' x].) *)
  Lemma aupd1_obs_fupd P Eo Ei α β Φ :
    atomic1_update Eo Ei α β Φ ⊢
    (∀.. x, α x ={Ei}=∗ α x ∗ P) ={Eo}=∗ atomic1_update Eo Ei α β Φ ∗ P.
  Proof.
    iIntros "AU Obs". iMod "AU" as (x) "[Hα Close]".
    iMod ("Obs" with "Hα") as "[Hα $]". by iMod ("Close" with "Hα") as "$".
  Qed.
  Lemma aupd1_obs_wand P Eo Ei α β Φ :
    atomic1_update Eo Ei α β Φ ⊢
    (∀.. x, α x -∗ α x ∗ P) ={Eo}=∗ atomic1_update Eo Ei α β Φ ∗ P.
  Proof.
    iIntros "AU Obs". iApply (aupd1_obs_fupd with "AU [Obs]").
    iIntros (x) "Hα !>". by iApply "Obs".
  Qed.
  Lemma aupd1_obs P Eo Ei α β Φ :
    (∀.. x, α x ⊢ α x ∗ P) →
    atomic1_update Eo Ei α β Φ ⊢ |={Eo}=> atomic1_update Eo Ei α β Φ ∗ P.
  Proof.
    rewrite tforall_forall. iIntros (Hobs) "AU".
    iMod (aupd1_obs_wand P with "AU []") as "$"; auto.
    iIntros (x). iApply Hobs.
  Qed.
End atomic.

Theorem of_envs_alt' {PROP : bi} (Δ : envs PROP) :
  of_envs Δ ⊣⊢ (⌜envs_wf Δ⌝ ∧ □ [∧] env_intuitionistic Δ) ∗ [∗] env_spatial Δ.
Proof.
  rewrite of_envs_alt. iSplit; [iIntros "[$[$$]]" | iIntros "[[$$]$]"].
Qed.

(** The tactic [iAuIntro1] applies lemma [aupd1_aacc] to change an Iris
    proof mode goal [P := atomic1_update Eo Ei α β Φ] into [atomic1_acc Eo
    Ei α P β Φ]. *)
Section coq_tactic.
  Import coq_tactics.
  Context `{BiFUpd PROP} {TA TB : tele}.
  Implicit Types (α : TA → PROP).
  Implicit Types (β Φ : TA → TB → PROP).

  Lemma tac_aupd1_intro Γp Γs n α β Eo Ei Φ P :
    P = env_to_prop Γs →
    envs_entails (Envs Γp Γs n) (atomic1_acc Eo Ei α P β Φ) →
    envs_entails (Envs Γp Γs n) (atomic1_update Eo Ei α β Φ).
  Proof.
    intros ->. rewrite envs_entails_unseal of_envs_eq /=.
    setoid_rewrite env_to_prop_sound =>HAU.
    iIntros "[#P [#Q R]]". iStopProof. apply: aupd1_intro.
    iIntros "[#P Q]". iApply HAU.
    iSplit; first iDestruct "P" as "[$ _]".
    iSplit; last done. iClear "Q".
    iDestruct "P" as "[_ $]".
  Qed.
End coq_tactic.

Lemma test_before `{BiFUpd PROP} {TA TB : tele} Eo Ei α (β Φ : TA → TB → PROP) :
  atomic1_update Eo Ei α β Φ ⊢ atomic1_update Eo Ei α β Φ.
Proof. iIntros "AU". Fail iAuIntro. Abort.

Tactic Notation "iAuIntro1" :=
  iStartProof; eapply tac_aupd1_intro; [
    (* P = ...: make the P pretty *) reduction.pm_reflexivity
  | (* the new proof mode goal *) ].
Lemma test_after `{BiFUpd PROP} {TA TB : tele} Eo Ei α (β Φ : TA → TB → PROP) :
  atomic1_update Eo Ei α β Φ ⊢ atomic1_update Eo Ei α β Φ.
Proof. iIntros "AU". iAuIntro1. Abort.

Tactic Notation "iAaccIntro1" "with" constr(sel) :=
  iStartProof; lazymatch goal with
  | |- environments.envs_entails _ (@atomic1_acc ?PROP ?H ?TA ?TB ?Eo ?Ei ?α ?P ?β ?Φ) =>
    iApply (@aacc1_intro PROP H TA TB Eo Ei α P β Φ with sel);
    first try solve_ndisj; last iSplit
  | _ => fail "iAaccIntro1: Goal is not an atomic accessor"
  end.

(* From here on, prevent TC search from implicitly unfolding these. *)
#[global] Typeclasses Opaque atomic1_acc atomic1_update.

Section derived.
  Context `{BiFUpd PROP} {TA TB : tele}.
  Implicit Types (α : TA → PROP) (β Φ : TA → TB → PROP).

  (* Framing invariants into an AU/AC inner mask *)
  Lemma atomic_update1_frame_mask Ef Eo Ei α β Φ :
    Eo ## Ef ->
    atomic1_update Eo Ei α β Φ ⊢
    atomic1_update (Eo ∪ Ef) (Ei ∪ Ef) α β Φ.
  Proof.
    iIntros (Ho) "AU". iAuIntro1.
    iDestruct (aupd1_aacc with "AU") as "AC". rewrite/atomic1_acc.
    iApply fupd_mask_frame_r'; first done. iMod "AC" as (x) "(pre & cl)".
    iIntros "!>" (Hi). iExists x. iFrame "pre". iSplit.
    - iDestruct "cl" as "[abort _]". iIntros "pre".
      iApply fupd_mask_frame_r; first done. by iApply "abort".
    - iDestruct "cl" as "[_ commit]". iIntros "!>" (y) "post".
      iApply fupd_mask_frame_r; first done. by iApply "commit".
  Qed.

  Lemma atomic_update1_ppost_wand Eo Ei α β Φ1 Φ2 :
    atomic1_update Eo Ei α β Φ1 ⊢
    ▷ (∀.. x y, Φ1 x y -∗ Φ2 x y) -∗
    atomic1_update Eo Ei α β Φ2.
  Proof.
    iIntros "AU1 W". iAuIntro1; rewrite /atomic1_acc.
    iMod "AU1" as (x) "[A Cl]"; iExists _; iFrame "A"; iIntros "!>".
    iSplit. { iFrame "W". iIntros "A". iDestruct "Cl" as "[H _]". iApply ("H" with "A"). }
    iIntros "!> % B". iApply ("W" with "(Cl B)").
  Qed.

  (* Strictly weaker, but proven for consistency. *)
  Lemma atomic_update1_weak_ppost_wand Eo Ei α β Φ1 Φ2 :
    atomic1_update Eo Ei α β Φ1 ⊢
    (∀.. x y, Φ1 x y -∗ Φ2 x y) -∗
    atomic1_update Eo Ei α β Φ2.
  Proof. iIntros "AU1 W". iApply (atomic_update1_ppost_wand with "AU1 W"). Qed.
End derived.
