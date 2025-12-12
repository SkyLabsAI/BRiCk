(*
 * Copyright (C) 2020 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *
 *
 * This file is derived from code original to the Iris project. That
 * original code is
 *
 *	Copyright Iris developers and contributors
 *
 * and used according to the following license.
 *
 *	SPDX-License-Identifier: BSD-3-Clause
 *
 * Original Code:
 * https://gitlab.mpi-sws.org/iris/iris/-/blob/8b5f7383202f19446c3f291050d4d21934a0b0af/theories/bi/lib/atomic.v
 *
 * Original Iris License:
 * https://gitlab.mpi-sws.org/iris/iris/-/blob/8b5f7383202f19446c3f291050d4d21934a0b0af/LICENSE-CODE
 *)
Require Import stdpp.coPset stdpp.namespaces.
Require Export iris.bi.bi iris.bi.updates.
Require Export bluerock.iris.extra.bi.laterable.
Require Import bluerock.iris.extra.bi.telescopes.
Require Import bluerock.iris.extra.proofmode.proofmode.
Set Default Proof Using "Type".

(** * Atomic commits *)
(** Atomic commits are atomic updates without abort. *)

Section definition.
  Context `{BiFUpd PROP} {TA TB : tele}.
  Implicit Types
    (Eo Ei : coPset) (* outer/inner masks *)
    (α : TA → PROP) (* atomic pre-condition *)
    (β : TA → TB → PROP) (* atomic post-condition *)
    (Φ : TA → TB → PROP) (* post-condition *)
  .

  (** commit_acc as the "introduction form" of atomic commit: an
      accessor. *)
  Definition commit_acc b Eo Ei α β Φ : PROP :=
    (|={Eo, Ei}=> ∃.. x, α x ∗ ▷?b (∀.. y, β x y ={Ei, Eo}=∗ Φ x y))%I.

  Lemma commit_acc_commit1_acc Eo Ei α β Φ :
    commit_acc false Eo Ei α β Φ -∗ commit_acc true Eo Ei α β Φ.
  Proof.
    rewrite /commit_acc.
    iIntros "AS". iMod "AS" as (x) "[Hα Hclose]".
    iModIntro. iExists x. iFrame "Hα".
    iIntros "!>" (y) "Hβ". iApply "Hclose". done.
  Qed.

  Lemma commit_acc_wand b Eo Ei α β Φ1 Φ2 :
    (∀.. x y, Φ1 x y -∗ Φ2 x y) -∗
    (commit_acc b Eo Ei α β Φ1 -∗ commit_acc b Eo Ei α β Φ2).
  Proof.
    iIntros "HP12 AS". iMod "AS" as (x) "[Hα Hclose]".
    iModIntro. iExists x. iFrame "Hα".
    iIntros "!>" (y) "Hβ". iApply "HP12". iApply "Hclose". done.
  Qed.

  Lemma commit_acc_mask b Eo Ed α β Φ :
    commit_acc b Eo (Eo∖Ed) α β Φ ⊣⊢ ∀ E, ⌜Eo ⊆ E⌝ → commit_acc b E (E∖Ed) α β Φ.
  Proof.
    iSplit; last first.
    { iIntros "Hstep". iApply ("Hstep" with "[% //]"). }
    iIntros "Hstep" (E HE).
    iApply (fupd_mask_frame_acc with "Hstep"); first done.
    iIntros "Hstep". iDestruct "Hstep" as (x) "[Hα Hclose]".
    iIntros "!> Hclose'".
    iExists x. iFrame.
    iIntros "!>" (y) "Hβ". iApply "Hclose'". iApply "Hclose". done.
  Qed.

  Lemma commit_acc_mask_weaken b Eo1 Eo2 Ei α β Φ :
    Eo1 ⊆ Eo2 →
    commit_acc b Eo1 Ei α β Φ -∗ commit_acc b Eo2 Ei α β Φ.
  Proof.
    iIntros (HE) "Hstep".
    iMod fupd_mask_subseteq as "Hclose1"; first done.
    iMod "Hstep" as (x) "[Hα Hclose2]". iIntros "!>". iExists x.
    iFrame. iIntros "!>" (y) "Hβ". iMod ("Hclose2" with "Hβ") as "$". done.
  Qed.

  (** Atomic commits *)
  Definition atomic_commit_def b Eo Ei α β Φ : PROP :=
    commit_acc b Eo Ei α β Φ.

End definition.

(** Seal it *)
Definition atomic_commit_aux : seal (@atomic_commit_def). Proof. by eexists. Qed.
Definition atomic_commit `{BiFUpd PROP} {TA TB : tele} := atomic_commit_aux.(unseal) PROP _ TA TB.
Definition atomic_commit_eq :
  @atomic_commit = @atomic_commit_def := atomic_commit_aux.(seal_eq).

Arguments commit_acc {PROP _ TA TB} b Eo Ei _ _ _ : simpl never, assert.
Arguments atomic_commit {PROP _ TA TB} b Eo Ei _ _ _ : simpl never.

(** Notation: Atomic commits *)
Notation "'AC' '<<' ∀ x1 .. xn , α '>>' @ Eo , Ei '<<' ∃ y1 .. yn , β , 'COMM' Φ '>>'" :=
  (atomic_commit (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
                 (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
                 false
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
   format "'[   ' 'AC'  '<<'  ∀  x1  ..  xn ,  α  '>>'  '/' @  Eo ,  Ei  '/' '[   ' '<<'  ∃  y1  ..  yn ,  β ,  '/' COMM  Φ  '>>' ']' ']'") : bi_scope.

Notation "'AC' '<<' ∀ x1 .. xn , α '>>' @ Eo , Ei '<<' β , 'COMM' Φ '>>'" :=
  (atomic_commit (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
                 (TB:=TeleO)
                 false
                 Eo Ei
                 (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn, α%I) ..)
                 (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn, tele_app (TT:=TeleO) β%I) .. )
                 (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn, tele_app (TT:=TeleO) Φ%I) .. )
  )
  (at level 20, Eo, Ei, α, β, Φ at level 200, x1 binder, xn binder,
   format "'[   ' 'AC'  '<<'  ∀  x1  ..  xn ,  α  '>>'  '/' @  Eo ,  Ei  '/' '[   ' '<<'  β ,  '/' COMM  Φ  '>>' ']' ']'") : bi_scope.

Notation "'AC' '<<' α '>>' @ Eo , Ei '<<' ∃ y1 .. yn , β , 'COMM' Φ '>>'" :=
  (atomic_commit (TA:=TeleO)
                 (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
                 false
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
   format "'[   ' 'AC'  '<<'  α  '>>'  '/' @  Eo ,  Ei  '/' '[   ' '<<'  ∃  y1  ..  yn ,  β ,  '/' COMM  Φ  '>>' ']' ']'") : bi_scope.

Notation "'AC' '<<' α '>>' @ Eo , Ei '<<' β , 'COMM' Φ '>>'" :=
  (atomic_commit (TA:=TeleO) (TB:=TeleO) false Eo Ei
                 (tele_app (TT:=TeleO) α%I)
                 (tele_app (TT:=TeleO) $ tele_app (TT:=TeleO) β%I)
                 (tele_app (TT:=TeleO) $ tele_app (TT:=TeleO) Φ%I)
  )
  (at level 20, Eo, Ei, α, β, Φ at level 200,
   format "'[   ' 'AC'  '<<'  α  '>>'  '/' @  Eo ,  Ei  '/' '[   ' '<<'  β ,  '/' COMM  Φ  '>>' ']' ']'") : bi_scope.

(** Notation: Commit accessors *)
Notation "'CACC' '<<' ∀ x1 .. xn , α '>>' @ Eo , Ei '<<' ∃ y1 .. yn , β , 'COMM' Φ '>>'" :=
  (commit_acc (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
              (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
              false
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
   format "'[     ' 'CACC'  '[   ' '<<'  ∀  x1  ..  xn ,  α  '>>'  ']' '/' @  Eo ,  Ei  '/' '[   ' '<<'  ∃  y1  ..  yn ,  β ,  '/' COMM  Φ  '>>' ']' ']'") : bi_scope.

Notation "'CACC' '<<' ∀ x1 .. xn , α '>>' @ Eo , Ei '<<' β , 'COMM' Φ '>>'" :=
  (commit_acc (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
              (TB:=TeleO)
              false
              Eo Ei
              (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                        λ x1, .. (λ xn, α%I) ..)
              (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                        λ x1, .. (λ xn, tele_app (TT:=TeleO) β%I) .. )
              (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                        λ x1, .. (λ xn, tele_app (TT:=TeleO) Φ%I) .. )
  )
  (at level 20, Eo, Ei, α, β, Φ at level 200, x1 binder, xn binder,
   format "'[     ' 'CACC'  '[   ' '<<'  ∀  x1  ..  xn ,  α  '>>'  ']' '/' @  Eo ,  Ei  '/' '[   ' '<<'  β ,  '/' COMM  Φ  '>>' ']' ']'") : bi_scope.

Notation "'CACC' '<<' α '>>' @ Eo , Ei '<<' ∃ y1 .. yn , β , 'COMM' Φ '>>'" :=
  (commit_acc (TA:=TeleO)
              (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
              false
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
   format "'[     ' 'CACC'  '[   ' '<<'  α  '>>'  ']' '/' @  Eo ,  Ei  '/' '[   ' '<<'  ∃  y1  ..  yn ,  β ,  '/' COMM  Φ  '>>' ']' ']'") : bi_scope.

Notation "'CACC' '<<' α '>>' @ Eo , Ei '<<' β , 'COMM' Φ '>>'" :=
  (commit_acc (TA:=TeleO)
              (TB:=TeleO)
              false
              Eo Ei
              (tele_app (TT:=TeleO) α%I)
                 (tele_app (TT:=TeleO) $ tele_app (TT:=TeleO) β%I)
                 (tele_app (TT:=TeleO) $ tele_app (TT:=TeleO) Φ%I)
  )
  (at level 20, Eo, Ei, α, β, Φ at level 200,
   format "'[     ' 'CACC'  '[   ' '<<'  α  '>>'  ']' '/' @  Eo ,  Ei  '/' '[   ' '<<'  β ,  '/' COMM  Φ  '>>' ']' ']'") : bi_scope.

(** Notation: Atomic commits with a step *)
Notation "'AC1' '<<' ∀ x1 .. xn , α '>>' @ Eo , Ei '<<' ∃ y1 .. yn , β , 'COMM' Φ '>>'" :=
  (atomic_commit (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
                 (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
                 true
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
   format "'[   ' 'AC1'  '<<'  ∀  x1  ..  xn ,  α  '>>'  '/' @  Eo ,  Ei  '/' '[   ' '<<'  ∃  y1  ..  yn ,  β ,  '/' COMM  Φ  '>>' ']' ']'") : bi_scope.

Notation "'AC1' '<<' ∀ x1 .. xn , α '>>' @ Eo , Ei '<<' β , 'COMM' Φ '>>'" :=
  (atomic_commit (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
                 (TB:=TeleO)
                 true
                 Eo Ei
                 (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn, α%I) ..)
                 (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn, tele_app (TT:=TeleO) β%I) .. )
                 (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn, tele_app (TT:=TeleO) Φ%I) .. )
  )
  (at level 20, Eo, Ei, α, β, Φ at level 200, x1 binder, xn binder,
   format "'[   ' 'AC1'  '<<'  ∀  x1  ..  xn ,  α  '>>'  '/' @  Eo ,  Ei  '/' '[   ' '<<'  β ,  '/' COMM  Φ  '>>' ']' ']'") : bi_scope.

Notation "'AC1' '<<' α '>>' @ Eo , Ei '<<' ∃ y1 .. yn , β , 'COMM' Φ '>>'" :=
  (atomic_commit (TA:=TeleO)
                 (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
                 true
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
   format "'[   ' 'AC1'  '<<'  α  '>>'  '/' @  Eo ,  Ei  '/' '[   ' '<<'  ∃  y1  ..  yn ,  β ,  '/' COMM  Φ  '>>' ']' ']'") : bi_scope.

Notation "'AC1' '<<' α '>>' @ Eo , Ei '<<' β , 'COMM' Φ '>>'" :=
  (atomic_commit (TA:=TeleO) (TB:=TeleO) true Eo Ei
                 (tele_app (TT:=TeleO) α%I)
                 (tele_app (TT:=TeleO) $ tele_app (TT:=TeleO) β%I)
                 (tele_app (TT:=TeleO) $ tele_app (TT:=TeleO) Φ%I)
  )
  (at level 20, Eo, Ei, α, β, Φ at level 200,
   format "'[   ' 'AC1'  '<<'  α  '>>'  '/' @  Eo ,  Ei  '/' '[   ' '<<'  β ,  '/' COMM  Φ  '>>' ']' ']'") : bi_scope.

(** Notation: Commit accessors with a step *)
Notation "'CACC1' '<<' ∀ x1 .. xn , α '>>' @ Eo , Ei '<<' ∃ y1 .. yn , β , 'COMM' Φ '>>'" :=
  (commit_acc (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
              (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
              true
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
   format "'[     ' 'CACC1'  '[   ' '<<'  ∀  x1  ..  xn ,  α  '>>'  ']' '/' @  Eo ,  Ei  '/' '[   ' '<<'  ∃  y1  ..  yn ,  β ,  '/' COMM  Φ  '>>' ']' ']'") : bi_scope.

Notation "'CACC1' '<<' ∀ x1 .. xn , α '>>' @ Eo , Ei '<<' β , 'COMM' Φ '>>'" :=
  (commit_acc (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
              (TB:=TeleO)
              true
              Eo Ei
              (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                        λ x1, .. (λ xn, α%I) ..)
              (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                        λ x1, .. (λ xn, tele_app (TT:=TeleO) β%I) .. )
              (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                        λ x1, .. (λ xn, tele_app (TT:=TeleO) Φ%I) .. )
  )
  (at level 20, Eo, Ei, α, β, Φ at level 200, x1 binder, xn binder,
   format "'[     ' 'CACC1'  '[   ' '<<'  ∀  x1  ..  xn ,  α  '>>'  ']' '/' @  Eo ,  Ei  '/' '[   ' '<<'  β ,  '/' COMM  Φ  '>>' ']' ']'") : bi_scope.

Notation "'CACC1' '<<' α '>>' @ Eo , Ei '<<' ∃ y1 .. yn , β , 'COMM' Φ '>>'" :=
  (commit_acc (TA:=TeleO)
              (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
              true
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
   format "'[     ' 'CACC1'  '[   ' '<<'  α  '>>'  ']' '/' @  Eo ,  Ei  '/' '[   ' '<<'  ∃  y1  ..  yn ,  β ,  '/' COMM  Φ  '>>' ']' ']'") : bi_scope.

Notation "'CACC1' '<<' α '>>' @ Eo , Ei '<<' β , 'COMM' Φ '>>'" :=
  (commit_acc (TA:=TeleO)
              (TB:=TeleO)
              true
              Eo Ei
              (tele_app (TT:=TeleO) α%I)
                 (tele_app (TT:=TeleO) $ tele_app (TT:=TeleO) β%I)
                 (tele_app (TT:=TeleO) $ tele_app (TT:=TeleO) Φ%I)
  )
  (at level 20, Eo, Ei, α, β, Φ at level 200,
   format "'[     ' 'CACC1'  '[   ' '<<'  α  '>>'  ']' '/' @  Eo ,  Ei  '/' '[   ' '<<'  β ,  '/' COMM  Φ  '>>' ']' ']'") : bi_scope.

(** Lemmas about AC *)
Section lemmas.
  Context `{BiFUpd PROP} {TA TB : tele}.
  Implicit Types (α : TA → PROP) (β Φ : TA → TB → PROP).

  (* Can't be in the section above as that fixes the parameters *)
  Global Instance commit_acc_ne b Eo Ei n :
    Proper (
        pointwise_relation TA (dist n) ==>
        pointwise_relation TA (pointwise_relation TB (dist n)) ==>
        pointwise_relation TA (pointwise_relation TB (dist n)) ==>
        dist n
    ) (commit_acc (PROP:=PROP) b Eo Ei).
  Proof. solve_proper. Qed.

  Global Instance commit_acc_proper b Eo Ei :
    Proper (
      pointwise_relation TA (≡) ==>
      pointwise_relation TA (pointwise_relation TB (≡)) ==>
      pointwise_relation TA (pointwise_relation TB (≡)) ==>
      (≡)
    ) (commit_acc (PROP:=PROP) b Eo Ei).
  Proof. solve_proper. Qed.

  Global Instance commit_acc_mono' b Eo Ei :
    Proper (
      pointwise_relation TA (≡) ==>
      pointwise_relation TA (pointwise_relation TB (flip (⊢))) ==>
      pointwise_relation TA (pointwise_relation TB (⊢)) ==>
      (⊢)
    ) (commit_acc (PROP:=PROP) b Eo Ei).
  Proof.
    intros α1 α2 Hα β1 β2 Hβ Φ1 Φ2 HΦ. rewrite/commit_acc.
    repeat f_equiv; by rewrite ?Hα ?Hβ.
  Qed.

  Global Instance commit_acc_flip_mono' b Eo Ei :
    Proper (
      pointwise_relation TA (≡) ==>
      pointwise_relation TA (pointwise_relation TB (⊢)) ==>
      pointwise_relation TA (pointwise_relation TB (flip (⊢))) ==>
      flip (⊢)
    ) (commit_acc (PROP:=PROP) b Eo Ei).
  Proof. repeat intro. by rewrite -commit_acc_mono'. Qed.

  Global Instance atomic_commit_ne b Eo Ei n :
    Proper (
        pointwise_relation TA (dist n) ==>
        pointwise_relation TA (pointwise_relation TB (dist n)) ==>
        pointwise_relation TA (pointwise_relation TB (dist n)) ==>
        dist n
    ) (atomic_commit (PROP:=PROP) b Eo Ei).
  Proof. rewrite atomic_commit_eq. solve_proper. Qed.

  Global Instance atomic_commit_proper b Eo Ei :
    Proper (
      pointwise_relation TA (≡) ==>
      pointwise_relation TA (pointwise_relation TB (≡)) ==>
      pointwise_relation TA (pointwise_relation TB (≡)) ==>
      (≡)
    ) (atomic_commit (PROP:=PROP) b Eo Ei).
  Proof. rewrite atomic_commit_eq. solve_proper. Qed.

  Global Instance atomic_commit_mono' b Eo Ei :
    Proper (
      pointwise_relation TA (≡) ==>
      pointwise_relation TA (pointwise_relation TB (flip (⊢))) ==>
      pointwise_relation TA (pointwise_relation TB (⊢)) ==>
      (⊢)
    ) (atomic_commit (PROP:=PROP) b Eo Ei).
  Proof. rewrite atomic_commit_eq. solve_proper. Qed.

  Global Instance atomic_commit_flip_mono' b Eo Ei :
    Proper (
      pointwise_relation TA (≡) ==>
      pointwise_relation TA (pointwise_relation TB (⊢)) ==>
      pointwise_relation TA (pointwise_relation TB (flip (⊢))) ==>
      flip (⊢)
    ) (atomic_commit (PROP:=PROP) b Eo Ei).
  Proof. repeat intro. by rewrite -atomic_commit_mono'. Qed.

  Lemma atomic_commit_atomic1_commit Eo Ei α β Φ :
    atomic_commit false Eo Ei α β Φ -∗ atomic_commit true Eo Ei α β Φ.
  Proof.
    rewrite atomic_commit_eq /atomic_commit_def /=.
    by iApply commit_acc_commit1_acc.
  Qed.

  Lemma atomic_commit_mask b Eo Ed α β Φ :
    atomic_commit b Eo (Eo∖Ed) α β Φ ⊣⊢ ∀ E, ⌜Eo ⊆ E⌝ → atomic_commit b E (E∖Ed) α β Φ.
  Proof.
    rewrite atomic_commit_eq /atomic_commit_def.
    by apply commit_acc_mask.
  Qed.

  Lemma atomic_commit_mask_weaken b Eo1 Eo2 Ei α β Φ :
    Eo1 ⊆ Eo2 →
    atomic_commit b Eo1 Ei α β Φ ⊢ atomic_commit b Eo2 Ei α β Φ.
  Proof.
    rewrite atomic_commit_eq /atomic_commit_def.
    iIntros (Heo) "HAU". by iApply commit_acc_mask_weaken.
  Qed.

  (** The elimination form: a commit accessor *)
  Lemma atomic_commit_elim b Eo Ei α β Φ :
    atomic_commit b Eo Ei α β Φ ⊢ commit_acc b Eo Ei α β Φ.
  Proof.
    rewrite atomic_commit_eq /atomic_commit_def. done.
  Qed.

  (* This lets you eliminate atomic commits with iMod. *)
  Global Instance elim_mod_atomic_commit φ b Eo Ei E α β Φ Q Q' :
    (∀ R, ElimModal φ false false (|={E,Ei}=> R) R Q Q') →
    ElimModal (φ ∧ Eo ⊆ E) false false
              (atomic_commit b Eo Ei α β Φ)
              (∃.. x, α x ∗ ▷?b (∀.. y, β x y ={Ei,E}=∗ Φ x y))
              Q Q'.
  Proof.
    intros ?. rewrite /ElimModal /= =>-[??]. iIntros "[AU Hcont]".
    iPoseProof (atomic_commit_elim with "AU") as "AC".
    iMod (commit_acc_mask_weaken with "AC"); first done.
    iApply "Hcont". done.
  Qed.

  Lemma atomic_commit_intro P Q b α β Eo Ei Φ :
    Affine P → Persistent P →
    (P ∗ Q -∗ commit_acc b Eo Ei α β Φ) →
    P ∗ Q -∗ atomic_commit b Eo Ei α β Φ.
  Proof.
    rewrite atomic_commit_eq /atomic_commit_def.
    iIntros (?? HAU) "[#HP HQ]".
    iApply HAU. by iFrame.
  Qed.

  Lemma commit_acc_intro b Eo Ei α β Φ :
    Ei ⊆ Eo → ⊢ (∀.. x, α x -∗
    ▷?b (∀.. y, β x y ={Eo}=∗ Φ x y) -∗
    commit_acc b Eo Ei α β Φ).
  Proof.
    iIntros (? x) "Hα Hclose".
    iMod fupd_mask_subseteq as "Hclose'"; last iModIntro; first set_solver.
    iExists x. iFrame.
    iIntros "!>" (y) "Hβ". iMod "Hclose'" as "_". iApply "Hclose". done.
  Qed.

  (* This lets you open invariants etc. when the goal is a commit accessor. *)
  Global Instance elim_acc_commit_acc {X} b E1 E2 Ei (α' β' : X → PROP) γ' α β Φ :
    ElimAcc (X:=X) True (fupd E1 E2) (fupd E2 E1) α' β' γ'
            (commit_acc b E1 Ei α β Φ)
            (λ x', commit_acc b E2 Ei α β
                (λ.. x y, β' x' ∗ (γ' x' -∗? Φ x y))
            )%I.
  Proof.
    rewrite /ElimAcc.
    iIntros (_) "Hinner >Hacc". iDestruct "Hacc" as (x') "[Hα' Hclose]".
    iMod ("Hinner" with "Hα'") as (x) "[Hα Hclose']".
    iMod (fupd_mask_subseteq) as "Hclose''"; last iModIntro; first done.
    iExists x. iFrame.
    iIntros "!>" (y) "Hβ". iMod "Hclose''" as "_".
    iMod ("Hclose'" with "Hβ") as "Hβ'".
    rewrite !tele_app_bind. iDestruct "Hβ'" as "[Hβ' HΦ]".
    iMod ("Hclose" with "Hβ'") as "Hγ'".
    iModIntro. destruct (γ' x'); iApply "HΦ"; done.
  Qed.

  (* Everything that fancy updates can eliminate without changing, commit
  accessors can eliminate as well.  This is a forwarding instance needed because
  commit_acc is opaque. *)
  Global Instance elim_modal_commit_acc p q φ P P' b Eo Ei α β Φ :
    (∀ Q, ElimModal φ p q P P' (|={Eo,Ei}=> Q) (|={Eo,Ei}=> Q)) →
    ElimModal φ p q P P'
              (commit_acc b Eo Ei α β Φ)
              (commit_acc b Eo Ei α β Φ).
  Proof. intros Helim. apply Helim. Qed.

  Lemma commit_acc_acc {TA' TB' : tele} b E1 E1' E2 E3
        α β Φ
        (α' : TA' → PROP) (β' Φ' : TA' → TB' → PROP) :
    E1' ⊆ E1 →
    commit_acc b E1' E2 α β Φ -∗
    (∀.. x, α x -∗ commit_acc b E2 E3 α' β'
            (λ.. x' y', ∃.. y, β x y ∗ (Φ x y ={E1}=∗ Φ' x' y'))) -∗
    commit_acc b E1 E3 α' β' Φ'.
  Proof.
    iIntros (?) "Hupd Hstep".
    iMod (commit_acc_mask_weaken with "Hupd") as (x) "[Hα Hclose]"; first done.
    iMod ("Hstep" with "Hα") as (x') "[Hα' Hclose']".
    iModIntro. iExists x'. iFrame "Hα'". iIntros "!>" (y') "Hβ'".
    iMod ("Hclose'" with "Hβ'") as "Hcont".
    (* FIXME: Using ssreflect rewrite does not work, see Coq bug #7773. *)
    rewrite ->!tele_app_bind.
    iDestruct "Hcont" as (y) "[Hβ HΦ']".
    iMod ("Hclose" with "Hβ") as "HΦ".
    iApply "HΦ'". done.
  Qed.

  Lemma commit_acc_commit {TA' TB' : tele} b E1 E1' E2 E3
        α β Φ
        (α' : TA' → PROP) (β' Φ' : TA' → TB' → PROP) :
    E1' ⊆ E1 →
    atomic_commit b E1' E2 α β Φ -∗
    (∀.. x, α x -∗ commit_acc b E2 E3 α' β'
            (λ.. x' y', ∃.. y, β x y ∗ (Φ x y ={E1}=∗ Φ' x' y'))) -∗
    commit_acc b E1 E3 α' β' Φ'.
  Proof.
    iIntros (?) "Hupd Hstep". iApply (commit_acc_acc with "[Hupd] Hstep"); first done.
    iApply atomic_commit_elim. done.
  Qed.

End lemmas.

(** ProofMode support for atomic commits *)
Section proof_mode.
  Import coq_tactics.
  Context `{BiFUpd PROP} {TA TB : tele}.
  Implicit Types (α : TA → PROP) (β Φ : TA → TB → PROP).

  Lemma tac_atomic_commit_intro Γp Γs n b α β Eo Ei Φ :
    envs_entails (Envs Γp Γs n) (commit_acc b Eo Ei α β Φ) →
    envs_entails (Envs Γp Γs n) (atomic_commit b Eo Ei α β Φ).
  Proof.
    by rewrite atomic_commit_eq /atomic_commit_def.
  Qed.
End proof_mode.

(** Now the coq-level tactics *)

Tactic Notation "iAcIntro" :=
  iStartProof; eapply tac_atomic_commit_intro.
Tactic Notation "iCaccIntro" "with" constr(sel) :=
  iStartProof; lazymatch goal with
  | |- environments.envs_entails _ (@commit_acc ?PROP ?H ?TA ?TB ?b ?Eo ?Ei ?α ?β ?Φ) =>
    iApply (@commit_acc_intro PROP H TA TB b Eo Ei α β Φ with sel);
    first try solve_ndisj
  | _ => fail "iCaccIntro: Goal is not an atomic commit accessor"
  end.

(* From here on, prevent TC search from implicitly unfolding these. *)
#[global] Typeclasses Opaque commit_acc atomic_commit.

Section derived.
  Context `{BiFUpd PROP} {TA TB : tele}.
  Implicit Types (α : TA → PROP) (β Φ : TA → TB → PROP).

  (** Framing invariants into an AC mask
  This is the kind of framing we need when we are given an AU/AC
  with masks [top\E, ∅] and we want an AU/AC with masks [(top\E) ∪ Ef, Ef].
  Such adjustments let us, e.g., open an AC and then an invariant in Ef. *)
  Lemma atomic_commit_frame_mask Ef b Eo Ei α β Φ :
    Eo ## Ef ->
    atomic_commit b Eo Ei α β Φ ⊢
    atomic_commit b (Eo ∪ Ef) (Ei ∪ Ef) α β Φ.
  Proof.
    iIntros (Ho) "AC". iAcIntro. rewrite/commit_acc.
    iApply fupd_mask_frame_r'; first done. iMod "AC" as (x) "(pre & cl)".
    iIntros "!>" (Hi). iExists x. iFrame "pre".
    iIntros "!>" (y) "post".
    iApply fupd_mask_frame_r; first done. by iApply "cl".
  Qed.

  (* ppost = (thread-)private postcondition, as opposed to the public or
  _atomic_ postcondition. *)
  Lemma atomic_commit1_ppost_wand Eo Ei α β Φ1 Φ2 :
    atomic_commit true Eo Ei α β Φ1 ⊢
    ▷ (∀.. x y, Φ1 x y -∗ Φ2 x y) -∗
    atomic_commit true Eo Ei α β Φ2.
  Proof.
    iIntros "AC1 W". iAcIntro; rewrite /commit_acc/=.
    iMod "AC1" as (x) "[A Cl] /=".
    iExists _; iFrame "A". iIntros "!> !> % B".
    iApply ("W" with "(Cl B)").
  Qed.

  Lemma atomic_commit1_weak_ppost_wand Eo Ei α β Φ1 Φ2 :
    atomic_commit true Eo Ei α β Φ1 ⊢
    (∀.. x y, Φ1 x y -∗ Φ2 x y) -∗
    atomic_commit true Eo Ei α β Φ2.
  Proof. iIntros "AC1 W". iApply (atomic_commit1_ppost_wand with "AC1 W"). Qed.

  (* This proof is almost a duplicate of [atomic_commit1_ppost_wand], but due to *)
  (* the different modalities, for simplicity we prefer duplicating it rather than *)
  (* doing conditional modality reasoning using [▷?b □?(negb b)] and trying to *)
  (* extend [iAc{1,}Intro] for this scenario. *)
  Lemma atomic_commit_ppost_wand Eo Ei α β Φ1 Φ2 :
    atomic_commit false Eo Ei α β Φ1 ⊢
    (∀.. x y, Φ1 x y -∗ Φ2 x y) -∗
    atomic_commit false Eo Ei α β Φ2.
  Proof.
    iIntros "AC1 W". iAcIntro; rewrite /commit_acc/=.
    iMod "AC1" as (x) "[A Cl]".
    iExists _; iFrame "A". iIntros "!> % B".
    iApply ("W" with "(Cl B)").
  Qed.
End derived.
