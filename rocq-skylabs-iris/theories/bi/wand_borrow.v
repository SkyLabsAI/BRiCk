(*
 * Copyright (C) 2021 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bluerock.iris.extra.bi.prelude.
Require Import bluerock.iris.extra.bi.observe.
Require Import bluerock.iris.extra.proofmode.proofmode.
Import ChargeNotation.

(** Simple, read-only accessor. *)
Reserved Notation "P '-borrow-*' Q"
  (at level 60, right associativity, format "'[' P  '/' '-borrow-*'  Q ']'").

(** Sealing avoids potentially over-aggressive reductions by [simpl].
The alternative of using notation can duplicate
large terms, which can be expensive. Moreover, an only parsing
notation wouldn't be very easy on the eye. *)
Definition wand_borrow_def {PROP : bi} (P Q : PROP) : PROP :=
  P -* (Q ** (Q -* P)).	(** The RHS is [borrow_from P Q] from [pred_utils]. *)
Definition wand_borrow_aux : seal (@wand_borrow_def). Proof. by eexists. Qed.
Definition wand_borrow := wand_borrow_aux.(unseal).
Definition wand_borrow_eq : @wand_borrow = _ := wand_borrow_aux.(seal_eq).
#[global] Arguments wand_borrow {_} (_ _)%_I : assert.
#[global] Hint Opaque wand_borrow : typeclass_instances.

Notation "P '-borrow-*' Q" := (wand_borrow P Q) : bi_scope.

Section theory.
  Context {PROP : bi}.
  Implicit Types P Q R : PROP.

  #[global] Instance wand_borrow_ne : NonExpansive2 (@wand_borrow PROP).
  Proof. rewrite wand_borrow_eq. solve_proper. Qed.
  #[global] Instance wand_borrow_proper :
    Proper (equiv ==> equiv ==> equiv) (@wand_borrow PROP).
  Proof. rewrite wand_borrow_eq. solve_proper. Qed.
  #[global] Instance wand_borrow_mono :
    Proper ((≡@{PROP}) ==> (≡) ==> (⊢)) wand_borrow.
  Proof. intros P1 P2 HP Q1 Q2 HQ. by rewrite HP HQ. Qed.
  #[global] Instance wand_borrow_flip_mono :
    Proper ((≡@{PROP}) ==> (≡) ==> flip (⊢)) wand_borrow.
  Proof. repeat intro. by apply wand_borrow_mono. Qed.

  Lemma wand_borrow_spec P Q : P -borrow-* Q -|- P -* (Q ** (Q -* P)).
  Proof. by rewrite wand_borrow_eq. Qed.

  Lemma False_wand_borrow P : (False -borrow-* P) -|- True.
  Proof. by rewrite wand_borrow_spec bi.False_wand. Qed.

  Lemma wand_borrow_refl P : |-- P -borrow-* P.
  Proof. rewrite wand_borrow_eq. iIntros "$". by iIntros "$". Qed.

  Lemma wand_borrow_trans P Q R :
    (P -borrow-* Q) ** (Q -borrow-* R) |-- P -borrow-* R.
  Proof.
    rewrite wand_borrow_eq. iIntros "[PQ QR] P".
    iDestruct ("PQ" with "P") as "[Q QP]".
    iDestruct ("QR" with "Q") as "[$ RQ]".
    iIntros "R". iApply "QP". by iApply "RQ".
  Qed.

  #[global] Instance wand_borrow_obs P Q R :
    Observe R Q -> Observe2 R (P -borrow-* Q) P.
  Proof.
    rewrite wand_borrow_eq.
    iIntros (?) "PQ P". iDestruct ("PQ" with "P") as "[Q _]".
    iApply (observe with "Q").
  Qed.

  (** Recover some of what we lost by sealing. *)
  Section proofmode.
    Lemma test_before P Q : P -borrow-* Q |-- P -* Q.
    Proof. iIntros "PQ P". Fail iDestruct ("PQ" with "P") as "[$ close]". Abort.
    Lemma test_before P Q : □ (P -borrow-* Q) |-- P -* Q.
    Proof. iIntros "#PQ P". Fail iDestruct ("PQ" with "P") as "[$ close]". Abort.

    #[global] Instance into_wand_wand_borrow p P Q :
      IntoWand p false (P -borrow-* Q) P (Q ** (Q -* P)).
    Proof.
      rewrite/IntoWand wand_borrow_spec. by rewrite bi.intuitionistically_if_elim.
    Qed.

    Lemma test_after P Q : P -borrow-* Q |-- P -* Q.
    Proof. iIntros "PQ P". iDestruct ("PQ" with "P") as "[$ close]". Abort.
    Lemma test_after P Q : □ (P -borrow-* Q) |-- P -* Q.
    Proof. iIntros "#PQ P". iDestruct ("PQ" with "P") as "[$ close]". Abort.

    Lemma test_before P Q : |-- P -borrow-* Q.
    Proof. Fail iIntros "P". Abort.

    #[global] Instance from_wand_wand_borrow P Q :
      FromWand (P -borrow-* Q) P (Q ** (Q -* P)).
    Proof. by rewrite/FromWand wand_borrow_spec. Qed.

    Lemma test_after P Q : |-- P -borrow-* Q.
    Proof. iIntros "P". Abort.

  End proofmode.

End theory.
