(*
 * Copyright (C) 2020-21 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *
*)
Require Export iris.bi.lib.laterable.
Require Import iris.bi.monpred.
Require Import bluerock.iris.extra.proofmode.proofmode.
Set Default Proof Using "Type".

(** Replace the TC instance [big_sepL_laterable] with a version that
    does not assume [Timeless emp] when the list is empty. *)

#[global] Remove Hints big_sepL_laterable : typeclass_instances.

Class ListNonEmpty {A} (l : list A) : Prop := list_non_empty : l ≠ nil.
#[global] Hint Mode ListNonEmpty - ! : typeclass_instances.
#[global] Instance cons_non_empty {A} (x : A) l : ListNonEmpty (x :: l).
Proof. done. Qed.

Section laterable.
  Context {PROP : bi}.
  Implicit Types P : PROP.
  Implicit Types Ps : list PROP.

  #[global] Instance big_sepL_laterable Ps :
    TCOr (ListNonEmpty Ps) (Timeless (PROP:=PROP) emp) →
    TCForall Laterable Ps →
    Laterable ([∗] Ps).
  Proof.
    destruct 1; last exact: big_sepL_laterable.
    induction 1 as [|P Ps]; first done.
    simpl. destruct Ps as [|Ps].
    - rewrite big_sepL_nil right_id. apply _.
    - apply _.
  Qed.
End laterable.

(** Some [Laterable] instances *)
Section laterable.
  Context {PROP : bi}.
  Implicit Types P Q : PROP.

  #[global] Instance or_laterable P Q :
    Laterable P → Laterable Q → Laterable (P ∨ Q).
  Proof.
    rewrite/Laterable=>HP HQ. iDestruct 1 as "[P|Q]".
    - iDestruct (HP with "P") as (P') "[P' #close]".
      iExists P'. iFrame "P'". iIntros "!> P'". iLeft. iApply ("close" with "P'").
    - iDestruct (HQ with "Q") as (Q') "[Q' #close]".
      iExists Q'. iFrame "Q'". iIntros "!> Q'". iRight. iApply ("close" with "Q'").
  Qed.
End laterable.

Section monpred.
  Context {I : biIndex} {PROP : bi}.
  Local Notation monPred := (monPred I PROP).
  Implicit Types i : I.
  Implicit Types P : monPred.

  #[global] Instance monPred_at_laterable p P :
    Laterable P → Laterable (monPred_at P p).
  Proof.
    rewrite/Laterable=>-[HP]. rewrite ->(HP p). clear HP.
    rewrite monPred_at_exist. iDestruct 1 as (P') "P".
    rewrite monPred_at_sep monPred_at_intuitionistically.
    iDestruct "P" as "[P #close]".
    iExists (monPred_at P' p). rewrite monPred_at_later. iFrame "P".
    rewrite monPred_wand_force monPred_at_later monPred_at_except_0. iFrame "close".
  Qed.
End monpred.
