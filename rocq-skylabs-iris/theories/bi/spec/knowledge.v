(*
 * Copyright (C) 2020-2022 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bluerock.iris.extra.bi.prelude.
Require Import bluerock.iris.extra.bi.observe.
Require Import bluerock.iris.extra.proofmode.proofmode.

#[local] Set Primitive Projections.

(** Spec building block: knowledge *)

Class Knowledge {PROP : bi} (P : PROP) : Prop := {
  #[global] knowledge_persistent :: Persistent P;
  #[global] knowledge_affine     :: Affine P;
}.
Arguments Knowledge {_} _%_I.

Ltac solve_knowledge := solve [intros; split; apply _].

Section knowledge.
  Context {PROP : bi}.

  #[global] Instance knowledge_proper : Proper (equiv ==> iff) (@Knowledge PROP).
  Proof.
    intros P1 P2 HP. split; intros []. by split; rewrite -HP. by split; rewrite HP.
  Qed.

  #[global] Instance emp_knowledge : @Knowledge PROP emp.
  Proof. solve_knowledge. Qed.
End knowledge.

(** [KnowledgeN] states that predicate [P] taking [N] arguments is [Knowledge] *)
Notation Knowledge1 P := (∀ a, Knowledge (P a)).
Notation Knowledge2 P := (∀ a, Knowledge1 (P a)).
Notation Knowledge3 P := (∀ a, Knowledge2 (P a)).
Notation Knowledge4 P := (∀ a, Knowledge3 (P a)).
Notation Knowledge5 P := (∀ a, Knowledge4 (P a)).


(**
Persistent ghost state with agreement on one higher-order argument.
Compared to [Knowledge], we

- add [Contractive] and [LaterAgreeF1] to enable agreement lemmas.
*)
Class KnowLaterAgree1 {A : ofe} {PROP} `{!BiInternalEq PROP}
    (R : A -> PROP) : Prop := {
  #[global] know_later_agree_1_persistent :: Persistent1 R;
  #[global] know_later_agree_1_affine :: Affine1 R;
  #[global] know_later_agree_1_contractive :: Contractive R;
  #[global] know_later_agree_1_agree :: LaterAgree1 R;
}.
#[global] Hint Mode KnowLaterAgree1 - - - ! : typeclass_instances.

Section know_later_agree.
  Context {A : ofe} `{!BiInternalEq PROP}.
  Context (R : A -> PROP).
  Context `{!knowledge.KnowLaterAgree1 R}.
  #[local] Set Default Proof Using "Type*".
  #[local] Notation PROPO := (bi_ofeO PROP).

  #[global] Instance know_later_agree_1_ne : NonExpansive R.
  Proof. exact: contractive_ne. Qed.
  #[global] Instance know_later_agree_1_proper : Proper (equiv ==> equiv) R.
  Proof. exact: ne_proper. Qed.

  #[global] Instance know_later_agree_1_equivI a1 a2 :
    Observe2 (R a1 ≡@{PROPO} R a2) (R a1) (R a2).
  Proof.
    iIntros "R1 R2". iDestruct (observe_2 (▷ (_ ≡ _)) with "R1 R2") as "#Eq".
    rewrite (f_equivI_contractive R). auto.
  Qed.
End know_later_agree.
