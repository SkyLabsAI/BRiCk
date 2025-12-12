(*
 * Copyright (c) 2021-2022 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Export iris.bi.lib.fractional.

Require Import bluerock.iris.extra.bi.prelude.
Require Import bluerock.iris.extra.bi.observe.
Require Import bluerock.iris.extra.proofmode.proofmode.

(** * Simple extensions to iris.bi.lib.fractional *)
(**
Overview:

- [Hint Extern] to case split goals

- Tactic [solve_as_frac] for solving [AsFractional]

- [FractionalN], [AsFractionalN], [AgreeF1], [LaterAgreeF1] notation to save typing

- Some properties of fractional predicates
*)

#[global] Hint Extern 100 (Fractional (fun a => match ?x with _ => _ end)) =>
  destruct x : typeclass_instances.

Ltac solve_as_frac := solve [intros; exact: Build_AsFractional].

(**
Do not extend this module. It exists for backwards compatibility.
*)
Module Export nary.
  (**
  [FractionalN] states that predicate [P] taking a fraction and then [N]
  arguments is [Fractional]
  *)
  Notation Fractional0 := Fractional (only parsing).
  Notation Fractional1 P := (∀ a, Fractional (fun q => P q a)).
  Notation Fractional2 P := (∀ a b, Fractional (fun q => P q a b)).
  Notation Fractional3 P := (∀ a b c, Fractional (fun q => P q a b c)).
  Notation Fractional4 P := (∀ a b c d, Fractional (fun q => P q a b c d)).
  Notation Fractional5 P := (∀ a b c d e, Fractional (fun q => P q a b c d e)).

  (** [AsFractionalN] informs the IPM about predicate [P] satisfying [FracitonalN P] *)
  Notation AsFractional0 P := (∀ q, AsFractional (P q) P q).
  Notation AsFractional1 P := (∀ q a, AsFractional (P q a) (fun q => P%I q a) q).
  Notation AsFractional2 P := (∀ q a b, AsFractional (P q a b) (fun q => P%I q a b) q).
  Notation AsFractional3 P := (∀ q a b c, AsFractional (P q a b c) (fun q => P%I q a b c) q).
  Notation AsFractional4 P := (∀ q a b c d, AsFractional (P q a b c d) (fun q => P%I q a b c d) q).
  Notation AsFractional5 P := (∀ q a b c d e, AsFractional (P q a b c d e) (fun q => P%I q a b c d e) q).

  (** [AgreeF1 P] states that [P q a] can only holds for one possible [a],
  regardless of the fraction [q]. *)
  Notation AgreeF1 P := (∀ (q1 q2 : Qp) a1 a2, Observe2 [| a1 = a2 |] (P q1 a1) (P q2 a2)).

  (** [LaterAgreeF1 P] is similar to [AgreeF1 P], but only provides equivalence
  under a later. This is typically used for higher-order agreement. *)
  Notation LaterAgreeF1 P :=
    (∀ (q1 q2 : Qp) a1 a2, Observe2 (▷ (a1 ≡ a2)) (P q1 a1) (P q2 a2)).
End nary.

Section with_bi.
  Context {PROP : bi}.

  #[global] Instance fractional_exist {A} (P : A → Qp → PROP)
    (Hfrac : ∀ oa, Fractional (P oa))
    (Hobs : ∀ a1 a2 q1 q2, Observe2 [| a1 = a2 |] (P a1 q1) (P a2 q2)) :
    Fractional (λ q, ∃ a : A, P a q)%I.
  Proof.
    intros q1 q2.
    rewrite -bi.exist_sep; last by intros; exact: observe_2_elim_pure.
    f_equiv=>oa. apply: fractional.
  Qed.

  (** This follows by unfolding, but that was surprising. *)
  Lemma fractional_dup (P : PROP) :
    (P ⊣⊢ P ∗ P) ->
    Fractional (λ _, P).
  Proof. by rewrite /Fractional. Qed.

  #[global] Instance fractional_ignore_exist (P : Qp -> PROP) {HcfP : Fractional0 P} :
    Fractional (λI _, ∃ q, P q).
  Proof.
    have ? : AsFractional0 P by solve_as_frac.
    apply fractional_dup. iSplit.
    { by iIntros "[% [$ $]]". }
    iIntros "[[% A] [% B]]". iCombine "A B" as "$".
  Qed.

  #[global] Instance big_sepL2_agreef1 {A C} {P : A -> Qp -> C -> PROP} xs ys1 ys2 (q1 q2 : Qp)
    `{∀ a, AgreeF1 (P a)} :
    Observe2 [| ys1 = ys2 |]
      ([∗ list] hpa;x ∈ xs;ys1, P hpa q1 x)
      ([∗ list] hpa;x ∈ xs;ys2, P hpa q2 x).
  Proof.
    apply observe_2_intro_only_provable.
    iIntros "YS1 YS2"; iInduction xs as [|x xs] "IH" forall (ys1 ys2);
      case: ys1 ys2 => [|y1 ys1] [|y2 ys2] //=; iRevert "YS1 YS2".
    iIntros "[Y1 YS1] [Y2 YS2]".
    iDestruct (observe_2_elim_pure (y1 = y2) with "Y1 Y2") as %<-.
    by iDestruct ("IH" with "YS1 YS2") as %<-.
  Qed.
End with_bi.
