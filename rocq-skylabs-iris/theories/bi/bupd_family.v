(*
 * Copyright (C) 2024-2025 BlueRock Security, Inc.
 * All rights reserved.
 *)

Require Import bluerock.prelude.finite.

Require Import bluerock.iris.extra.proofmode.proofmode.

Section with_prop.
  Context {PROP : bi} `{BiBUpd PROP} .
  Context {U T : Type}.

  Lemma bupd_family_base `{EqDecision U} (P : U -> T -> PROP) (us : list U)
    (c : if us is nil then T else unit) :
    (∀ u, ⊢ |==> ∃ γ : T, P u γ) ->
    NoDup us ->
    ⊢ |==> ∃ γs : U -> T, [∗list] id ∈ us, P id (γs id).
  Proof.
    intros Hupd.
    induction us as [|u us IH]; intros ND.
    { iIntros "!>". by iExists (fun _ => c). }
    iMod Hupd as (γ) "P".
    apply NoDup_cons in ND as [ND1 ND2].
    iMod IH as (γs') "Ps".
    { case_match; auto. } { done. }
    iIntros "!>".
    iExists (<[u:=γ]>γs').
    rewrite /= fn_lookup_insert. iFrame "P".
    iApply (big_sepL_mono with "Ps").
    intros k y IN%elem_of_list_lookup_2.
    rewrite fn_lookup_insert_ne; [done|].
    by intros ->.
  Qed.

  Lemma bupd_family `{Finite U} (P : U -> T -> PROP) :
    (∀ u, ⊢ |==> ∃ γ : T, P u γ) ->
    ⊢ |==> ∃ γs : U -> T, [∗list] id ∈ (enum U), P id (γs id).
  Proof.
    intros Hupd.
    destruct (enum_empty_dec U) as [[f ?] | [cf Henum]].
    - apply bupd_family_base.
      + case_match; done.
      + done.
      + apply NoDup_enum.
    - iModIntro.
      iExists (fun c => @False_rect _ (cf c)).
      by rewrite Henum.
  Qed.
End with_prop.

