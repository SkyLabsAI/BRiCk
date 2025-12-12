(**
 * Copyright (C) 2025 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *
 * This file is derived from code original to the GPFSL project. That
 * original code is
 *
 *  Copyright: GPFSL developers and contributors
 *
 * and used according to the following license.
 *
 *  SPDX-License-Identifier: BSD-3-Clause
 *
 * Original Code:
 * https://gitlab.mpi-sws.org/iris/gpfsl/-/blob/35a7c7df492237047d24d996d33f7f102f75e7c5/gpfsl/logic/na_invariants.v
 *
 * Original GPFSL License:
 * https://gitlab.mpi-sws.org/iris/gpfsl/-/blob/35a7c7df492237047d24d996d33f7f102f75e7c5/LICENSE
 *)

Require Import stdpp.fin_maps.

Require Import iris.algebra.functions.
Require Import iris.algebra.gmap.
Require Import iris.algebra.lib.excl_auth.
Require Import iris.algebra.lib.frac_auth.
Require Import iris.bi.monpred.

Require Import iris.base_logic.lib.na_invariants. (* << [na_inv_pool_name] *)
Require Import iris.proofmode.monpred.

Require Import bluerock.iris.extra.proofmode.proofmode.

Require Import bluerock.iris.extra.bi.only_provable.
Require Import bluerock.iris.extra.bi.invariants.
Require Import bluerock.iris.extra.bi.prop_constraints.
Require Import bluerock.iris.extra.bi.own.

(** * Thread-local NA invariants

As with Iris' non-atomic invariants, these NA invariants implement a
form of "multi-borrow". The predicate [na_inv] represents knowledge
that some resource _might_ be accessible for local (non-atomic) use,
while the predicate [na_own] tracks which of those resources are
currently accessible.

In contrast to Iris' non-atomic invariants, including the BI-generic version
in [bluerock.iris.extra.bi.na_invariants], these NA invariants are
_local_, meaning both [na_inv] and [na_own] depend, implicitly, on
the current thread.

This model is derived and generalized to arbitrary [monPred]
from the view-based version of GPFSL.
*)

Notation naEnableMapFunR I :=
  (discrete_funR (λ _ : positive, authUR (gmapUR positive (agreeR (leibnizO I))))).
Notation naEnableMapR I :=
  (excl_authR (leibnizO (gmap positive I))).

Section defs.
  Context `{I : biIndex} {PROP : bi}.
  Context `{!Ghostly PROP} `{!BiFUpd PROP}.
  Context `{!HasUsualOwn PROP (naEnableMapFunR I)}.
  Context `{!HasUsualOwn PROP (naEnableMapR I)}.

  Definition to_agree_map (m : gmap positive I)
      : (gmapUR positive (agreeR (leibnizO I))) :=
    to_agree <$> m.

  Definition to_ofe_funR (E : coPset) (Ts : positive → gmap positive I)
      : naEnableMapFunR I :=
    λ i, if decide (i ∈ E) then ● (to_agree_map (Ts i)) else ε.

  (* Thread-local na_own *)
  Definition na_own (p : na_inv_pool_name) (E : coPset) : monPred I PROP :=
    (∃ Ts, ⎡own p (to_ofe_funR E Ts)⎤ ∗
    (* ^^ we can use own in monPred if we have [HasOwn (monPred I PROP) _]
    from [HasOwn PROP _]. *)
    ∀ i, [∗map] s ∈ Ts i, monPred_in s)%I.

  (* Thread-local na_inv *)
  Definition na_inv (p : na_inv_pool_name) (N : namespace) (P : monPred I PROP)
      : monPred I PROP :=
    (∃ i (s : I) γ, ⌜i ∈ (↑N:coPset)⌝ ∗ monPred_in s ∗
    ⎡inv N (
      (* init case *)
      (P s ∗ own p (ε : naEnableMapFunR I) ∗ own γ (● None))
      ∨
      (* enabled *)
      (∃ k (s' : I), P s' ∗ ⌜s ⊑ s'⌝ ∗
        own p (discrete_fun_singleton i (◯ (to_agree_map {[k := s']}))) ∗
        own γ (● None))
      ∨
      (* disabled *)
      (∃ m,
        own p (discrete_fun_singleton i (● to_agree_map m)) ∗
        own γ (●E (m : leibnizO _)))
    )⎤)%I.

End defs.

Section props.
  Context `{I : biIndex} {PROP : bi}.
  Context `{!Ghostly PROP} `{!BiFUpd PROP}.
  Context `{!HasUsualOwn PROP (naEnableMapFunR I)}.
  Context `{!HasUsualOwn PROP (naEnableMapR I)}.

  #[global] Instance na_own_timeless `{!Timeless (emp%I : monPred I PROP)}
      p E : Timeless (na_own p E).
  Proof. rewrite /na_own; apply _. Qed.

  #[global] Instance na_inv_contractive `{!BiLaterContractive PROP}
      p N : Contractive (na_inv p N).
  Proof. rewrite /na_inv. solve_contractive. Qed.
  #[global] Instance na_inv_ne `{!BiLaterContractive PROP}
      p N : NonExpansive (na_inv p N).
  Proof. apply (contractive_ne _). Qed.
  #[global] Instance na_inv_proper `{!BiLaterContractive PROP}
      p N : Proper ((≡) ==> (≡)) (na_inv p N).
  Proof. apply (ne_proper _). Qed.

  #[global] Instance na_inv_persistent p N P : Persistent (na_inv p N P).
  Proof. rewrite /na_inv; apply _. Qed.
  #[global] Instance na_inv_affine `{!BiAffine PROP} p N P :
    Affine (na_inv p N P).
  Proof. rewrite /na_inv; apply _. Qed.

  Lemma na_alloc_strong (P : na_inv_pool_name → Prop) :
    pred_infinite P → ⊢ |==> ∃ p, ⌜P p⌝ ∗ na_own p ⊤.
  Proof.
    
    intros.
    rewrite /na_own.
    iDestruct (monPred_in_intro True%I with "[//]") as (s) "[HV _]".
    iMod (own_alloc_strong (PROP:=PROP)
            (to_ofe_funR ⊤ (λ _, {[1%positive := s]})) P) as (p HP) "Own".
    { done. }
    { intro i.
      by rewrite /to_ofe_funR /= auth_auth_valid /to_agree_map
            map_fmap_singleton singleton_valid. }
    iIntros "!>".
    iExists p. iSplitR. { by iIntros "!%". }
    iFrame "Own".
    iIntros (?). by rewrite big_sepM_singleton.
  Qed.

  Lemma na_own_disjoint p E1 E2 : na_own p E1 ⊢ na_own p E2 -∗ ⌜E1 ## E2⌝.
  Proof.
    rewrite /na_own. iIntros "H1 H2".
    iDestruct "H1" as (Ts1) "[H1 _]". iDestruct "H2" as (Ts2) "[H2 _]".
    iDestruct (own_valid_2 (PROP:=PROP) with "H1 H2") as %VALID.
    iIntros "!%" (i Hi1 Hi2).
    specialize (VALID i).
    rewrite /to_ofe_funR /= discrete_fun_lookup_op !decide_True in VALID; auto.
    by destruct VALID.
  Qed.

  Lemma na_own_union `{!BiAffine PROP} `{!BiPersistentlyForall PROP}
      tid E1 E2 :
    E1 ## E2 → na_own tid (E1 ∪ E2) ⊣⊢ na_own tid E1 ∗ na_own tid E2.
  Proof.
    intros DISJ. rewrite /na_own. iSplit.
    - iIntros "H". iDestruct "H" as (Ts) "[Hown #Hin]".
      rewrite -!(bi.exist_intro Ts). iFrame "Hin".
      rewrite -embed_sep -own_op
        (_:to_ofe_funR (E1 ∪ E2) Ts ≡ to_ofe_funR E1 Ts ⋅ to_ofe_funR E2 Ts) //.
      intros i. rewrite discrete_fun_lookup_op /to_ofe_funR. specialize (DISJ i).
      do 3 destruct decide; try set_solver; by rewrite ?right_id ?left_id.
    - iIntros "[H1 H2]".
      iDestruct "H1" as (Ts1) "[H1 #Hin1]". iDestruct "H2" as (Ts2) "[H2 #Hin2]".
      iExists (λ i, if decide (i ∈ E1) then Ts1 i else Ts2 i). iSplitL.
      + iCombine "H1 H2" as "H".
        rewrite (_:to_ofe_funR E1 Ts1 ⋅ to_ofe_funR E2 Ts2 ≡ _) //.
        intros i. rewrite discrete_fun_lookup_op /to_ofe_funR. specialize (DISJ i).
        do 3 destruct decide; try set_solver; by rewrite ?right_id ?left_id.
      + iIntros (i). destruct decide; [iApply "Hin1"|iApply "Hin2"].
  Qed.

  Lemma na_own_acc `{!BiAffine PROP} `{!BiPersistentlyForall PROP}
      E2 E1 tid :
    E2 ⊆ E1 → na_own tid E1 ⊢ na_own tid E2 ∗ (na_own tid E2 -∗ na_own tid E1).
  Proof.
    intros HF. assert (E1 = E2 ∪ (E1 ∖ E2)) as -> by exact: union_difference_L.
    rewrite na_own_union; last by set_solver+. iIntros "[$ $]". auto.
  Qed.

  (*
  This lemma is not available for arbitrary monPred.
  See bluerock.iris.extra.base_logic.monpred_na_invariants for the lemma for
  (P : monPred I (iProp Σ)).

  Lemma na_inv_alloc p E N P : ▷ P ={E}=∗ na_inv p N P.
  Proof. Abort.
  *)

  #[local] Lemma to_agree_map_valid (m : gmap positive I) k s' :
    ✓ (● to_agree_map m ⋅ ◯ to_agree_map {[k := s']}) ->
    m !! k = Some s'.
  Proof.
    intros [Hv VALID]%auth_both_valid_discrete.
    rewrite /to_agree_map fmap_insert fmap_empty singleton_included_l in Hv.
    destruct Hv as (y & Eqky & Eqy).
    have /to_agree_uninj [i' Hx] := lookup_valid_Some _ _ _ VALID Eqky.
    rewrite -Hx in Eqky.
    rewrite Some_included_total -{}Hx to_agree_included in Eqy.
    inversion Eqy. subst i'. clear y Eqy.
    move : Eqky.
    rewrite lookup_fmap. destruct (_ !! _); simpl.
    - rewrite (inj_iff Some) (inj_iff to_agree). by fold_leibniz=>->.
    - by inversion_clear 1 as [].
  Qed.

  (* TODO: misplaced *)
  Lemma monPred_in_intro_incl `{!BiAffine PROP} (j : I) (P : monPred I PROP) :
    monPred_in j ⊢ P -∗ ∃ i : I, monPred_in i ∧ ⌜j ⊑ i⌝ ∧ ⎡ P i ⎤.
  Proof.
    iIntros "In P". iCombine "In P" as "IP".
    by iDestruct (monPred_in_intro with "IP") as (i) "($ & %Le & $)".
  Qed.

  Lemma na_inv_acc
      `{!BiAffine PROP} `{!BiPersistentlyForall PROP}
      `{!BiBUpdFUpd PROP}
      `{!BiEmbedBUpd PROP (monPredI I PROP)}
      p E F N P :
    ↑N ⊆ E → ↑N ⊆ F →
    na_inv p N P ⊢ na_own p F ={E}=∗
    ▷ P ∗ na_own p (F∖↑N) ∗ (▷ P ∗ na_own p (F∖↑N) ={E}=∗ na_own p F).
  Proof.
    rewrite /na_inv. iIntros (??) "#Hnainv Htoks".
    iDestruct "Hnainv" as (i s γ) "(% & HinV & Hinv)".
    rewrite [F as X in na_own p X](union_difference_L (↑N) F) //.
    rewrite [X in (X ∪ _)](union_difference_L {[i]} (↑N)) ?na_own_union; [|set_solver..].

    iDestruct "Htoks" as "[[Htoki $] $]".
    iDestruct "Htoki" as (Ts) "[Hown #HinVs]".
    iInv N as "[HP|[HP|>Htoki]]" "Hclose"; last first.
    { (* cannot be disabled *)
      iDestruct "Htoki" as (m) "[Hown' _]".
      iDestruct (own_valid_2 (PROP:=PROP) with "Hown Hown'") as %Hv. specialize (Hv i).
      rewrite /= discrete_fun_lookup_op discrete_fun_lookup_singleton /to_ofe_funR
        decide_True // in Hv; [by destruct Hv|set_solver-]. }

    { (* enabled *)

      iDestruct "HP" as (k s') "(HP & >%Le & >HV' & >Hdis)".
      iDestruct (own_valid_2 (PROP:=PROP) with "Hown HV'") as %Hv. specialize (Hv i).
      rewrite /= discrete_fun_lookup_op discrete_fun_lookup_singleton /to_ofe_funR
        decide_True in Hv; [|set_solver].
      have HL := to_agree_map_valid _ _ _ Hv.

      iSpecialize ("HinVs" $! i).
      iDestruct (big_sepM_lookup _ _ _ _ HL with "HinVs") as "Hins".
      iDestruct (monPred_in_elim (▷ P)%I s' with "Hins [$HP]") as "$".
      iMod (own_update (PROP:=PROP) with "[$Hdis]") as "[Hdis1 Hdis2]".
      { by apply auth_update_alloc, (alloc_option_local_update (Excl (Ts i : leibnizO _))). }
      iMod ("Hclose" with "[Hown Hdis1]") as "_".
      { iNext. iRight. iRight.
        iExists (Ts i).
        rewrite (_: to_ofe_funR {[i]} Ts ≡ _); [by iFrame|].
        intros i'. rewrite /to_ofe_funR /discrete_fun_singleton /discrete_fun_insert.
        do 2 destruct decide; set_solver. }

      (* closing *)
      iIntros "!> [HP $]".
      iInv N as "[HP'|[HP'|>Htoki]]" "Hclose".
      { iDestruct "HP'" as "(_ & _ & >Hdis1)".
        iDestruct (own_valid_2 (PROP:=PROP) with "Hdis1 Hdis2")
          as %[Hv'%option_included _]%auth_both_valid_discrete.
        exfalso. naive_solver. }
      { iDestruct "HP'" as (??) "(_ & _ & _ & >Hdis1)".
        iDestruct (own_valid_2 (PROP:=PROP) with "Hdis1 Hdis2")
          as %[Hv'%option_included _]%auth_both_valid_discrete.
        exfalso. naive_solver. }

      iDestruct "Htoki" as (m) "[Hown Hdis1]".
      iDestruct (own_valid_2 (PROP:=PROP) with "Hdis1 Hdis2") as %EQVi%excl_auth_agree_L.
      subst m.

      iMod (own_update_2 (PROP:=PROP) with "Hdis1 Hdis2") as "Hdis".
      { apply auth_update_dealloc, delete_option_local_update, _. }
      iDestruct (monPred_in_intro_incl with "Hins HP ")
        as (s'') "(#HV'' & %Le' & HP)".

      destruct (fresh_inv_name (dom (Ts i)) N) as (i' & FR & ?).
      iMod (own_update (PROP:=PROP) with "Hown") as "[Hown1 Hown2]".
      { etrans.
        - apply discrete_fun_singleton_update, auth_update_alloc,
                (alloc_singleton_local_update _ i' (to_agree (s'' : leibnizO _)));
            last done.
          by rewrite /to_agree_map lookup_fmap fmap_None -not_elem_of_dom.
        - by rewrite -discrete_fun_singleton_op. }

      rewrite -fmap_insert -/(to_agree_map (<[i':=s'']>_)).

      iMod ("Hclose" with "[-Hown1]") as "_".
      - iRight. iLeft. iExists i', s''.
        rewrite monPred_at_later.
        iFrame. iNext. iSplitR "Hown2".
        + iIntros "!%". by etrans.
        + iClear "#". rewrite /to_agree_map fmap_insert fmap_empty. iFrame.
      - iIntros "!>".
        rewrite /na_own. iExists (λ _, <[i' := s'']>(Ts i)). iSplitL.
        + iApply (own_proper (PROP:=PROP) with "Hown1").
          intros i''. unfold discrete_fun_singleton, discrete_fun_insert, to_ofe_funR.
          do 2 destruct decide; set_solver.
        + iIntros (_). rewrite big_sepM_insert; [by iFrame "#"|].
          by apply not_elem_of_dom. }

    (* initialized *)
    iDestruct "HP" as "(HP & _ & >Hdis)".
    iDestruct (monPred_in_elim (▷ P)%I s with "HinV [HP]") as "$".
    { by rewrite monPred_at_later. }
    iMod (own_update (PROP:=PROP) with "Hdis") as "[Hdis1 Hdis2]".
    { by apply auth_update_alloc, (alloc_option_local_update (Excl ((Ts i) : leibnizO _))). }
    iMod ("Hclose" with "[Hown Hdis1]") as "_".
    { iNext. iRight. iRight.
      iExists (Ts i). rewrite (_:to_ofe_funR {[i]} Ts ≡ _); [by iFrame|].
      intros i'. rewrite /to_ofe_funR /discrete_fun_singleton /discrete_fun_insert.
      do 2 destruct decide; set_solver. }

    (* closing *)
    iIntros "!> [HP $]".
    iInv N as "[HP'|[HP'|>Htoki]]" "Hclose".
    { iDestruct "HP'" as "(_ & _ & >Hdis1)".
      iDestruct (own_valid_2 (PROP:=PROP) with "Hdis1 Hdis2")
        as %[Hv'%option_included _]%auth_both_valid_discrete.
      exfalso. naive_solver. }
    { iDestruct "HP'" as (??) "(_ & _ & _ & >Hdis1)".
      iDestruct (own_valid_2 (PROP:=PROP) with "Hdis1 Hdis2")
        as %[Hv'%option_included _]%auth_both_valid_discrete.
      exfalso. naive_solver. }

    iDestruct "Htoki" as (m) "[Hown Hdis1]".
    iDestruct (own_valid_2 (PROP:=PROP) with "Hdis1 Hdis2") as %EQVi%excl_auth_agree_L.
    subst m.
    iMod (own_update_2 (PROP:=PROP) with "Hdis1 Hdis2") as "Hdis".
    { apply auth_update_dealloc, delete_option_local_update, _. }
    iDestruct (monPred_in_intro_incl with "HinV HP")
      as (s') "(#HV'' & %Le' & HP)".

    destruct (fresh_inv_name (dom (Ts i)) N) as (i' & FR & ?).
    iMod (own_update (PROP:=PROP) with "Hown") as "[Hown1 Hown2]".
    { etrans.
      - apply discrete_fun_singleton_update, auth_update_alloc,
              (alloc_singleton_local_update _ i' (to_agree (s' : leibnizO _)));
          last done.
        by rewrite /to_agree_map lookup_fmap fmap_None -not_elem_of_dom.
      - by rewrite -discrete_fun_singleton_op. }

    rewrite -fmap_insert -/(to_agree_map (<[i':=s']>_)).

    iMod ("Hclose" with "[-Hown1]") as "_".
    - iRight. iLeft. iExists i', s'.
      rewrite monPred_at_later.
      iFrame (Le') "∗". iNext.
      iClear "#". rewrite /to_agree_map fmap_insert fmap_empty. iFrame.
    - iIntros "!>".
      rewrite /na_own. iExists (λ _, <[i' := s']>(Ts i)). iSplitL.
      + iApply (own_proper (PROP:=PROP) with "Hown1").
        intros i''. unfold discrete_fun_singleton, discrete_fun_insert, to_ofe_funR.
        do 2 destruct decide; set_solver.
      + iIntros (_). rewrite big_sepM_insert; [by iFrame "#"|].
        by apply not_elem_of_dom.
  Qed.

  (*
  This doesn't hold without a stronger property than (P ∗-∗ Q) that concerns
  the thread info.

  Lemma na_inv_iff : ∀ N P Q, na_inv N P |-- □ ▷ (P ∗-∗ Q) -* na_inv N Q.
  Proof. Abort.
  *)
End props.

#[global] Hint Opaque na_own na_inv : typeclass_instances br_opacity.
