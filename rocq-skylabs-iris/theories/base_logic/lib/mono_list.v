(*
 * Copyright (c) 2023 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(** * Well-typed ghost state for mono list.

Right now this has a rather limited yet simple interface: we have
- two [half γ s]'s that agree on the authoritative current list [s] who
  can only grow, and
- [snap γ s'] holds a snapshot [s'] that is always a prefix of [s].

It's easy to replace [half] with a fractional ownership.
*)
Require Import iris.algebra.lib.mono_list.

Require Import iris.base_logic.lib.own. (* for inG *)
Require Import bluerock.iris.extra.bi.observe.
Require Import bluerock.iris.extra.bi.only_provable.
Require Import bluerock.iris.extra.bi.own.
Require Import bluerock.iris.extra.bi.prop_constraints.

Require Import bluerock.iris.extra.bi.spec.knowledge.
Require Import bluerock.iris.extra.bi.spec.nary_classes.

Require Import iris.proofmode.tactics.

Module mono_list.

  Definition traceR (T : Type) := (mono_listR (leibnizO T)).

  Definition Σ (T : Type) : gFunctors := #[ GFunctor (traceR T)].

  Class G {Σ : gFunctors} {T : Type} := mkG { traceG : inG Σ (traceR T) }.
  #[global] Arguments G : clear implicits.
  #[global] Existing Instance traceG.

  #[global] Instance subG_Σ {Σ' T} : subG (Σ T) Σ' -> G Σ' T.
  Proof. solve_inG. Qed.

  Record gname := { _gname : iprop.gname }.

  Section with_logic.
    #[local] Set Default Proof Using "All".
    Context `{HasUsualOwn PROP (traceR T)}.

    Definition half (γ : gname) (s : list T) : PROP :=
      own γ.(_gname) (●ML{#(1/2)%Qp} (s : list (leibnizO _))).
    #[global] Instance half_timeless : Timeless2 half := _.

    Definition snap (γ : gname) (s : list T) : PROP :=
      own γ.(_gname) (◯ML (s : list (leibnizO _))).
    #[global] Instance snap_timeless : Timeless2 snap := _.
    #[global] Instance snap_persistent : Persistent2 snap := _.

    Lemma half_snap_fork γ s :
      half γ s ⊢ half γ s ∗ snap γ s.
    Proof. by rewrite -own_op -mono_list_auth_lb_op. Qed.

    Lemma half_agree γ : Agree1 (half γ).
    Proof.
      iIntros (s1 s2) "o1 o2".
      iDestruct (own_valid_2 with "o1 o2") as %[]%mono_list_auth_dfrac_op_valid_L.
      by iIntros "!>".
    Qed.

    Lemma half_snap_sub γ s s' :
      Observe2 [| s' `prefix_of` s |] (half γ s) (snap γ s').
    Proof.
      iIntros "o1 o2".
      iDestruct (own_valid_2 with "o1 o2") as %[]%mono_list_both_dfrac_valid_L.
      by iIntros "!>".
    Qed.

    Lemma half_update γ s' s (PRE: s `prefix_of` s') :
      half γ s ⊢ half γ s ==∗ half γ s' ∗ half γ s'.
    Proof.
      iIntros "o1 o2".
      iCombine "o1 o2" as "o".
      iMod (own_update with "o") as "o".
      { by apply mono_list_update. }
      iIntros "!>". by iDestruct "o" as "[$ $]".
    Qed.

    Lemma half_alloc s :
      ⊢ |==> ∃ γ, half γ s ∗ half γ s.
    Proof.
      iMod (own_alloc) as (γ) "o".
      { apply mono_list_auth_valid. }
      iIntros "!>". iExists ({| _gname := γ |}).
      iDestruct "o" as "[$ $]".
    Qed.
  End with_logic.
  #[global] Hint Opaque half snap : br_opacity typeclass_instances.
End mono_list.
