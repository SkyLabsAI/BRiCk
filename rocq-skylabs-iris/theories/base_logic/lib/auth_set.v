(*
 * Copyright (C) 2021 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import stdpp.propset.
Require Import iris.base_logic.lib.own. (* for inG *)

Require Export bluerock.iris.extra.algebra.authset.
Require Import bluerock.iris.extra.bi.observe.
Require Import bluerock.iris.extra.bi.only_provable.
Require Import bluerock.iris.extra.bi.own.
Require Import bluerock.iris.extra.bi.prop_constraints.

Require Import bluerock.iris.extra.proofmode.proofmode.


Set Default Proof Using "Type".

(** * Spec building block: auth/frag propsets with weakening

  This file defines auth/frag tokens for propsets such that
  the following strengthening lemma holds:
  [[
     frag_upd γ s' s (sub : s' ⊆ s) : frag γ s ==∗ frag γ s'
  ]]
  One use is to relate code to an abstract model that permit internal choices,
  considering the model of a given implementation physical state as an element
  of the powerset of the abstract state.
  Pruning frag sets in this setting corresponds to resolving
  internal nondeterminism.

  The provided interface is:

    (* auth *)
    auth (γ : gname) (s : propset T) : mpred
    auth_exclusive γ s1 s2 : Observe2 False (auth γ s1) (auth γ s2)
    auth_timeless γ s : Timeless (auth γ s)

    (* frag *)
    frag (γ : gname) (s : propset T) : mpred
    frag_exclusive γ s1 s2 : Observe2 False (frag γ s1) (frag γ s2)
    frag_timeless γ s : Timeless (frag γ s)
    frag_upd γ s' s (sub : s' ⊆ s) : frag γ s ==∗ frag γ s'

    (* auth/frag properties *)
    frag γ s1 -∗ auth γ s2 ==∗ frag γ s3 ∗ auth γ s3
    frag_auth_sub γ s1 s2 : Observe2 [| s1 ⊆ s2 |] (frag γ s1) (auth γ s2)

    (* allocation *)
    alloc s : ⊢ |==> ∃ γ, frag γ s ∗ auth γ s

    (* derived *)
    auth_exact γ s := auth γ {[ s ]}
    frag_exact γ s := frag γ {[ s ]}
    frag_exact_auth_sub γ s1 s1_set :
      Observe2 [| s1 ∈ s1_set |] (frag_exact γ s1) (auth γ s1_set)
*)

Module AuthSet.
  Class G `{ Σ : gFunctors, T : Type } :=
    { #[global] auth_setG :: inG Σ (auth_setR T) }.
  Arguments G : clear implicits.

  Definition Σ T : gFunctors := #[ GFunctor (auth_setR T) ].

  #[global] Instance subG_Σ {Σ' T} : subG (Σ T) Σ' -> G Σ' T.
  Proof. solve_inG. Qed.

  Section with_authset.
    #[local] Set Default Proof Using "All".
    Context `{HasUsualOwn PROP (auth_setR T)}.

    Record gname := { _gname : iprop.gname }.

    Section with_logic.
      Definition auth (γ : gname) (s : propset T) : PROP :=
        own γ.(_gname) (AuthSet.auth s).
      #[global] Instance auth_proper (γ : gname) :
        Proper (equiv ==> equiv) (auth γ).
      Proof. move => x y E. apply: own_proper. by rewrite E. Qed.
      #[global] Instance auth_exclusive γ s1 s2 :
        Observe2 False (auth γ s1) (auth γ s2).
      Proof.
        iIntros "o1 o2"; iDestruct (own_valid_2 with "o1 o2") as "%val".
          by apply auth_set_auth_excl in val.
      Qed.
      #[global] Instance auth_timeless γ s : Timeless (auth γ s).
      Proof. apply: _. Qed.

      Definition frag (γ : gname) (s : propset T) : PROP :=
        own γ.(_gname) (AuthSet.frag s).
      #[global] Instance frag_proper (γ : gname) :
        Proper (equiv ==> equiv) (frag γ).
      Proof. move => x y E. apply: own_proper. by rewrite E. Qed.

      #[global] Instance frag_exclusive γ s1 s2 :
        Observe2 False (frag γ s1) (frag γ s2).
      Proof.
        iIntros "o1 o2"; iDestruct (own_valid_2 with "o1 o2") as "%val".
          by apply auth_set_frag_excl in val.
      Qed.
      #[global] Instance frag_timeless γ s : Timeless (frag γ s).
      Proof. apply: _. Qed.
      Lemma frag_upd γ s' s (sub : s' ⊆ s) : frag γ s ⊢ |==> frag γ s'.
      Proof.
        iIntros "o"; iMod (own_update with "o") as "H";
          [ by apply: auth_set_update_frag; apply: sub
          | iModIntro; iFrame ].
      Qed.
      Lemma frag_auth_upd γ s3 s1 s2 :
        frag γ s1 ⊢ auth γ s2 ==∗ frag γ s3 ∗ auth γ s3.
      Proof.
        iIntros "f a".
        iMod (own_update_2 (A:=auth_setR T) γ.(_gname)
                           (AuthSet.frag s1) (AuthSet.auth s2)
          with "f a") as "fa".
        { apply: (auth_set_update s3 s3); set_solver. }
        iModIntro. setoid_rewrite <-own_op; iApply "fa".
      Qed.
      #[global] Instance frag_auth_sub γ s1 s2 : Observe2 [| s1 ⊆ s2 |] (frag γ s1) (auth γ s2).
      Proof.
        iIntros "f a"; iDestruct (own_valid_2 with "f a") as "%val".
          by move: val; rewrite auth_set_valid_frag_auth => sub; iModIntro.
      Qed.

      (*allocation*)
      Lemma alloc (s : propset T) : ⊢ |==> ∃ γ, frag γ s ∗ auth γ s.
      Proof.
        iMod (own_alloc (A:=auth_setR T)
                        (AuthSet.frag s ⋅ AuthSet.auth s)) as "own".
        setoid_rewrite auth_set_valid_frag_auth; first by [].
        setoid_rewrite own_op. iDestruct "own" as (γ) "(f & a)".
        iModIntro. iExists {| _gname := γ |}. iFrame.
      Qed.

      (*derived*)
      Definition auth_exact γ s := auth γ {[ s ]}. (*#[global] Notation fails*)
      Definition frag_exact γ s := frag γ {[ s ]}.

      #[global] Instance auth_exact_timeless γ s : Timeless (auth_exact γ s).
      Proof. apply: _. Qed.
      #[global] Instance frag_exact_timeless γ s : Timeless (frag_exact γ s).
      Proof. apply: _. Qed.
      #[global] Instance frag_exact_auth_sub γ s1 s1_set :
        Observe2 [| s1 ∈ s1_set |] (frag_exact γ s1) (auth γ s1_set).
      Proof.
        iIntros "frag auth".
        iDestruct (frag_auth_sub γ {[ s1 ]} s1_set with "frag auth") as "#H".
        by rewrite elem_of_subseteq_singleton.
      Qed.
      #[global] Instance frag_exact_auth_exact γ s1 s2 :
        Observe2 [| s1 = s2 |] (frag_exact γ s1) (auth_exact γ s2).
      Proof.
        iIntros "frag auth".
        iDestruct (observe_2 [| _ ∈ _ |] with "frag auth") as %InS.
        iIntros "!# !%". set_solver.
      Qed.
    End with_logic.
  End with_authset.

  #[global] Hint Opaque auth frag auth_exact frag_exact
    : br_opacity typeclass_instances.
End AuthSet.
