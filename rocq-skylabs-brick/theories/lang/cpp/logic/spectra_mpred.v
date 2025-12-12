(*
 * Copyright (C) 2020-2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE file in the repository root for details.
 *)

(*** mpred's instance of the Spectra framework *)

Require Import bluerock.lang.cpp.cpp.

Require Export bluerock.iris.extra.base_logic.lib.spectra.
Require Import bluerock.lang.cpp.logic.mpred_prop.
Require Import bluerock.iris.extra.base_logic.invariants.

(** Conversion from Σ-dependent definitions to BI-dependent ones *)
#[local] Instance ΣG_G `{!cpp_logic ti Σ}
    (cfg : Compose.config) `{!ComposeN.Σ.G Σ cfg}
    : ComposeN.G (PROP:=mpredI) cfg := {|
  ComposeN.inGs := λ n, _ ;
|}.

#[global] Instance comp `{!cpp_logic ti Σ} `{!ComposeN.Σ.compose Σ}
    : ComposeN.compose (PROP:=mpredI) := {|
  ComposeN.fam := ComposeN.Σ.fam ;
  ComposeN.ings := ΣG_G _ ;
|}.

Definition bi_app `{!cpp_logic ti Σ} (a : App.Σ.app Σ) : App.app :=
  {| App.lts := a.(App.Σ.lts) |}.

#[global] Instance updater_WeaklyObjective `{!cpp_logic ti Σ}
    {app : App.Σ.app Σ} E γ :
  WeaklyObjective (Step.updater (bi_app app) E γ).
Proof. rewrite Step.updater_unseal /Step.updater_def /AuthSet.frag. apply _. Qed.

Section with_mpred.
  Context `{!cpp_logic ti Σ}.
  Context `{compΣ : !ComposeN.Σ.compose Σ}.

  #[global] Instance Decomp_WeaklyObjective γleft γup :
    WeaklyObjective (Decomp_def γleft γup).
  Proof. rewrite /Decomp_def/decomp_aux/AuthSet.auth /AuthSet.frag. apply _. Qed.

  Let inv_alloc_mpred :=
    (λ γ γup N E, inv_alloc N E (Decomp_def γ γup)).

  Definition alloc_decompose :=
    alloc_decompose_bi inv_alloc_mpred.

  (** * Top-level theorem for mpred *)
  Definition gen_decompose {R : refinement} :=
    gen_decompose_bi inv_alloc_mpred.

End with_mpred.
