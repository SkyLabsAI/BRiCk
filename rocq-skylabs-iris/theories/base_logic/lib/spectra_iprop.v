(*
 * Copyright (C) 2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(*** iProp's instance of the Spectra framework *)

Require Import bluerock.iris.extra.base_logic.lib.spectra.
Require Import bluerock.iris.extra.base_logic.iprop_prop.

Require Import bluerock.iris.extra.bi.invariants.
Require Import bluerock.iris.extra.base_logic.iprop_invariants.

(** Conversion from Σ-dependent definitions to BI-dependent ones *)
#[local] Instance ΣG_G {Σ : gFunctors}
    (cfg : Compose.config) `{!ComposeN.Σ.G Σ cfg}
    : ComposeN.G (PROP:=iPropI Σ) cfg := {|
  ComposeN.inGs := λ n, _ ;
|}.

#[global] Instance comp {Σ : gFunctors} `{!ComposeN.Σ.compose Σ}
    : ComposeN.compose (PROP:=iPropI Σ) := {|
  ComposeN.fam := ComposeN.Σ.fam ;
  ComposeN.ings := ΣG_G _ ;
|}.

(*** Decomposition for iProp *)
Section with_iprop.
  Context {Σ : gFunctors}.
  Context `{!invGS Σ}.
  Context `{compΣ : !ComposeN.Σ.compose Σ}.

  Let inv_alloc_iprop :=
    (λ γ γup N E, inv_alloc N E (Decomp_def γ γup)).

  Definition alloc_decompose :=
    alloc_decompose_bi inv_alloc_iprop.

  (** * Top-level theorem for iProp *)
  Definition gen_decompose_iprop {R : refinement} :=
    gen_decompose_bi inv_alloc_iprop.
End with_iprop.
