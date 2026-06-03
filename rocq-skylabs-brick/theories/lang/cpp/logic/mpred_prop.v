(*
 * Copyright (C) 2021 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE file in the repository root for details.
 *)

(** * Mpred satisfies Ghostly and HasUsualOwn

Mpred instances of the PROP constraint bundles defined in
lang/bi/prop_constraints.v

*)

Require Import iris.bi.monpred.
Require Import skylabs.iris.extra.base_logic.own_instances.
Require Import skylabs.iris.extra.bi.prop_constraints.
Require Import skylabs.lang.cpp.logic.mpred.

Section with_Σ.
  Context {ti : biIndex} {Σ : gFunctors}.

  #[global] Instance mpred_ghostly : Ghostly mpredI :=
    {| ghostly_bibupd := _
    ; ghostly_embed := _ |}.

  #[global] Instance mpred_has_usual_own `{T : cmra, hasG : !inG Σ T }
    : HasUsualOwn mpredI T :=
    {| has_usual_own_own := _
    ; has_usual_own_upd := _
    ; has_usual_own_valid := _ |}.
End with_Σ.
