(*
 * Copyright (c) 2022-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Export stdpp.fin_map_dom.
Require Import skylabs.prelude.base.
Require Import skylabs.prelude.fin_maps.
Require Import skylabs.prelude.fin_sets.

Section fin_map_dom.
  Context `{FMD : FinMapDom K M D}.
  Context {A : Type}.
  Implicit Type (m : M A).

  Lemma elem_of_map_to_list_dom m k v :
    (k, v) ∈ map_to_list m → k ∈ dom m.
  Proof using FMD. move=> /elem_of_map_to_list. apply elem_of_dom_2. Qed.

  (* Named after stdpp's [lookup_weaken_*]. *)

  Lemma lookup_weaken_elem_of_dom m1 m2 i :
    i ∈ dom m1 → m1 ⊆ m2 → m1 !! i = m2 !! i.
  Proof using FMD.
    intros [a1 Hl1]%elem_of_dom Hsub.
    rewrite map_subseteq_spec in Hsub.
    by rewrite (Hsub _ _ Hl1).
  Qed.

  Lemma lookup_total_weaken_elem_of_dom `{Inhabited A} m1 m2 i :
    i ∈ dom m1 → m1 ⊆ m2 → m1 !!! i = m2 !!! i.
  Proof using FMD.
    intros Hin Hsub; apply (inj Some).
    rewrite -!lookup_lookup_total_dom //; last exact /(subseteq_dom _ _ Hsub) /Hin.
    exact: lookup_weaken_elem_of_dom.
  Qed.
End fin_map_dom.
