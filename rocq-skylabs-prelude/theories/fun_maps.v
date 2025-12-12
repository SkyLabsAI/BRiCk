(*
 * Copyright (c) 2021-2025 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import Stdlib.Logic.FunctionalExtensionality.
Require Import bluerock.prelude.base.
Require Import bluerock.prelude.finite.
Require Import bluerock.prelude.gmap.

Notation map_to_fun m := (m !!!.) (only parsing).
Definition _map_to_fun {M K A} `{LookupTotal K A (M A)} (m : M A) : K -> A :=
  map_to_fun m.
Definition fun_to_map {M K A} `{Finite K} `{Empty (M A)} `{PartialAlter K A (M A)}
    (f : K -> A) : M A :=
  list_to_map $ (λ k, (k, f k)) <$> enum K.

Section map_from_finite.
  Context {K V : Type} {M} `{Finite K} `{FinMap K M}.
  Implicit Types (f : K -> V) (m : M V).
  Notation fun_to_map := (fun_to_map (M := M)).
  #[local] Set Default Proof Using "Type*".

  Lemma lookup_fun_to_map f k :
    fun_to_map f !! k = Some (f k).
  Proof.
    apply elem_of_list_to_map; last set_solver.
    apply NoDup_fmap_fst, NoDup_fmap, NoDup_enum; first set_solver.
    by intros ?? [= ->].
  Qed.

  Section map_from_finite_inh.
    Context `{Inhabited V}.

    Lemma map_to_fun_app_lookup m k :
      map_to_fun m k = m !!! k.
    Proof. done. Qed.

    Lemma lookup_total_fun_to_map f k :
      fun_to_map f !!! k = f k.
    Proof.
      apply (inj Some). by rewrite -lookup_lookup_total lookup_fun_to_map.
    Qed.

    Definition map_to_fun_to_map f k :
      map_to_fun (fun_to_map f) k = f k.
    Proof. apply lookup_total_fun_to_map. Qed.

    Definition fun_map_update (old_f : K -> V) (delta_m : M V) : K -> V :=
      map_to_fun (delta_m ∪ fun_to_map old_f).

    Lemma fun_map_update_empty f :
      fun_map_update f ∅ = f.
    Proof.
      rewrite /fun_map_update left_id_L.
      apply functional_extensionality, lookup_total_fun_to_map.
    Qed.
  End map_from_finite_inh.
End map_from_finite.
