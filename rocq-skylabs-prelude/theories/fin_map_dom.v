(*
 * Copyright (c) 2022-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Export stdpp.fin_map_dom.
Require Import bluerock.prelude.base.
Require Import bluerock.prelude.list_numbers.
Require Import bluerock.prelude.fin_maps.
Require Import bluerock.prelude.fin_sets.

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

Section dom_map_seqZ.
  (* Context `{FMD : FinMapDom Z M D}. *)
  (* ^^ No: abstracts over [EqDecision Z] :-( *)
  Context  `{!∀ A, Dom (M A) D, !FMap M,
               HL : !∀ A, Lookup Z A (M A),
               HE : !∀ A, Empty (M A),
               HP : !∀ A, PartialAlter Z A (M A)}.
  Context `{!Singleton Z D, !Union D, !Intersection D, !Difference D}.
  Context `{!OMap M, !Merge M, HF : !∀ A, MapFold Z A (M A),
            !ElemOf Z D, !Empty D, FMD : !FinMapDom Z M D}.

  Import list_numbers.
  #[local] Open Scope Z_scope.

  Lemma dom_seqZ {A} (start : Z) (xs : list A) :
    dom (map_seqZ start xs : M A) ≡ (set_rangeZ start (start + lengthZ xs) : D).
  Proof using FMD.
    rewrite /set_rangeZ.
    elim: xs start => [|x xs IH] start.
    - rewrite lengthN_nil /= Z.add_0_r rangeZ_oob //; apply dom_empty.
    - have ? : (start < start + (lengthN xs + 1)%N) by lia.
      rewrite [X in dom X] /= dom_insert lengthN_cons rangeZ_cons //.
      rewrite N.add_1_r N2Z.inj_succ -Z.add_succ_comm Z.add_1_r.
      by rewrite /= -IH.
  Qed.

  Lemma dom_seqZ_L `{!LeibnizEquiv D} {A} (start : Z) (xs : list A) :
    dom (map_seqZ start xs : M A) = (set_rangeZ start (start + lengthN xs) : D).
  Proof using FMD.
    apply leibniz_equiv, dom_seqZ.
  Qed.

End dom_map_seqZ.
