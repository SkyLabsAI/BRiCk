(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.semantics.genv.
Require Import skylabs.lang.cpp.semantics.types.
Require Import skylabs.lang.cpp.model.simple_pred.
Require Import skylabs.lang.cpp.logic.mpred.
Require Import skylabs.lang.cpp.algebra.cfrac.
Require Import skylabs.iris.extra.bi.prelude.
Require Import skylabs.iris.extra.proofmode.proofmode.

Import ChargeNotation SimpleCPP.

Section with_genv.
  Context `{Σ : cpp_logic} {σ : genv}.

  Example void_result_encoding :
    pure_encodes Tvoid VALUES_DEFS_IMPL.Vvoid [Rundef].
  Proof. by split. Qed.

  Example void_result_encoding_matches_size v vs :
    pure_encodes Tvoid v vs ->
    size_of σ Tvoid = Some (N.of_nat (length vs)).
  Proof. move=> /length_encodes ->. reflexivity. Qed.

  Example void_result_encoding_unique v vs :
    pure_encodes Tvoid v vs -> v = VALUES_DEFS_IMPL.Vvoid /\ vs = [Rundef].
  Proof. done. Qed.

  (* Void's undefined result byte must not change ordinary boolean encoding. *)
  Example false_boolean_encoding :
    pure_encodes Tbool (VALUES_DEFS_IMPL.Vint 0) [Rval 0%N].
  Proof. done. Qed.

  Example false_boolean_is_not_undefined :
    ~ pure_encodes Tbool (VALUES_DEFS_IMPL.Vint 0) [Rundef].
  Proof. done. Qed.

  Example integer_is_not_void :
    ~ pure_encodes Tvoid (VALUES_DEFS_IMPL.Vint 0) [Rundef].
  Proof. by move=> [H _]. Qed.

  (* A physical result cell uses ordinary byte ownership at the promised width. *)
  Example physical_void_result_cell p a q :
    type_ptr Tvoid p ** mem_inj_own p (Some a) **
    bytes a [Rundef] q ** vbytes a [Rundef] (cQp.frac q)
    |-- tptsto Tvoid q p VALUES_DEFS_IMPL.Vvoid.
  Proof.
    iIntros "(#T & I & B & V)".
    iPoseProof "T" as "Tc". iDestruct "Tc" as "(%Hnn & _)".
    rewrite /tptsto. iSplit; first done. iSplit; first done.
    iExists (Some a). iFrame "T I". iExists [Rundef].
    iFrame. by iPureIntro.
  Qed.

  (* Register-only results use ghost cells and retain their value ownership. *)
  Example ghost_void_result_cell p q :
    type_ptr Tvoid p ** mem_inj_own p None ** val_ p VALUES_DEFS_IMPL.Vvoid q
    |-- tptsto Tvoid q p VALUES_DEFS_IMPL.Vvoid.
  Proof.
    iIntros "(#T & I & V)".
    iPoseProof "T" as "Tc". iDestruct "Tc" as "(%Hnn & _)".
    rewrite /tptsto. iSplit; first done. iSplit; first done.
    iExists None. by iFrame "# ∗".
  Qed.
End with_genv.
