(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.semantics.
Require Import skylabs.lang.cpp.logic.pred.
Require Import skylabs.lang.cpp.logic.heap_pred.
Require Import skylabs.lang.cpp.logic.layout.
Require Import skylabs.lang.cpp.logic.object_repr.
Require Import skylabs.iris.extra.proofmode.proofmode.

Set Default Proof Using "Type*".

(** [tblockR] is a [Parameter]. The full-size definition it replaced is
    [tblockR_raw] at every type, and it satisfies every axiom about
    [tblockR]. So these axioms are consistent with the logic as it was,
    and only stop clients from relying on the full size at class types.
    [tblockR_raw_eq] holds by reflexivity; this file checks the others. *)
Section with_cpp.
  Context `{Σ : cpp_logic} {σ : genv}.

  #[local] Notation fullR := tblockR_raw.

  (** [tblockR_array_unfold] *)
  Lemma fullR_array_unfold t n q :
    fullR (Tarray t n) q -|-
    match size_of σ t with
    | Some sz =>
        if realign_ok t sz then
        aligned_ofR t **
        .[ Tbyte ! Z.of_N (n * sz) ] |-> validR **
        [∗list] i ∈ seq 0 (N.to_nat n),
          .[ Tbyte ! Z.of_N (N.of_nat i * sz) ] |-> fullR t q
        else False
    | None => False
    end.
  Proof.
    destruct (size_of σ t) as [sz|] eqn:Hsz; last by rewrite /tblockR_raw /= Hsz.
    destruct (realign_ok t sz) eqn:Hok; last by rewrite /tblockR_raw /= Hsz Hok.
    pose proof (RealignOk_of_ok σ t sz Hsz Hok) as HR.
    destruct (align_of_size_of' _ _ Hsz) as (al & Hal & Hal0 & Hdvd).
    have HA : aligned_ofR t -|- alignedR al.
    { rewrite aligned_ofR.unlock Hal. iSplit.
      - iIntros "(%a & %Ha & H)". by simplify_eq.
      - iIntros "H". iExists al. by iFrame. }
    rewrite /tblockR_raw /= Hsz Hok /= align_of_array Hal.
    have HC := blockR_chunks (N.to_nat n) sz q. rewrite N2Nat.id in HC.
    setoid_rewrite <- HA.
    iSplit.
    - iIntros "(B & #A)".
      iDestruct (observe validR with "B") as "#Vp".
      iEval (rewrite HC) in "B". iDestruct "B" as "[E B]". iFrame "A E".
      iApply (big_sepL_impl with "B").
      iIntros "!>" (k i Hi) "$".
      iApply (aligned_ofR_byte_sub t sz (N.of_nat i) Hsz Hok). by iFrame "A Vp".
    - rewrite HC. iIntros "(#A & E & B)". iFrame "A E".
      iApply (big_sepL_impl with "B"). iIntros "!>" (k i Hi) "B".
      rewrite _offsetR_sep. iDestruct "B" as "[$ _]".
  Qed.

  (** The instances. *)
  Lemma fullR_timeless ty q : Timeless (fullR ty q).
  Proof. rewrite/tblockR_raw. case_match; apply _. Qed.
  Lemma fullR_cfractional ty : CFractional (fullR ty).
  Proof.
    rewrite/tblockR_raw. do 2!(case_match; last by apply _).
    apply _.
  Qed.
  Lemma fullR_observe_frac_valid ty n :
    SizeOf ty n -> TCLt (0 ?= n)%N -> CFracValid0 (fullR ty).
  Proof. rewrite/tblockR_raw=>-> ?. case_match; solve_cfrac_valid. Qed.
  Lemma fullR_nonnull n ty q :
    SizeOf ty n -> TCLt (0 ?= n)%N -> Observe nonnullR (fullR ty q).
  Proof. intros Heq ?. rewrite/tblockR_raw {}Heq. case_match; by apply _. Qed.
  Lemma fullR_valid_ptr ty q : Observe validR (fullR ty q).
  Proof. rewrite /tblockR_raw. case_match; refine _. case_match; refine _. Qed.
End with_cpp.
