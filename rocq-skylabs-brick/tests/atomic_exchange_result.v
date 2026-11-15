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
Require Import skylabs.lang.cpp.logic.atomics.
Require Import skylabs.iris.extra.proofmode.proofmode.

Set Default Proof Using "Type*".

Section with_cpp.
  Context `{Σ : cpp_logic} {σ : genv}.

  (* The generic exchange writes the old value through ret, keeps the source,
     updates the atomic location, and returns void. No auto axioms are used. *)
  Example generic_exchange_result (x y z : ptr) (ty : type) (old new : val) :
    x |-> primR ty 1$m old ** y |-> primR ty 1$m new ** z |-> anyR ty 1$m
    |-- wp_atom top "__atomic_exchange" ty
      [Vptr x; _SEQ_CST; Vptr y; Vptr z]
      (fun v => x |-> primR ty 1$m new ** y |-> primR ty 1$m new **
                z |-> primR ty 1$m old ** [| v = Vundef |]).
  Proof.
    iIntros "(Hx & Hy & Hz)".
    iApply wp_atom_exchange_cst.
    iSplit; first done.
    iSplitL "Hy Hz"; first by iNext; iFrame.
    iAuIntro1. rewrite /atomic1_acc.
    iDestruct (fupd_mask_subseteq empty) as ">Y"; first set_solver.
    iModIntro. iExists old. iFrame "Hx".
    iSplit.
    { iIntros "Hx". iMod "Y". iModIntro. iFrame. }
    iIntros "!> Hx". iMod "Y". iModIntro. iIntros "[Hy Hz]".
    iFrame. done.
  Qed.
End with_cpp.
