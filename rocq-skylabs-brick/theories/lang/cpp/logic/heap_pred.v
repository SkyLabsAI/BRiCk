(*
 * Copyright (c) 2020-2023 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Export elpi.apps.locker.locker.

Require Import bluerock.iris.extra.proofmode.proofmode.
Require Import bluerock.iris.extra.bi.fractional.

Require Import bluerock.lang.cpp.bi.cfractional.
Require Import bluerock.lang.cpp.semantics.
Require Import bluerock.lang.cpp.syntax.
Require Import bluerock.lang.cpp.logic.pred.
Require Import bluerock.lang.cpp.logic.path_pred.

Export bluerock.lang.cpp.logic.pred.
(* ^^ Should this be exported? this file is supposed to provide wrappers
   so that clients do not work directly with [pred.v] *)
Export bluerock.lang.cpp.algebra.cfrac.

Require Export bluerock.lang.cpp.logic.heap_pred.aggregate.
Require Export bluerock.lang.cpp.logic.heap_pred.any.
Require Export bluerock.lang.cpp.logic.heap_pred.block.
Require Export bluerock.lang.cpp.logic.heap_pred.everywhere.
Require Export bluerock.lang.cpp.logic.heap_pred.null.
Require Export bluerock.lang.cpp.logic.heap_pred.prim.
Require Export bluerock.lang.cpp.logic.heap_pred.simple.
Require Export bluerock.lang.cpp.logic.heap_pred.tptsto.
Require Export bluerock.lang.cpp.logic.heap_pred.uninit.
Require Export bluerock.lang.cpp.logic.heap_pred.valid.

#[local] Set Printing Coercions.

Implicit Types (σ : genv) (p : ptr) (o : offset).

Section with_cpp.
  Context `{Σ : cpp_logic}.

  (** [varargsR ts_ps] is the ownership of a group of variadic arguments.
      The [type] is the type of the argument and the [ptr] is the location
      of the argument.

      TODO: move to [pred.v]
   *)
  Parameter varargsR : forall {σ : genv}, list (type * ptr) -> Rep.
End with_cpp.

Section with_cpp.
  Context `{Σ : cpp_logic} {σ : genv}.

  (* TODO: misplaced not relevant to [heap_pred] *)
  Lemma has_type_noptr v ty :
    nonptr_prim_type ty ->
    has_type v ty -|- [| has_type_prop v ty |].
  Proof.
    intros; iSplit.
    iApply has_type_has_type_prop.
    by iApply has_type_prop_has_type_noptr.
  Qed.

  Lemma has_type_void v : has_type v Tvoid -|- [| v = Vvoid |].
  Proof. by rewrite has_type_noptr ?has_type_prop_void. Qed.


  Lemma tptstoR_Vvoid_tptstoR_fuzzy q :
    tptstoR Tvoid q Vvoid -|- tptsto_fuzzyR Tvoid q Vvoid.
  Proof.
    rewrite tptsto_fuzzyR.unlock. split'.
    - iIntros "R". iExists Vvoid. by iFrame "R".
    - iIntros "(% & %Hval & R)". apply val_related_Vundef in Hval. by simplify_eq.
  Qed.
  Lemma tptsto_fuzzyR_Vvoid_primR q : tptsto_fuzzyR Tvoid q Vvoid -|- primR Tvoid q Vvoid.
  Proof.
    rewrite primR.unlock initializedR.unlock. rewrite left_id.
    by rewrite has_type_void pureR_only_provable only_provable_True// left_id.
  Qed.
  Lemma tptstoR_Vvoid_primR q : tptstoR Tvoid q Vvoid -|- primR Tvoid q Vvoid.
  Proof. by rewrite tptstoR_Vvoid_tptstoR_fuzzy tptsto_fuzzyR_Vvoid_primR. Qed.

  Lemma has_type_ptr p ty :
    has_type (Vptr p) (Tptr ty) -|- p |-> (validR ** aligned_ofR ty).
  Proof.
    by rewrite has_type_ptr' _at_sep _at_validR aligned_ofR_aligned_ptr_ty.
  Qed.

  Definition is_raw_or_undef (v : val) : bool :=
    if v is (Vundef | Vraw _) then true else false.

  Lemma tptsto_fuzzyR_Vxxx_primR ty q v :
    ~~ is_raw_or_undef v -> tptsto_fuzzyR ty q v -|- primR ty q v.
  Proof.
    split'; try apply primR_tptsto_fuzzyR.
    rewrite primR.unlock initializedR.unlock. iIntros "R".
    iDestruct (observe_elim (pureR $ has_type_or_undef _ _) with "R") as "($ & #T)".
    rewrite has_type_or_undef_unfold.
    rewrite pureR_or pureR_only_provable. iDestruct "T" as "[$ | ->]".
    by destruct v. done.
  Qed.

  Lemma tptstoR_Vxxx_primR ty q v :
    ~~ is_raw_or_undef v -> tptstoR ty q v |-- primR ty q v.
  Proof.
    intros. by rewrite tptsto_fuzzyR_intro tptsto_fuzzyR_Vxxx_primR.
  Qed.
End with_cpp.

Notation uninitR := uninit.uninitR.
Notation tptstoR := tptsto.tptstoR.
Notation tptsto_fuzzyR := tptsto.tptsto_fuzzyR.
Notation blockR := block.blockR.
Notation primR := prim.primR.
Notation anyR := any.anyR.
Notation tblockR := block.tblockR.
