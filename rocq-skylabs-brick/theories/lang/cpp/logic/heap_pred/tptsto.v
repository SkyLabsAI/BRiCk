(*
 * Copyright (c) 2023 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bluerock.lang.cpp.logic.heap_pred.prelude.
Require Import bluerock.lang.cpp.logic.heap_pred.valid.
Require Import bluerock.lang.cpp.logic.heap_pred.null.

#[local] Set Printing Coercions.
Implicit Types (σ : genv) (p : ptr) (o : offset).

(**
[tptstoR ty q v] is [q] ownership of a memory location of type [ty]
storing the value [v].

Whereas [tptstoR] is precise w.r.t. the value (i.e., given two
fractions, one learns the values are equal), [tptstoR_fuzzyR ty q v]
lets one view the contents of the memory as either [v] or a related
value [v'] (see [val_related] and [tptsto_fuzzyR_val_related]).
*)
mlock Definition tptstoR `{Σ : cpp_logic} {σ : genv} (ty : Rtype) (q : cQp.t) (v : val) : Rep :=
  as_Rep (fun p => tptsto ty q p v).

mlock Definition tptsto_fuzzyR `{Σ : cpp_logic, σ : genv} (ty : Rtype) (q : cQp.t) (v : val) : Rep :=
  Exists v', [| val_related ty v v' |] ** tptstoR ty q v'.

Section tptstoR.
  Context `{Σ : cpp_logic} {σ : genv}.

  (** [tptstoR] *)

  Lemma _at_tptstoR (p : ptr) ty q v : p |-> tptstoR ty q v -|- tptsto ty q p v.
  Proof. by rewrite tptstoR.unlock _at_as_Rep. Qed.

  #[global] Instance tptstoR_timeless ty q v :
    Timeless (tptstoR ty q v).
  Proof. rewrite tptstoR.unlock. apply _. Qed.

  #[global] Instance tptstoR_cfractional ty :
    CFractional1 (tptstoR ty).
  Proof. rewrite tptstoR.unlock. apply _. Qed.
  #[global] Instance tptstoR_as_cfractional ty :
    AsCFractional1 (tptstoR ty).
  Proof. solve_as_cfrac. Qed.

  #[global] Instance tptstoR_observe_cfrac_valid ty :
    CFracValid1 (tptstoR ty).
  Proof. rewrite tptstoR.unlock. solve_cfrac_valid. Qed.

  #[global] Instance tptstoR_observe_agree ty q1 q2 v1 v2 :
    Observe2 [| v1 = v2 |] (tptstoR ty q1 v1) (tptstoR ty q2 v2).
  Proof.
    rewrite tptstoR.unlock; apply: as_Rep_only_provable_observe_2=> p.
  Qed.

  #[global] Instance _at_tptstoR_welltyped p ty q v :
    Observe (has_type_or_undef v ty) (p |-> tptstoR ty q v).
  Proof. rewrite _at_tptstoR. refine _. Qed.
  #[global] Instance tptstoR_welltyped ty q v :
    Observe (pureR (has_type_or_undef v ty)) (tptstoR ty q v).
  Proof.
    apply observe_at=>p. rewrite _at_pureR. apply _.
  Qed.

  #[global] Instance _at_tptstoR_reference_to p ty q v :
    Observe (reference_to ty p) (p |-> tptstoR ty q v) | 100.
  Proof. rewrite _at_tptstoR. refine _. Qed.

  #[global] Instance tptstoR_type_ptrR ty q v :
    Observe (type_ptrR ty) (tptstoR ty q v).
  Proof.
    rewrite tptstoR.unlock type_ptrR_eq/type_ptrR_def.
    apply as_Rep_observe. intros; apply tptsto_type_ptr.
  Qed.

  #[global] Instance tptstoR_validR ty q v : Observe validR (tptstoR ty q v).
  Proof. apply observe_at=>p. rewrite -type_ptrR_validR. refine _. Qed.

  #[global] Instance tptstoR_nonnull ty q v : Observe nonnullR (tptstoR ty q v).
  Proof. trans (type_ptrR ty); apply _. Qed.

  (**
  The various [tptsto] accessors in this file support low-level
  mechanisms like constant casts (see [primR_wp_const_val]) and
  transporting resources along [ptr_congP] and [offset_congP] (see,
  e.g., [rawR_ptr_congP_transport]).
  *)
  Lemma tptstoR_tptsto_acc (p : ptr) ty q v :
    p |-> tptstoR ty q v |--
      tptsto ty q p v **
      (Forall p' q' v', tptsto ty q' p' v' -* p' |-> tptstoR ty q' v').
  Proof.
    setoid_rewrite _at_tptstoR. iIntros "$". auto.
  Qed.

  #[global] Instance tptstoR_heap_type ty q v :
    Observe [| is_heap_type ty |] (tptstoR ty q v).
  Proof. rewrite tptstoR.unlock. refine _. Qed.

  (** [tptsto_fuzzyR] *)

  Lemma _at_tptsto_fuzzyR (p : ptr) ty q v :
    p |-> tptsto_fuzzyR ty q v -|-
      Exists v', [| val_related ty v v' |] ** p |-> tptstoR ty q v'.
  Proof.
    rewrite tptsto_fuzzyR.unlock. rewrite _at_exists. f_equiv=>v'.
    by rewrite _at_sep _at_only_provable.
  Qed.

  #[global] Instance tptsto_fuzzyR_timeless : Timeless3 tptsto_fuzzyR.
  Proof. rewrite tptsto_fuzzyR.unlock. apply _. Qed.

  #[global] Instance tptsto_fuzzyR_cfractional ty : CFractional1 (tptsto_fuzzyR ty).
  Proof. rewrite tptsto_fuzzyR.unlock. apply _. Qed.
  #[global] Instance tptsto_fuzzyR_cfrac_valid ty : CFracValid1 (tptsto_fuzzyR ty).
  Proof. rewrite tptsto_fuzzyR.unlock. solve_cfrac_valid. Qed.

  #[global] Instance tptsto_fuzzyR_welltyped ty q v :
    Observe (pureR (has_type_or_undef v ty)) (tptsto_fuzzyR ty q v).
  Proof.
    rewrite tptsto_fuzzyR.unlock. iIntros "(% & % & R)".
    iDestruct (tptstoR_welltyped with "R") as "#?".
    by rewrite has_type_or_undef_val_related.
  Qed.
  #[global] Instance _at_tptsto_fuzzyR_welltyped p ty q v :
    Observe (has_type_or_undef v ty) (p |-> tptsto_fuzzyR ty q v).
  Proof. apply _at_observe_pureR, _. Qed.

  #[global] Instance _at_tptsto_fuzzyR_reference_to p ty q v :
    Observe (reference_to ty p) (p |-> tptsto_fuzzyR ty q v) | 100.
  Proof. rewrite _at_tptsto_fuzzyR. refine _. Qed.

  #[global] Instance tptsto_fuzzyR_type_ptrR ty q v :
    Observe (type_ptrR ty) (tptsto_fuzzyR ty q v).
  Proof. rewrite tptsto_fuzzyR.unlock. apply _. Qed.

  #[global] Instance tptsto_fuzzyR_validR ty q v : Observe validR (tptsto_fuzzyR ty q v).
  Proof. apply observe_at=>p. rewrite -type_ptrR_validR. refine _. Qed.

  #[global] Instance tptsto_fuzzyR_nonnull ty q v :
    Observe nonnullR (tptsto_fuzzyR ty q v).
  Proof. rewrite tptsto_fuzzyR.unlock. apply _. Qed.

  #[global] Instance tptstoR_tptsto_fuzzyR_agree ty q1 q2 v1 v2 :
    Observe2 [| val_related ty v1 v2 |] (tptstoR ty q1 v1) (tptsto_fuzzyR ty q2 v2).
  Proof.
    rewrite tptsto_fuzzyR.unlock. iIntros "R1 (% & % & R2)".
    iDestruct (observe_2 [| _ = _ |] with "R1 R2") as %?. simplify_eq. auto.
  Qed.
  #[global] Instance tptsto_fuzzyR_agree ty q1 q2 v1 v2 :
    Observe2 [| val_related ty v1 v2 |] (tptsto_fuzzyR ty q1 v1) (tptsto_fuzzyR ty q2 v2).
  Proof.
    rewrite tptsto_fuzzyR.unlock. iIntros "(% & % & R1) (% & % & R2)".
    iDestruct (observe_2 [| _ = _ |] with "R1 R2") as %?. simplify_eq.
    iIntros "!> !%". by etrans.
  Qed.

  Lemma tptsto_fuzzyR_intro ty q v : tptstoR ty q v |-- tptsto_fuzzyR ty q v.
  Proof.
    rewrite tptsto_fuzzyR.unlock -(bi.exist_intro v). by iIntros "$".
  Qed.

  Lemma tptsto_fuzzyR_elim_r ty q1 q2 v1 v2 :
    tptstoR ty q1 v1 ** tptsto_fuzzyR ty q2 v2 |-- tptstoR ty (q1 + q2) v1.
  Proof.
    rewrite tptsto_fuzzyR.unlock. iIntros "(R1 & (% & % & R2))".
    iDestruct (observe_2 [| _ = _ |] with "R1 R2") as %?. simplify_eq.
    iCombine "R1 R2" as "$".
  Qed.
  Lemma tptsto_fuzzyR_elim_l ty q1 q2 v1 v2 :
    tptsto_fuzzyR ty q1 v1 ** tptstoR ty q2 v2 |-- tptstoR ty (q1 + q2) v2.
  Proof. by rewrite comm tptsto_fuzzyR_elim_r comm_L. Qed.

  Lemma tptsto_fuzzyR_val_related ty q v1 v2 :
    val_related ty v1 v2 ->
    tptsto_fuzzyR ty q v1 -|- tptsto_fuzzyR ty q v2.
  Proof.
    intros. rewrite tptsto_fuzzyR.unlock. f_equiv=>v'. do 2!f_equiv. split; by etrans.
  Qed.

  Lemma tptsto_fuzzyR_tptsto_acc (p : ptr) ty q v :
    p |-> tptsto_fuzzyR ty q v |--
      Exists v', [| val_related ty v v' |] ** tptsto ty q p v' **
      (Forall p' q' v', [| val_related ty v v' |] -* tptsto ty q' p' v' -* p' |-> tptsto_fuzzyR ty q' v).
  Proof.
    setoid_rewrite _at_tptsto_fuzzyR. iIntros "(%v' & %Hval & R)".
    iDestruct (tptstoR_tptsto_acc with "R") as "(R & HR)".
    iExists v'. iFrame (Hval) "R". iIntros (??? Hval') "R". iExists _. iFrame (Hval').
    iApply ("HR" with "R").
  Qed.

  #[global] Instance tptsto_fuzzyR_heap_type ty q v :
    Observe [| is_heap_type ty |] (tptsto_fuzzyR ty q v).
  Proof. rewrite tptsto_fuzzyR.unlock. refine _. Qed.

End tptstoR.
