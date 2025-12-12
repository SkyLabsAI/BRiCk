(*
 * Copyright (c) 2023 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bluerock.lang.cpp.logic.heap_pred.prelude.
Require Import bluerock.lang.cpp.logic.heap_pred.simple.
Require Import bluerock.lang.cpp.logic.heap_pred.valid.
Require Import bluerock.lang.cpp.logic.heap_pred.null.
Require Import bluerock.lang.cpp.logic.heap_pred.tptsto.
Require Import bluerock.lang.cpp.logic.heap_pred.uninit.

#[local] Set Printing Coercions.
Implicit Types (σ : genv) (p : ptr) (o : offset).

(**
[initializedR ty q v]: the argument pointer points to an initialized value
[v] of C++ type [ty].

NOTE [ty] *must* be a primitive type.
 *)
mlock
Definition initializedR `{Σ : cpp_logic, σ : genv} (ty : Rtype) (q : cQp.t) (v : val) : Rep :=
  (**
  NOTE: Clients use [primR (erase_qualifiers ty)] but we do not bake
  [erase_qualifiers] in to simplify our automation.
   *)
  pureR (has_type v ty) **
  tptsto_fuzzyR ty q v.


(**
[primR ty q v]: the argument pointer points to an initialized value
[v] of C++ type [ty] **that is not raw**.

NOTE [ty] *must* be a primitive type.
*)
mlock
Definition primR `{Σ : cpp_logic, σ : genv} (ty : Rtype) (q : cQp.t) (v : val) : Rep :=
  [| ~~ is_raw v |] ** initializedR ty q v.

(* TODO: documentation needed *)
mlock Definition reference_toR `{Σ : cpp_logic, σ : genv} (ty : Rtype) : Rep :=
  as_Rep (reference_to ty).

#[global] Instance reference_toR_knoweldge `{Σ : cpp_logic, resolve : genv}
  : Knowledge1 reference_toR.
Proof. rewrite reference_toR.unlock; intros. split; refine _. Qed.
#[global] Instance reference_toR_timeless `{Σ : cpp_logic, resolve : genv}
  : Timeless1 reference_toR.
Proof. rewrite reference_toR.unlock; intros. refine _. Qed.


Section with_cpp.
  Context `{Σ : cpp_logic} {σ : genv}.

  Lemma _at_reference_toR ty (p : ptr) :
    p |-> reference_toR ty -|- reference_to ty p.
  Proof. by rewrite reference_toR.unlock _at_as_Rep. Qed.

  Lemma _at_initializedR (p : ptr) ty q v :
    p |-> initializedR ty q v -|- has_type v ty ** p |-> tptsto_fuzzyR ty q v.
  Proof.
    by rewrite initializedR.unlock !_at_sep _at_pureR.
  Qed.

  Lemma _at_primR (p : ptr) ty q v :
    p |-> primR ty q v -|-
      [| ~~ is_raw v |] **
      has_type v ty **
      p |-> tptsto_fuzzyR ty q v.
  Proof.
    by rewrite primR.unlock initializedR.unlock !_at_sep _at_only_provable _at_pureR.
  Qed.

  (** [initializedR] *)
  #[global] Instance initializedR_timeless ty q v
    : Timeless (initializedR ty q v).
  Proof. rewrite initializedR.unlock. apply _. Qed.

  #[global] Instance initializedR_cfractional ty :
    CFractional1 (initializedR ty).
  Proof. rewrite initializedR.unlock. apply _. Qed.
  #[global] Instance initializedR_as_cfractional ty :
    AsCFractional1 (initializedR ty).
  Proof. solve_as_cfrac. Qed.

  #[global] Instance initializedR_observe_cfrac_valid ty :
    CFracValid1 (initializedR ty).
  Proof. rewrite initializedR.unlock. solve_cfrac_valid. Qed.

  #[global] Instance initializedR_observe_has_type ty q v :
    Observe (pureR (has_type v ty)) (initializedR ty q v).
  Proof. rewrite initializedR.unlock has_type_drop_qualifiers. apply _. Qed.

  #[global] Instance _at_initializedR_observe_has_type ty q v (p : ptr) :
    Observe (has_type v ty) (p |-> initializedR ty q v).
  Proof. apply: _at_observe_pureR. Qed.

  #[global] Instance initializedR_observe_has_type_prop ty q v :
    Observe [| has_type_prop v ty |] (initializedR ty q v).
  Proof.
    apply observe_at=>p. rewrite _at_only_provable -has_type_has_type_prop.
    apply _.
  Qed.

  Lemma initializedR_has_type_prop ty q v :
    initializedR ty q v |--
    initializedR ty q v ** [| has_type_prop v ty |].
  Proof. apply: observe_elim. Qed.

  Lemma initializedR_tptsto_acc p ty q v :
    p |-> initializedR ty q v |--
      Exists v', [| val_related ty v v' |] ** tptsto ty q p v' **
      (Forall p' q' v', [| val_related ty v v' |] -* tptsto ty q' p' v' -* p' |-> initializedR ty q' v).
  Proof.
    setoid_rewrite _at_initializedR. iIntros "(#T & R)".
    iDestruct (tptsto_fuzzyR_tptsto_acc with "R") as "(%v' & %Hval & R & HR)".
    iExists v'. iFrame (Hval) "R T". iFrame "HR".
  Qed.

  #[global] Instance _at_initializedR_reference_to p ty q v :
    Observe (reference_to ty p) (p |-> initializedR ty q v) | 100.
  Proof. rewrite _at_initializedR. refine _. Qed.

  Lemma test:
    forall σ ty v v',
      v' = Vundef ->
      val_related ty v v' ->
      v = Vundef.
  Proof.
    intros * Hv' Hval_related.
    induction Hval_related;
      try (by inversion Hv'); auto.
  Succeed Qed. Abort.

  (** This seems odd, but it's relevant to the (former) proof that [anyR] is
  fractional; currently unused. *)
  Lemma initializedR_uninitR ty q1 q2 v :
    initializedR ty q1 v |--
    uninitR ty q2 -*
    initializedR ty (q1 + q2) Vundef.
  Proof.
    rewrite initializedR.unlock uninitR_tptstoR. iIntros "(#T & R1) R2".
    iDestruct (observe_2 [| val_related _ _ _ |] with "R2 R1") as %->%val_related_Vundef.
    iFrame "T". iDestruct (tptsto_fuzzyR_elim_l with "[$R1 $R2]") as "R".
    by iDestruct (tptsto_fuzzyR_intro with "R") as "$".
  Qed.

  #[global]
  Instance initializedR_type_ptr_observe ty q v : Observe (type_ptrR ty) (initializedR ty q v).
  Proof. rewrite initializedR.unlock. apply _. Qed.

  (** Observing [valid_ptr] *)
  #[global]
  Instance initializedR_valid_observe {ty q v} : Observe validR (initializedR ty q v).
  Proof. rewrite -svalidR_validR -type_ptrR_svalidR; refine _. Qed.

  Lemma initializedR_tptsto_fuzzyR ty q v : initializedR ty q v |-- tptsto_fuzzyR ty q v.
  Proof. rewrite initializedR.unlock. iIntros "(_ & $)". Qed.

  #[global]
  Instance initializedR_nonnull_observe {ty q v} :
    Observe nonnullR (initializedR ty q v).
  Proof. rewrite initializedR.unlock. apply _. Qed.

  (** [primR] *)
  #[global] Instance primR_timeless ty q v
    : Timeless (primR ty q v).
  Proof. rewrite primR.unlock. apply _. Qed.

  #[global] Instance primR_cfractional ty :
    CFractional1 (primR ty).
  Proof. rewrite primR.unlock. apply _. Qed.
  #[global] Instance primR_as_cfractional ty :
    AsCFractional1 (primR ty).
  Proof. solve_as_cfrac. Qed.

  #[global] Instance primR_observe_cfrac_valid ty :
    CFracValid1 (primR ty).
  Proof. rewrite primR.unlock. solve_cfrac_valid. Qed.

  Section TEST.
    Context (p : ptr).

    Goal
        p |-> primR Tint (1/2)$m 0
        |-- p |-> primR Tint (1/2)$m 0 -* p |-> primR Tint 1$m 0.
    Proof.
      iIntros "H1 H2".
      iCombine "H1 H2" as "$".
    Abort.

    Goal
        p |-> primR Tint 1$c 0 |-- p |-> primR Tint (1/2)$c 0 ** p |-> primR Tint (1/2)$c 0.
    Proof.
      iIntros "H".
      iDestruct "H" as "[H1 H2]".
    Abort.

    Goal p |-> primR Tint 1$c 1 |-- True.
    Proof.
      iIntros "H".
      iDestruct (observe [| 1 ≤ 1 |]%Qp with "H") as %? (* ; [] << FAILS *).
    Abort.
  End TEST.

  #[global] Instance primR_observe_agree ty q1 q2 v1 v2 :
    Observe2 [| v1 = v2 |] (primR ty q1 v1) (primR ty q2 v2).
  Proof.
    rewrite primR.unlock initializedR.unlock. iIntros "(% & _ & R1) (% & _ & R2)".
    iDestruct (observe_2 [| val_related _ _ _ |] with "R1 R2") as %?.
    eauto using val_related_not_raw.
  Qed.

  (* Typical [f] are [Vint], [Vn] etc; this gives agreement for [ulonglongR] etc. *)
  #[global] Instance primR_observe_agree_constr ty q1 q2 {A} f `{!Inj eq eq f} (v1 v2 : A) :
    Observe2 [| v1 = v2 |]
      (primR ty q1 (f v1))
      (primR ty q2 (f v2)).
  Proof. apply (observe2_inj f), _. Qed.

  #[global] Instance primR_observe_has_type ty q v :
    Observe (pureR (has_type v ty)) (primR ty q v).
  Proof. rewrite primR.unlock initializedR.unlock has_type_drop_qualifiers. apply _. Qed.

  #[global] Instance _at_primR_observe_has_type ty q v (p : ptr) :
    Observe (has_type v ty) (p |-> primR ty q v).
  Proof. apply: _at_observe_pureR. Qed.

  #[global] Instance primR_observe_has_type_prop ty q v :
    Observe [| has_type_prop v ty |] (primR ty q v).
  Proof.
    apply observe_at=>p. rewrite _at_only_provable -has_type_has_type_prop.
    apply _.
  Qed.

  Lemma primR_has_type_prop ty q v :
    primR ty q v |--
    primR ty q v ** [| has_type_prop v ty |].
  Proof. apply: observe_elim. Qed.

  Lemma primR_tptsto_acc p ty q v :
    p |-> primR ty q v |--
      Exists v', [| val_related ty v v' |] ** tptsto ty q p v' **
      (Forall p' q' v', [| val_related ty v v' |] -* tptsto ty q' p' v' -* p' |-> primR ty q' v).
  Proof.
    setoid_rewrite _at_primR. iIntros "(%Hraw & #T & R)".
    iDestruct (tptsto_fuzzyR_tptsto_acc with "R") as "(%v' & %Hval & R & HR)".
    iExists v'. iFrame (Hval Hraw) "R T". iFrame "HR".
  Qed.

  #[global] Instance _at_primR_reference_to p ty q v :
    Observe (reference_to ty p) (p |-> primR ty q v) | 100.
  Proof. rewrite _at_primR. refine _. Qed.


  Lemma test:
    forall σ ty v v',
      v' = Vundef ->
      val_related ty v v' ->
      v = Vundef.
  Proof.
    intros * Hv' Hval_related.
    induction Hval_related;
      try (by inversion Hv'); auto.
  Succeed Qed. Abort.

  (** This seems odd, but it's relevant to the (former) proof that [anyR] is
  fractional; currently unused. *)
  Lemma primR_uninitR ty q1 q2 v :
    primR ty q1 v |--
    uninitR ty q2 -*
    primR ty (q1 + q2) Vundef.
  Proof.
    rewrite primR.unlock initializedR.unlock uninitR_tptstoR. iIntros "(_ & #T & R1) R2".
    iDestruct (observe_2 [| val_related _ _ _ |] with "R2 R1") as %->%val_related_Vundef.
    iFrame "T". iDestruct (tptsto_fuzzyR_elim_l with "[$R1 $R2]") as "R".
    by iDestruct (tptsto_fuzzyR_intro with "R") as "$".
  Qed.

  #[global]
  Instance primR_type_ptr_observe ty q v : Observe (type_ptrR ty) (primR ty q v).
  Proof. rewrite primR.unlock. apply _. Qed.

  (** Observing [valid_ptr] *)
  #[global]
  Instance primR_valid_observe {ty q v} : Observe validR (primR ty q v).
  Proof. rewrite -svalidR_validR -type_ptrR_svalidR; refine _. Qed.

  #[global]
  Instance observe_type_ptr_pointsto (p : ptr) ty (R : Rep) :
    Observe (type_ptrR ty) R -> Observe (type_ptr ty p) (_at p R).
  Proof. rewrite -_at_type_ptrR. apply _at_observe. Qed.

  Lemma primR_tptsto_fuzzyR ty q v : primR ty q v |-- tptsto_fuzzyR ty q v.
  Proof. rewrite primR.unlock initializedR.unlock. iIntros "(_ & _ & $)". Qed.

  #[global]
  Instance primR_nonnull_observe {ty q v} :
    Observe nonnullR (primR ty q v).
  Proof. rewrite primR.unlock. apply _. Qed.

  (** ** [reference_to] *)
  #[global] Instance reference_to_valid ty p : Observe (valid_ptr p) (reference_to ty p).
  Proof. rewrite reference_to_elim. refine _. Qed.
  #[global] Instance reference_to_aligned ty p : Observe [| aligned_ptr_ty ty p |] (reference_to ty p).
  Proof. rewrite reference_to_elim. refine _. Qed.
  #[global] Instance reference_to_aligned_ofR ty (p : ptr) : Observe (p |-> aligned_ofR ty) (reference_to ty p).
  Proof. rewrite reference_to_elim aligned_ofR_aligned_ptr_ty. refine _. Qed.
  #[global] Instance reference_to_not_null ty p : Observe [| p <> nullptr |] (reference_to ty p).
  Proof. rewrite reference_to_elim. refine _. Qed.
  #[global] Instance reference_to_strict_valid ty p :
    TCEq (zero_sized_array ty) false ->
    Observe (strict_valid_ptr p) (reference_to ty p).
  Proof. rewrite reference_to_elim. move => ->. refine _. Qed.


  #[global] Instance reference_to_aligned_observe p ty :
    Observe (p |-> aligned_ofR ty) (reference_to ty p).
  Proof. rewrite aligned_ofR_aligned_ptr_ty reference_to_elim; refine _. Qed.
  #[global] Instance reference_to_valid_observe p ty :
    Observe (p |-> validR) (reference_to ty p).
  Proof. rewrite _at_validR reference_to_elim; refine _. Qed.

End with_cpp.
