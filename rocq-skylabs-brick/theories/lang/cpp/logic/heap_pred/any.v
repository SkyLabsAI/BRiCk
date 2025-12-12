(*
 * Copyright (c) 2023 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bluerock.lang.cpp.logic.heap_pred.prelude.
Require Import bluerock.lang.cpp.logic.heap_pred.valid.
Require Import bluerock.lang.cpp.logic.heap_pred.everywhere.
Require Import bluerock.lang.cpp.logic.heap_pred.tptsto.
Require Import bluerock.lang.cpp.logic.heap_pred.prim.
Require Import bluerock.lang.cpp.logic.heap_pred.uninit.
Require Import bluerock.lang.cpp.logic.heap_pred.null.

#[local] Set Printing Coercions.
Implicit Types (σ : genv) (p : ptr) (o : offset).

#[local]
Definition primitiveR `{Σ : cpp_logic} {σ : genv} q ty :=
  Exists v,
    let rty :=
      match erase_qualifiers ty with
      | Trv_ref t => Tref t
      | t => t
      end
    in tptstoR rty q v.

(** [anyR] The argument pointers points to a value of C++ type [ty] that might be
    uninitialized.
 *)
mlock
Definition anyR `{Σ : cpp_logic} {σ : genv} (ty : Rtype) (q : cQp.t) : Rep :=
  everywhereR σ.(genv_tu) primitiveR q ty.

Section with_cpp.
  Context `{Σ : cpp_logic} {σ : genv}.

  #[global] Instance anyR_timeless : ∀ ty q, Timeless (anyR ty q).
  Proof.
    intros. red.
    rewrite anyR.unlock.
    iIntros "X".
    iDestruct "X" as (f) "X".
    iExists f.
    iStopProof.
    eapply everywhereR_f_timeless. refine _.
  Qed.

  #[global] Instance anyR_cfractional : ∀ ty, CFractional (anyR ty).
  Proof.
    do 3 intro.
    rewrite anyR.unlock.
    iSplit.
    { iIntros "X"; iDestruct "X" as (f) "X".
      rewrite everywhereR_f_cfractional.
      iDestruct "X" as "[A B]".
      iSplitL "A"; iExists _; iFrame. }
    { iIntros "[A B]".
      iDestruct "A" as (fa) "A".
      iDestruct "B" as (fb) "B".
      iExists (max fa fb).
      rewrite everywhereR_f_cfractional.
      iSplitL "A".
      - rewrite -(_offsetR_id (everywhereR_f _ _ fa _ _)).
        rewrite -(_offsetR_id (everywhereR_f _ _ (_ `max` _) _ _)).
        iRevert "A".
        iApply everywhereR_f_mono'. lia.
      - rewrite -(_offsetR_id (everywhereR_f _ _ fb _ _)).
        rewrite -(_offsetR_id (everywhereR_f _ _ (_ `max` _) _ _)).
        iRevert "B".
        iApply everywhereR_f_mono'. lia. }
  Qed.


  #[global] Instance anyR_observe_frac_valid ty :
    TCSimpl (zero_sized_array ty) false -> CFracValid0 (anyR ty).
  Proof.
    rewrite anyR.unlock.
    constructor =>q.
    rewrite everywhereR_unfold.
    revert q; induction ty; simpl; refine _.
    { revert H.
      simpl. rewrite /qual_norm/=.
      case_bool_decide.
      { inversion 1. }
      { intros. iIntros "H".
        have ->: (n = N.succ (n - 1))%N by lia.
        rewrite replicateN_S. rewrite arr.arrayR_cons.
        iDestruct "H" as "[? [H ?]]".
        iDestruct (IHty with "H") as "$"; eauto. } }
    { case_match; refine _.
      case_match; refine _. }
    { intros.
      iIntros "H".
      iDestruct (IHty with "H") as "%".
      { by erewrite zero_sized_array_qual. }
      { rewrite qualify_frac in H0.
        eauto. } }
  Qed.

  #[global] Instance anyR_as_fractional ty : AsCFractional0 (anyR ty).
  Proof. solve_as_cfrac. Qed.

  Lemma anyR_disjoint (l : ptr) ty b1 b2 :
    TCSimpl (zero_sized_array ty) false ->
    l |-> anyR ty (cQp.mk b1 1) |-- l |-> anyR ty (cQp.mk b2 1) -* False.
  Proof.
    iIntros (?) "K L". iCombine "K L" as "P".
    by iDestruct (observe [| _ ≤ 1 |]%Qp with "P") as %?.
  Qed.

  Lemma anyR_Tqualified t tq q : anyR (Tqualified tq t) q -|- anyR t (qualify tq q).
  Proof. by rewrite anyR.unlock everywhereR_Tqualified. Qed.

  #[local] Lemma not_heap_type (t : type) :
    (if t is Tqualified _ _ then false else
       is_value_type t || match t with
                        | Tref _ => true
                        | _ => false
                        end) = false ->
    Is_true (is_heap_type t) -> False.
  Proof.
    rewrite /is_heap_type.
    destruct t; try (move => ->; rewrite andb_false_r; inversion 1).
    intros. case_bool_decide; try inversion H0.
    by symmetry in H1; apply unqual_erase_qualifiers in H1.
  Qed.

  (**
  For value types and reference types, [anyR] coincides with
  [tptstoR].
  *)
  Lemma tptstoR_anyR_val : ∀ t q v,
      tptstoR t q v |-- anyR t q.
  Proof.
    induction t; simpl; try tauto.
    all: try solve [
             intros;
             iIntros "H"; iDestruct (observe [| is_heap_type _ |] with "H") as "%H";
             exfalso; revert H;
             apply not_heap_type; reflexivity
           | intros; rewrite anyR.unlock everywhereR_unfold/primitiveR/=; eauto ].
    { (* pointers *)
      iIntros (??) "H".
      iDestruct (observe [| is_heap_type _ |] with "H") as "%H".
      rewrite anyR.unlock everywhereR_unfold/primitiveR/=.
      iExists v; iStopProof. f_equiv.
      rewrite /is_heap_type in H.
      case_bool_decide; auto. exfalso; done. }
    { (* ref *)
      iIntros (??) "H".
      iDestruct (observe [| is_heap_type _ |] with "H") as "%H".
      rewrite anyR.unlock everywhereR_unfold/primitiveR/=.
      iExists v; iStopProof. f_equiv.
      rewrite /is_heap_type in H.
      case_bool_decide; auto. exfalso; done. }
    { (* member_pointer *)
      iIntros (??) "H".
      iDestruct (observe [| is_heap_type _ |] with "H") as "%H".
      rewrite anyR.unlock everywhereR_unfold/primitiveR/=.
      iExists v; iStopProof. f_equiv.
      rewrite /is_heap_type in H.
      case_bool_decide; auto. exfalso; done. }
  Qed.

  Lemma anyR_tptstoR_val : ∀ t q,
      is_value_type t ->
      anyR t q |-- Exists v, tptstoR (erase_qualifiers (decompose_type t).2) (qualify (decompose_type t).1 q) v.
  Proof.
    induction t; simpl; try tauto;
      try solve [
                    intros; rewrite anyR.unlock/everywhereR/=;
          iIntros "X"; iDestruct "X" as (f) "X";
            destruct f; [ iDestruct "X" as "[]" | simpl; eauto ]

          | intros; rewrite anyR.unlock/everywhereR/=;
          iSplit;
          [ iIntros "X"; iDestruct "X" as (f) "X";
            destruct f; [ iDestruct "X" as "[]" | simpl; eauto ]
          | iIntros "X"; iExists 1; simpl; auto ] ].
    { intros. rewrite anyR_Tqualified IHt; first last.
      { rewrite -is_value_type_drop_qualifiers in H.
        simpl in H.
        rewrite -is_value_type_drop_qualifiers; done. }
      f_equiv. intro.
      rewrite -erase_qualifiers_decompose_type.
      Opaque decompose_type.
      rewrite qual_norm_decompose_type. simpl.
      rewrite -erase_qualifiers_decompose_type/=.
      f_equiv.
      rewrite decompose_type_qual/=.
      by rewrite qualify_merge_tq merge_tq_comm.
      Transparent decompose_type. }
  Qed.
  Lemma anyR_tptstoR_ref t q :
      anyR (Tref t) q -|- Exists v, tptstoR (Tref (erase_qualifiers t)) q v.
  Proof.
    (* todo: should be derived for [typeR] *)
    intros.
    rewrite anyR.unlock.
    rewrite everywhereR_unfold/=.
    rewrite /primitiveR/=. eauto.
  Qed.
  Lemma anyR_tptstoR_rv_ref t q :
      anyR (Trv_ref t) q -|- Exists v, tptstoR (Tref (erase_qualifiers t)) q v.
  Proof.
    intros.
    rewrite anyR.unlock.
    rewrite everywhereR_unfold/=.
    rewrite /primitiveR/=. eauto.
  Qed.

  Lemma initializedR_anyR : ∀ t q v,
      initializedR t q v |-- anyR t q.
  Proof.
    intros.
    rewrite initializedR.unlock.
    iIntros "(#HT&Hp)".
    iDestruct (observe [| has_type_prop _ _ |] with "HT") as %Ht.
    rewrite tptsto_fuzzyR.unlock.
    iDestruct "Hp" as (?) "[% Hp]".
    rewrite -tptstoR_anyR_val. eauto.
  Qed.

  Lemma primR_anyR : ∀ t q v,
      primR t q v |-- anyR t q.
  Proof.
    intros.
    rewrite primR.unlock initializedR_anyR.
    iIntros "[% $]".
  Qed.
  Lemma uninitR_anyR : ∀ t q,
      uninitR t q |-- anyR t q.
  Proof.
    intros.
    rewrite uninitR.unlock.
    rewrite -tptstoR_anyR_val. eauto.
  Qed.


  Lemma tptstoR_anyR_ref t q v :
    tptstoR (Tref t) q v |-- anyR (Tref t) q.
  Proof.
    intros. rewrite anyR_tptstoR_ref.
    iIntros "H"; iExists _.
    iDestruct (observe [| is_heap_type _ |] with "H") as "%H".
    rewrite /is_heap_type in H.
    case_bool_decide; auto. rewrite H0. eauto. exfalso; done.
  Qed.

  Lemma anyR_tptsto_fuzzyR_val_2 t q v :
    is_value_type t -> tptsto_fuzzyR t q v |-- anyR t q.
  Proof.
    intros. rewrite tptsto_fuzzyR.unlock. iIntros "(% & % & R)".
    rewrite -tptstoR_anyR_val; eauto.
  Qed.

  #[global] Instance anyR_type_ptr_observe ty q :
    TCSimpl match to_heap_type ty with
            | Tarray _ _ => false
            | _ => true
            end true →
    Observe (type_ptrR $ to_heap_type ty) (anyR ty q).
  Proof.
    intros; rewrite anyR.unlock.
    rewrite everywhereR_unfold.
    revert q; induction ty; simpl; refine _; simpl in *; try tauto.
    { inversion H. }
    { case_match; refine _.
      case_match; refine _. }
  Qed.

  #[global]
  Instance anyR_valid_observe {ty q} : Observe validR (anyR ty q).
  Proof.
    rewrite anyR.unlock /everywhereR.
    iIntros "H"; iDestruct "H" as (?) "H". iStopProof.
    apply everywhereR_f_valid.
    rewrite /primitiveR. intros.
    iIntros "H"; iDestruct "H" as (?) "H".
    iStopProof.
    case_match; try solve [ iIntros "X"; iDestruct (observe validR with "X") as "$" ].
  Qed.

  #[global] Instance anyR_nonnull_observe : ∀ {ty q},
      TCSimpl (zero_sized_array ty) false ->
      Observe nonnullR (anyR ty q).
  Proof.
    rewrite anyR.unlock /everywhereR. intros.
    iIntros "H"; iDestruct "H" as (?) "H". iStopProof.
    apply everywhereR_f_nonnull; eauto.
    rewrite /primitiveR. intros.
    iIntros "H"; iDestruct "H" as (?) "H".
    iStopProof.
    case_match; try solve [ iIntros "X"; iDestruct (observe nonnullR with "X") as "$" ].
    inversion H as [H1]; rewrite H1. auto.
  Qed.

  (** decompose a struct into its constituent fields and base classes. *)
  Lemma anyR_struct : forall cls st q,
    glob_def σ cls = Some (Gstruct st) ->
        anyR (Tnamed cls) q
    -|- Reduce (struct_defR anyR cls st q).
  Proof.
    intros. rewrite {1}anyR.unlock everywhereR_unfold/=.
    have->: types (genv_tu σ) !! cls = Some (Gstruct st) by done.
    rewrite /struct_defR anyR.unlock.
    iSplit; iIntros "($&$&$)".
  Qed.

  (** decompose a union into the classical disjunction of the alternatives
   *)
  Lemma anyR_union : forall cls un q,
    glob_def σ cls = Some (Gunion un) ->
        anyR (Tnamed cls) q
    -|- Reduce (union_defR anyR cls un q).
  Proof.
    intros. rewrite {1}anyR.unlock everywhereR_unfold/=.
    have->: types (genv_tu σ) !! cls = Some (Gunion un) by done.
    rewrite /union_defR anyR.unlock.
    done.
  Qed.

  (** Proof requires the generalization of [anyR] to support aggregates (and arrays) *)
  Lemma anyR_array_0 t q :
    anyR (Tarray t 0) q -|- validR ** [| is_Some (size_of σ t) |].
  Proof.
    rewrite anyR.unlock everywhereR_unfold/=.
    by rewrite replicateN_0 arr.arrayR_nil.
  Qed.

  Lemma anyR_array_succ t n q :
    anyR (Tarray t (N.succ n)) q -|-
    type_ptrR t ** anyR t q ** .[ t ! 1 ] |-> anyR (Tarray t n) q.
  Proof.
    rewrite anyR.unlock everywhereR_unfold/=.
    rewrite replicateN_S arr.arrayR_cons !everywhereR_unfold.
    f_equiv. f_equiv. simpl. done.
  Qed.

  (** decompose an array into individual components
      note that one past the end of an array is a valid location, but
      it doesn't store anything.

      TODO this should move
   *)
  Lemma anyR_array' t n q :
        anyR (Tarray t n) q
    -|- arr.arrayR t (fun _ => anyR t q) (replicateN n ()).
  Proof.
    induction n using N.peano_ind;
      rewrite (replicateN_0, replicateN_S) (arr.arrayR_nil, arr.arrayR_cons).  {
      apply anyR_array_0.
    }
    by rewrite -IHn anyR_array_succ.
  Qed.

  (* Wrapper using [repeat] instead of [replicate] for compatibility. *)
  Lemma anyR_array t n q :
        anyR (Tarray t n) q
    -|- arr.arrayR t (fun _ => anyR t q) (repeat () (N.to_nat n)).
  Proof. by rewrite anyR_array' repeatN_replicateN. Qed.

  Lemma _at_anyR_ptr_congP_transport : forall p p' ty q,
    ptr_congP σ p p' ** type_ptr ty p' |-- p |-> anyR ty q -* p' |-> anyR ty q.
  Proof. (* TODO: this is very interesting *) Admitted.

End with_cpp.

#[deprecated(since="20231127",note="use [tptstoR_anyR_val].")] Notation anyR_tptstoR_val_2 := tptstoR_anyR_val (only parsing).
