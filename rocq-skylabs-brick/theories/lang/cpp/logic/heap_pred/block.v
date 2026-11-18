(*
 * Copyright (c) 2023 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.lang.cpp.logic.heap_pred.prelude.
Require Import skylabs.lang.cpp.logic.heap_pred.valid.
Require Import skylabs.lang.cpp.logic.heap_pred.null.
Require Import skylabs.lang.cpp.logic.heap_pred.simple.
Require Import skylabs.lang.cpp.logic.heap_pred.any.

Import rep_defs.INTERNAL. (* for access to [unfold_at] *)


#[local] Set Printing Coercions.
Implicit Types (σ : genv) (p : ptr) (o : offset).

Section with_cpp.
  Context `{Σ : cpp_logic} {σ : genv}.

  (** [blockR sz q] represents [q] ownership of a contiguous chunk of
      [sz] bytes without any C++ structure on top of it. *)
  Definition blockR_def {σ} sz (q : cQp.t) : Rep :=
    _offsetR (o_sub σ Tbyte (Z.of_N sz)) validR **
    (* ^ Encodes valid_ptr (this .[ Tbyte ! sz]). This is
    necessary to get [l |-> blockR n -|- l |-> blockR n ** l .[ Tbyte ! m] |-> blockR 0]. *)
    [∗list] i ∈ seq 0 (N.to_nat sz),
      _offsetR (o_sub σ Tbyte (Z.of_nat i)) (anyR Tbyte q).
  Definition blockR_aux : seal (@blockR_def). Proof. by eexists. Qed.
  Definition blockR := blockR_aux.(unseal).
  Definition blockR_eq : @blockR = _ := blockR_aux.(seal_eq).
  #[global] Arguments blockR {_} _%_N _%_cQp.

  #[global] Instance blockR_timeless sz q :
    Timeless (blockR sz q).
  Proof. rewrite blockR_eq /blockR_def. unfold_at. apply _. Qed.
  #[global] Instance blockR_cfractional sz :
    CFractional (blockR sz).
  Proof. rewrite blockR_eq. apply _. Qed.
  #[global] Instance blockR_as_cfractional sz :
    AsCFractional0 (blockR sz).
  Proof. solve_as_cfrac. Qed.

  #[global] Instance blockR_observe_frac_valid sz :
    TCLt (0 ?= sz)%N ->
    CFracValid0 (blockR sz).
  Proof.
    rewrite TCLt_N blockR_eq/blockR_def. intros.
    destruct (N.to_nat sz) eqn:?; [ lia | ] => /=.
    try solve_cfrac_valid.
  Qed.

  Lemma nullptr_blockR sz q :
    nullptr |-> blockR sz q |-- [| sz = 0%N |].
  Proof.
    rewrite blockR_eq/blockR_def _at_sep.
    elim /N.peano_ind: sz => [|sz _] /=. by eauto.
    rewrite N2Nat.inj_succ /= _offsetR_sub_0 //.
    iIntros "(_&B&_)".
    iDestruct (observe (nullptr |-> nonnullR) with "B") as "X".
    rewrite _at_nonnullR.
    by iDestruct "X" as %[].
  Qed.

  Lemma blockR_disjoint (l : ptr):
    l |-> blockR 1 1$m |-- l |-> blockR 1 1$m -* False.
  Proof.
    iIntros "K L". iCombine "K L" as "P".
    by iDestruct (observe [| _ ≤ 1 |]%Qp with "P") as %?.
  Qed.

  #[global] Instance blockR_nonnull n q :
    TCLt (0 ?= n)%N -> Observe nonnullR (blockR n q).
  Proof.
    rewrite TCLt_N blockR_eq/blockR_def.
    destruct (N.to_nat n) eqn:Hn; [ lia | ] => {Hn} /=.
    rewrite _offsetR_sub_0; last done.
    assert (TCEq (zero_sized_array Tbyte) false) by done.
    apply _.
  Qed.
  #[global] Instance blockR_valid_ptr sz q : Observe validR (blockR sz q).
  Proof.
    rewrite blockR_eq/blockR_def.
    elim /N.peano_ind: sz => [|sz _] /=.
    { rewrite _offsetR_sub_0 //. apply _. }
    { apply observe_sep_r.
      rewrite N2Nat.inj_succ /=.
      apply observe_sep_l.
      rewrite _offsetR_sub_0 //.
      apply _. }
  Qed.

End with_cpp.

(** * Typed storage

[tblockR ty q] is [q] ownership of the storage that an object of type [ty]
occupies, before construction or after destruction, wherever that object
sits. Constructors consume it and destructors return it.

[tblockR] is abstract, not a definition, because the storage an object owns
depends on its position for class types. A potentially-overlapping
subobject, i.e. a base class subobject or a <<[[no_unique_address]]>> member
(<https://eel.is/c++draft/intro.object#7>), need not own its tail padding:
the ABI may place another member there. So the storage of a class object
may be smaller than [size_of σ ty], and a destructor cannot hand back
[size_of σ ty] bytes. The axioms below describe [tblockR] as [blockR] only
for types that contain no class: for class types, nothing relates [tblockR]
to [size_of]. An array element is never potentially overlapping, but its
storage is still described by its element type's [tblockR].

A definition could only replace this [Parameter] once the logic knows each
class's data size, which cpp2v does not record. The full-size definition
used before ([blockR sz q ** alignedR al]) satisfies all of these axioms. *)
Parameter tblockR : forall `{Σ : cpp_logic} {σ : genv} (ty : Rtype) (q : cQp.t), Rep.

(** Types whose [tblockR] is plain bytes: types that contain no class and
    are not arrays. Arrays are described element-wise by [tblockR_array_unfold]. *)
Fixpoint tblockR_raw_type (ty : type) : bool :=
  match ty with
  | Tnamed _ | Tarray _ _ => false
  | Tqualified _ t => tblockR_raw_type t
  | _ => true
  end.

Section tblockR.
  Context `{Σ : cpp_logic} {σ : genv}.

  (** The storage of a type without classes: [size_of σ ty] bytes, aligned. *)
  Definition tblockR_raw (ty : Rtype) (q : cQp.t) : Rep :=
    match size_of σ ty , align_of ty with
    | Some sz , Some al => blockR sz q ** alignedR al
    | _ , _  => False
    end.

  Axiom tblockR_raw_eq : forall ty q,
    tblockR_raw_type ty ->
    tblockR ty q -|- tblockR_raw ty q.

  (** Array storage is its elements' storage at byte offsets, together with
      the validity of the end pointer and the array's alignment. Unsized
      element types have no storage. *)
  Axiom tblockR_array_unfold : forall t n q,
    tblockR (Tarray t n) q -|-
    match size_of σ t with
    | Some sz =>
        aligned_ofR t **
        .[ Tbyte ! Z.of_N (n * sz) ] |-> validR **
        [∗list] i ∈ seq 0 (N.to_nat n),
          .[ Tbyte ! Z.of_N (N.of_nat i * sz) ] |-> tblockR t q
    | None => False
    end.

  Axiom tblockR_timeless : forall ty q, Timeless (tblockR ty q).
  Axiom tblockR_cfractional : forall ty, CFractional (tblockR ty).
  Axiom tblockR_observe_frac_valid : forall ty n,
    SizeOf ty n -> TCLt (0 ?= n)%N -> CFracValid0 (tblockR ty).
  Axiom tblockR_nonnull : forall n ty q,
    SizeOf ty n -> TCLt (0 ?= n)%N -> Observe nonnullR (tblockR ty q).
  Axiom tblockR_valid_ptr : forall ty q, Observe validR (tblockR ty q).

  #[global] Existing Instances tblockR_timeless tblockR_cfractional
    tblockR_observe_frac_valid tblockR_nonnull tblockR_valid_ptr.

  #[global] Instance tblockR_as_cfractional ty : AsCFractional0 (tblockR ty).
  Proof. solve_as_cfrac. Qed.
End tblockR.
