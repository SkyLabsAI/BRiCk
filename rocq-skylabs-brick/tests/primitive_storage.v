(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.iris.extra.proofmode.proofmode.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.semantics.
Require Import skylabs.lang.cpp.logic.heap_pred.
Require Import skylabs.lang.cpp.logic.raw.
Require Import skylabs.lang.cpp.logic.object_repr.

Set Default Proof Using "Type*".

Section with_cpp.
  Context `{Σ : cpp_logic} {σ : genv}.
  Example empty_raw_storage (q : cQp.t) (P : Rep) :
    rawsR q [] ** P |-- blockR 0 q ** P.
  Proof. by rewrite rawsR_blockR. Qed.

  Example three_raw_bytes (q : cQp.t) (r1 r2 r3 : raw_byte) (P : Rep) :
    rawsR q [r1; r2; r3] ** P |-- blockR 3 q ** P.
  Proof. by rewrite rawsR_blockR. Qed.

  (* Recover only one permission share, retaining the initialized value in
     the other share and preserving an arbitrary unrelated frame. *)
  Example split_primitive_storage (ty : Rtype) (v : val)
      (q1 q2 : cQp.t) (P : Rep) :
    primR ty (q1 + q2) v ** P |--
    (tblockR ty q1 ** primR ty q2 v) ** P.
  Proof.
    rewrite (cfractional (P:=fun q => primR ty q v) q1 q2).
    by rewrite {1}primR_tblockR.
  Qed.

  Example readonly_reference_storage (p : ptr) :
    primR "int&" 1$c (Vref p) |-- tblockR "int&" 1$c.
  Proof. apply primR_tblockR. Qed.

  Example member_pointer_storage (cls ty : Rtype) (q : cQp.t) (v : val) :
    primR (Tmember_pointer cls ty) q v |-- blockR (member_pointer_size σ) q.
  Proof.
    rewrite primR_tblockR /tblockR /=.
    destruct (align_of_size_of' (σ:=σ) (Tmember_pointer cls ty)
      (member_pointer_size σ) eq_refl) as (al & Hal & _).
    rewrite Hal. by iIntros "[$ _]".
  Qed.

  (* Long-double bytes stay abstract; storage recovery needs only their length. *)
  Example long_double_storage (q : cQp.t) (v : val) :
    primR "long double" q v |-- blockR 16 q.
  Proof.
    rewrite primR_tblockR /tblockR /=.
    destruct (align_of_size_of' (σ:=σ) "long double" 16 eq_refl) as (al & Hal & _).
    rewrite Hal. by iIntros "[$ _]".
  Qed.

  Example zero_sized_primitive_rejected (ty : Rtype) (q : cQp.t) (v : val) :
    size_of σ ty = Some 0%N ->
    primR ty q v |-- False.
  Proof.
    intros Hsz. iIntros "P".
    iDestruct (primR_size_nonzero with "P") as %Hnz. by contradiction.
  Qed.

End with_cpp.

Set Printing Width 4611686018427387903.
Set Printing Fully Qualified.
