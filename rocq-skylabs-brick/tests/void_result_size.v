(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.semantics.
Require Import skylabs.lang.cpp.logic.heap_pred.
Require Import skylabs.iris.extra.proofmode.proofmode.

Section with_cpp.
  Context `{Σ : cpp_logic} {σ : genv}.

  Example void_result_has_one_byte : size_of σ Tvoid = Some 1%N.
  Proof. reflexivity. Qed.

  Example void_result_typeclass_size : SizeOf Tvoid 1.
  Proof. typeclasses eauto. Qed.

  Example void_result_array_size n : size_of σ (Tarray Tvoid n) = Some n.
  Proof. by rewrite /= N.mul_1_r. Qed.

  Example void_result_array_stride i :
    eval_offset σ (o_sub σ Tvoid i) = Some i.
  Proof. by rewrite (eval_o_sub' 1) //= Z.mul_1_l. Qed.

  (* This is the original contradiction produced by a void result cell. *)
  Lemma primR_void_false (p : ptr) q v : p |-> primR Tvoid q v |-- False.
  Proof.
    iIntros "R".
    iDestruct (observe (p |-> type_ptrR Tvoid) with "R") as "#T".
    rewrite _at_type_ptrR type_ptr_size.
    Fail by iDestruct "T" as %[? ?].
  Abort.
End with_cpp.
