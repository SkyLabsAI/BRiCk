(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import iris.bi.bi.

(* [siProp] lemmas missing from upstream Iris. *)
Lemma si_prop_affinely (P : siProp) : <affine> P ⊣⊢@{siProp} P.
Proof. by rewrite /bi_affinely left_id. Qed.

Lemma si_prop_emp : emp ⊣⊢@{siProp} True.
Proof. done. Qed.

Section with_sbi.
  Context `{Sbi PROP}.

  Lemma si_pure_True : <si_pure> True ⊣⊢@{PROP} True.
  Proof. apply si_pure_pure. Qed.

  Lemma si_pure_False : <si_pure> False ⊣⊢@{PROP} False.
  Proof. apply si_pure_pure. Qed.

  Lemma si_pure_emp : <si_pure> emp ⊣⊢@{PROP} True.
  Proof. by rewrite si_prop_emp si_pure_True. Qed.

  Lemma si_pure_affinely (P : siProp) :
    <si_pure> <affine> P ⊣⊢@{PROP} <si_pure> P.
  Proof. by rewrite /bi_affinely left_id. Qed.
End with_sbi.
