(*
 * Copyright (c) 2023 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bluerock.lang.cpp.logic.heap_pred.prelude.

#[local] Set Printing Coercions.
Implicit Types (σ : genv) (p : ptr) (o : offset).

Section with_cpp.
  Context `{Σ : cpp_logic} {σ : genv}.

  (* TODO:  requires [σ] *)
  Definition validR_def : Rep := as_Rep valid_ptr.
  Definition validR_aux : seal (@validR_def). Proof. by eexists. Qed.
  Definition validR := validR_aux.(unseal).
  Definition validR_eq : @validR = _ := validR_aux.(seal_eq).

  (* TODO: requires [σ] *)
  Definition svalidR_def : Rep := as_Rep strict_valid_ptr.
  Definition svalidR_aux : seal (@svalidR_def). Proof. by eexists. Qed.
  Definition svalidR := svalidR_aux.(unseal).
  Definition svalidR_eq : @svalidR = _ := svalidR_aux.(seal_eq).

  Definition type_ptrR_def (t : Rtype) : Rep := as_Rep (@type_ptr _ _ _ σ t).
  Definition type_ptrR_aux : seal (@type_ptrR_def). Proof. by eexists. Qed.
  Definition type_ptrR := type_ptrR_aux.(unseal).
  Definition type_ptrR_eq : @type_ptrR = _ := type_ptrR_aux.(seal_eq).

  #[global] Instance validR_persistent : Persistent validR.
  Proof. rewrite validR_eq; refine _. Qed.
  #[global] Instance validR_timeless : Timeless validR.
  Proof. rewrite validR_eq; refine _. Qed.
  #[global] Instance validR_affine : Affine validR.
  Proof. rewrite validR_eq; refine _. Qed.

  Import rep_defs.INTERNAL.

  Lemma monPred_at_validR p : validR p -|- valid_ptr p.
  Proof. by rewrite validR_eq. Qed.
  Lemma _at_validR (p : ptr) : _at p validR -|- valid_ptr p.
  Proof. by rewrite validR_eq _at_eq. Qed.

  #[global] Instance svalidR_persistent : Persistent svalidR.
  Proof. rewrite svalidR_eq; refine _. Qed.
  #[global] Instance svalidR_timeless : Timeless svalidR.
  Proof. rewrite svalidR_eq; refine _. Qed.
  #[global] Instance svalidR_affine : Affine svalidR.
  Proof. rewrite svalidR_eq; refine _. Qed.

  Lemma monPred_at_svalidR p : svalidR p -|- strict_valid_ptr p.
  Proof. by rewrite svalidR_eq. Qed.
  Lemma _at_svalidR (p : ptr) : _at p svalidR -|- strict_valid_ptr p.
  Proof. by rewrite svalidR_eq _at_eq. Qed.

  #[global] Instance type_ptrR_persistent t : Persistent (type_ptrR t).
  Proof. rewrite type_ptrR_eq; refine _. Qed.
  #[global] Instance type_ptrR_timeless t : Timeless (type_ptrR t).
  Proof. rewrite type_ptrR_eq; refine _. Qed.
  #[global] Instance type_ptrR_affine t : Affine (type_ptrR t).
  Proof. rewrite type_ptrR_eq; refine _. Qed.

  Lemma monPred_at_type_ptrR ty p : type_ptrR ty p -|- type_ptr ty p.
  Proof. by rewrite type_ptrR_eq. Qed.
  Lemma _at_type_ptrR (p : ptr) ty : _at p (type_ptrR ty) -|- type_ptr ty p.
  Proof. by rewrite type_ptrR_eq _at_eq. Qed.

  Lemma svalidR_validR : svalidR |-- validR.
  Proof.
    rewrite validR_eq/validR_def svalidR_eq/svalidR_def.
    constructor =>p /=. by apply strict_valid_valid.
  Qed.
  Lemma type_ptrR_svalidR ty : type_ptrR ty |-- svalidR.
  Proof.
    rewrite type_ptrR_eq/type_ptrR_def svalidR_eq/svalidR_def.
    constructor =>p /=. by apply type_ptr_strict_valid.
  Qed.
  Lemma type_ptrR_validR ty : type_ptrR ty |-- validR.
  Proof. by rewrite type_ptrR_svalidR svalidR_validR. Qed.

  #[global] Instance svalidR_validR_observe : Observe validR svalidR.
  Proof. rewrite svalidR_validR. red; iIntros "#$". Qed.
  #[global] Instance type_ptrR_svalidR_observe t : Observe svalidR (type_ptrR t).
  Proof. rewrite type_ptrR_svalidR; red; iIntros "#$". Qed.

  Lemma off_validR o
    (Hv : ∀ p, valid_ptr (p ,, o) |-- valid_ptr p) :
    _offsetR o validR |-- validR.
  Proof.
    apply Rep_entails_at => p. by rewrite _at_offsetR !_at_validR.
  Qed.

  Lemma _field_validR f : _offsetR (_field f) validR |-- validR.
  Proof. apply off_validR => p. apply _valid_ptr_field. Qed.

  #[global] Instance type_ptrR_size_observe ty :
    Observe [| is_Some (size_of σ ty) |] (type_ptrR ty).
  Proof.
    apply monPred_observe_only_provable => p.
    rewrite monPred_at_type_ptrR. apply _.
  Qed.

End with_cpp.

#[global] Typeclasses Opaque type_ptrR validR svalidR.
#[global] Opaque type_ptrR validR svalidR.
