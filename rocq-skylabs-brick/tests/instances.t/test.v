(*
 * Copyright (c) 2025 BlueRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bluerock.lang.cpp.algebra.cfrac.
Require Import bluerock.lang.cpp.logic.arr.
(* Require Import bluerock.lang.cpp.logic.rep_defs. *)
(* Require Import bluerock.lang.cpp.logic.mpred. *)
Require Import bluerock.lang.cpp.logic.

Section with_cpp.
  (* Context `{Σ : cpp_logic}. *)
  Context `{Σ : cpp_logic, σ : genv}.
  (* Context `{Σ : cpp_logic, module ⊧ σ}. *)

  Section cQp.
    Context {A} {R : cQp.t -> A -> Rep} (xs : list A) (q : cQp.t) (ty : type).

    Example foo `{!forall q x, AsCFractional (R q x) (fun q' => R q' x) q} : True.
    Proof.
      eassert (Hfrac : AsCFractional (arrayR ty (R q) xs) _ _).
      {
        apply _. }
      simpl in Hfrac.
      assert (AsCFractional (arrayR ty (R q) xs) (λ q0 : cQp.t, arrayR ty (λ x : A, R q0 x) xs) q);
        first apply Hfrac.
    Abort.

    Example foo `{!CFractional1 R} : True.
    Proof.
      eassert (Hfrac : AsCFractional (arrayR ty (R q) xs) _ _).
      {
        Fail apply _.
    Abort.

  End cQp.

  Section Qp.
    Context {A} {R : Qp -> A -> Rep} (xs : list A) (q : Qp) (ty : type).
    Import fractional.

    Example foo `{!forall q x, AsFractional (R q x) (fun q' => R q' x) q} : True.
    Proof.
      eassert (Hfrac : AsFractional (arrayR ty (R q) xs) _ _).
      { apply _. }
      simpl in Hfrac.
      assert (AsFractional (arrayR ty (R q) xs) (λ q0 : Qp, arrayR ty (λ x : A, R q0 x) xs) q);
        first apply Hfrac.
    Abort.

    Example foo `{!Fractional1 R} : True.
    Proof.
      eassert (Hfrac : AsFractional (arrayR ty (R q) xs) _ _).
      {
        Fail apply _.
    Abort.

  End Qp.


End with_cpp.
