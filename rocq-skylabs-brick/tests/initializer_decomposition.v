(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.prelude.base.
Require Import skylabs.iris.extra.bi.errors.
Require Import skylabs.lang.cpp.logic.

Set Default Proof Using "Type*".

Section with_cpp.
  Context `{Σ : cpp_logic} {σ : genv}.
  Context (tu : translation_unit) (ρ : region) (addr : ptr) (e : Expr)
    (Q : FreeTemps -> epred).

  (* This case was absent from the view, making its totality theorem false. *)
  Example unresolved_auto_case :
    wp_initialize_decomp_spec tu ρ Tauto addr e Q
      (UNSUPPORTED (initializing_type Tauto e)).
  Proof. apply WpInitUnsupported with (cv := QM); done. Qed.

  Example qualified_unresolved_case :
    wp_initialize_decomp_spec tu ρ (Tconst Tauto) addr e Q
      (UNSUPPORTED (initializing_type Tauto e)).
  Proof. apply WpInitUnsupported with (cv := QC); done. Qed.

  Example unresolved_decltype_case :
    wp_initialize_decomp_spec tu ρ (Tdecltype e) addr e Q
      (UNSUPPORTED (initializing_type (Tdecltype e) e)).
  Proof. apply WpInitUnsupported with (cv := QM); done. Qed.

  (* The qualifier belongs to the reference cell here. Its referent is erased
     in the representation, and initialization accepts a glvalue. *)
  Example const_reference_case :
    wp_initialize_decomp_spec tu ρ (Tconst "const int&") addr e Q
      (wp_glval tu ρ e (fun p free =>
        addr |-> primR "int&" 1$c (Vref p) -* Q free)).
  Proof. apply WpInitRef with (cv := QC) (ty' := "const int"%cpp_type); done. Qed.

  Example const_rvalue_reference_case :
    wp_initialize_decomp_spec tu ρ (Tconst "const int&&") addr e Q
      (wp_xval tu ρ e (fun p free =>
        addr |-> primR "int&" 1$c (Vref p) -* Q free)).
  Proof. apply WpInitRvRef with (cv := QC) (ty' := "const int"%cpp_type); done. Qed.

  Example volatile_reference_case :
    wp_initialize_decomp_spec tu ρ (Tvolatile "int&") addr e Q False.
  Proof. apply WpInitVolatile with (cv := QV) (ty' := "int&"%cpp_type); done. Qed.
End with_cpp.

(* Guard against replacing the exhaustive proof by another admission. *)
Set Printing Width 4611686018427387903.
Set Printing Fully Qualified.
Print Assumptions wp_initialize_decomp_ok.
