(*
 * Copyright (c) 2020-2025 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
(**
This file axiomatizes and instantiates [mpred] with the ghost types of the logic
that we use for C++.
The core C++ logic is defined in [pred.v]. *)
Require Import iris.base_logic.lib.own.
Require Import iris.base_logic.lib.cancelable_invariants.
Require Import iris.bi.monpred.

Require Import bluerock.prelude.base.
Require Import bluerock.iris.extra.bi.prelude.
Require Export bluerock.iris.extra.base_logic.mpred.
Require Export bluerock.iris.extra.algebra.commons.
Import ChargeNotation.

Module Type CPP_LOGIC_CLASS_BASE.
  Parameter cppPreG : gFunctors -> Type.
  Axiom has_inv : forall Σ, cppPreG Σ -> invGS Σ.
  Axiom has_brG : forall Σ, cppPreG Σ -> br.ghost.G Σ.

  Parameter _cpp_ghost : Type.
End CPP_LOGIC_CLASS_BASE.

Module Type CPP_LOGIC_CLASS_MIXIN (Import CC : CPP_LOGIC_CLASS_BASE).

  (* In Iris idiom, this corresponds to a cppG *)
  Class cpp_logic {thread_info : biIndex} {_Σ : gFunctors} : Type :=
  { cpp_ghost    : _cpp_ghost
  ; cpp_has_cppG : cppPreG _Σ
  }.
  #[global] Arguments cpp_logic : clear implicits.
  #[global] Hint Mode cpp_logic - - : cpp_logic.

  #[global] Instance cpp_has_inv `{!cpp_logic thread_info _Σ} : invGS _Σ
    := has_inv _Σ cpp_has_cppG.

  #[global] Instance cpp_has_br_ghost `{!cpp_logic thread_info _Σ} : br.ghost.G _Σ
    := has_brG _Σ cpp_has_cppG.

  #[local] Existing Instance br.ghost.frac_inG.
  #[global] Instance cpp_has_cinv `{!cpp_logic thread_info _Σ} : cinvG _Σ.
  Proof. constructor. apply _. Qed.

  #[global] Hint Opaque cpp_has_inv cpp_has_br_ghost cpp_has_cinv
  : typeclass_instances br_opacity.

End CPP_LOGIC_CLASS_MIXIN.

Module Type CPP_LOGIC_CLASS := CPP_LOGIC_CLASS_BASE <+ CPP_LOGIC_CLASS_MIXIN.

Declare Module LC : CPP_LOGIC_CLASS.
Export LC.
