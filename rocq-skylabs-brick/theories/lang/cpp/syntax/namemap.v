(*
 * Copyright (c) 2024-2025 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import Stdlib.Structures.OrderedTypeAlt.
Require Import Stdlib.FSets.FMapAVL.
Require Import skylabs.prelude.avl.
Require Import skylabs.prelude.compare.
Require Import skylabs.lang.cpp.syntax.prelude.
Require Import skylabs.lang.cpp.syntax.core.
Require Import skylabs.lang.cpp.syntax.compare.

(** ** Name maps *)

Module Import internal.

  Module NameMap.
    Module Compare.
      Definition t : Type := name.
      #[local] Definition compare : t -> t -> comparison := compareN.
      #[local] Infix "?=" := compare.
      #[local] Lemma compare_sym x y : (y ?= x) = CompOpp (x ?= y).
      Proof. exact: compare_antisym. Qed.
      #[local] Lemma compare_trans c x y z : (x ?= y) = c -> (y ?= z) = c -> (x ?= z) = c.
      Proof. exact: base.compare_trans. Qed.
    End Compare.
    Module Key := OrderedType_from_Alt Compare.
    Lemma eqL : forall a b, Key.eq a b -> @eq _ a b.
    Proof. apply LeibnizComparison.cmp_eq; refine _. Qed.
    Include FMapAVL.Make Key.
    Include FMapExtra.MIXIN Key.
    Include FMapExtra.MIXIN_LEIBNIZ Key.
  End NameMap.

End internal.

Module NM.
  Include NameMap.
End NM.

Module TM.
  Include NameMap.
End TM.

Module TPMap.
  (* Map over [temp_param] *)

  (* TODO: the need for this suggests some oddity in the setup of the
     [Compare] and [Comparison] typeclasses. *)
  #[local] Hint Transparent base.compare : typeclass_instances.

  Module Compare.
    Definition t : Type := temp_param.
    #[local] Definition compare : t -> t -> comparison := temp_param_compare.
    #[local] Infix "?=" := compare.
    #[local] Lemma compare_sym x y : (y ?= x) = CompOpp (x ?= y).
    Proof. exact: compare_antisym. Qed.
    #[local] Lemma compare_trans c x y z : (x ?= y) = c -> (y ?= z) = c -> (x ?= z) = c.
    Proof. exact: compare_trans. Qed.
  End Compare.
  Module Key := OrderedType_from_Alt Compare.
  Lemma eqL : forall a b, Key.eq a b -> @eq _ a b.
  Proof. apply LeibnizComparison.cmp_eq; refine _. Qed.
  Include FMapAVL.Make Key.
  Include FMapExtra.MIXIN Key.
  Include FMapExtra.MIXIN_LEIBNIZ Key.
End TPMap.
