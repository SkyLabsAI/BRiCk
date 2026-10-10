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
      #[local] Instance compare : base.Compare t := _.
      #[local] Infix "?=" := compare.
      #[local] Lemma compare_sym x y : (y ?= x) = CompOpp (x ?= y).
      Proof. exact: (compare_antisym (f:=base.compare (A:=t))). Qed.
      #[local] Lemma compare_trans c x y z : (x ?= y) = c -> (y ?= z) = c -> (x ?= z) = c.
      Proof. exact: (base.compare_trans (f:=base.compare (A:=t))). Qed.
    End Compare.
    Module Key := OrderedType_from_Alt Compare.
    Lemma eqL : forall a b, Key.eq a b -> @eq _ a b.
    Proof. exact (LeibnizComparison.cmp_eq (base.compare (A:=Compare.t))). Qed.
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

  Module Compare.
    Definition t : Type := temp_param.
    #[local] Instance compare : base.Compare t := _.
    #[local] Infix "?=" := compare.
    #[local] Lemma compare_sym x y : (y ?= x) = CompOpp (x ?= y).
    Proof. exact: (compare_antisym (f:=base.compare (A:=t))). Qed.
    #[local] Lemma compare_trans c x y z : (x ?= y) = c -> (y ?= z) = c -> (x ?= z) = c.
    Proof. exact: (base.compare_trans (f:=base.compare (A:=t))). Qed.
  End Compare.
  Module Key := OrderedType_from_Alt Compare.
  Lemma eqL : forall a b, Key.eq a b -> @eq _ a b.
  Proof. exact (LeibnizComparison.cmp_eq (base.compare (A:=Compare.t))). Qed.
  Include FMapAVL.Make Key.
  Include FMapExtra.MIXIN Key.
  Include FMapExtra.MIXIN_LEIBNIZ Key.
End TPMap.
