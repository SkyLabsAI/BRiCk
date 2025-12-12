(*
 * Copyright (c) 2024-2025 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import Stdlib.Structures.OrderedTypeAlt.
Require Import Stdlib.FSets.FMapAVL.
Require Import bluerock.prelude.avl.
Require Import bluerock.prelude.compare.
Require Import bluerock.lang.cpp.syntax.prelude.
Require Import bluerock.lang.cpp.syntax.core.
Require Import bluerock.lang.cpp.syntax.compare.

(** ** Name maps *)

#[global] Declare Instance name_comparison :
  Comparison (compareN).	(** TODO *)

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
