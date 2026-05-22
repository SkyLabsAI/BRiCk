(*
 * Copyright (c) 2021 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Export iris.si_logic.bi.
Require Import skylabs.prelude.base.

Module siProp.
  Export iris.si_logic.bi.siProp.

  (** Missing upstream. Unseal [siProp]'s BI layer, then its primitives. *)
  Ltac unseal :=
    unfold bi_emp, bi_sep, bi_wand, bi_persistently; cbn;
    unfold siProp_emp, siProp_sep, siProp_wand,
      siProp_persistently, siProp_plainly; cbn;
    unfold bi_pure, bi_and, bi_or, bi_impl, bi_forall, bi_exist; cbn;
    try siProp_primitive.unseal.

End siProp.
