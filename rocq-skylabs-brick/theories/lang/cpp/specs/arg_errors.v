(*
 * Copyright (c) 2022 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import iris.bi.bi.
Require Import iris.proofmode.tactics.

Module Type BAD_ARGUMENTS.
  Parameter insufficient_arguments : forall {PROP : bi}, PROP.
  Axiom insufficient_arguments_eq : forall PROP, @insufficient_arguments PROP = False%I.

  Parameter too_many_arguments : forall {PROP : bi}, PROP.
  Axiom too_many_arguments_eq : forall PROP, @too_many_arguments PROP = False%I.
End BAD_ARGUMENTS.

Module bad_arguments : BAD_ARGUMENTS.
  Definition insufficient_arguments {PROP : bi} : PROP := False.
  Definition insufficient_arguments_eq {PROP : bi} : @insufficient_arguments PROP = False%I := eq_refl.

  Definition too_many_arguments {PROP : bi} : PROP := False.
  Definition too_many_arguments_eq {PROP : bi} : @too_many_arguments PROP = False%I := eq_refl.

End bad_arguments.
