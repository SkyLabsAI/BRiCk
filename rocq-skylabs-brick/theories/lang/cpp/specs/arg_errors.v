(*
 * Copyright (c) 2022 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import iris.bi.bi.
Require Import skylabs.iris.extra.proofmode.proofmode.

Module Type BAD_ARGUMENTS.
  Parameter insufficient_arguments : forall {SI : sidx} {PROP : bi}, PROP.
  Axiom insufficient_arguments_eq :
    forall SI PROP, @insufficient_arguments SI PROP = False%I.

  Parameter too_many_arguments : forall {SI : sidx} {PROP : bi}, PROP.
  Axiom too_many_arguments_eq :
    forall SI PROP, @too_many_arguments SI PROP = False%I.
End BAD_ARGUMENTS.

Module bad_arguments : BAD_ARGUMENTS.
  Definition insufficient_arguments {SI : sidx} {PROP : bi} : PROP := False.
  Definition insufficient_arguments_eq {SI : sidx} {PROP : bi} :
      @insufficient_arguments SI PROP = False%I := eq_refl.

  Definition too_many_arguments {SI : sidx} {PROP : bi} : PROP := False.
  Definition too_many_arguments_eq {SI : sidx} {PROP : bi} :
      @too_many_arguments SI PROP = False%I := eq_refl.

End bad_arguments.
