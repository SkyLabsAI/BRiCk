(*
 * Copyright (C) 2024 BlueRock Security, Inc.
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)

Require Import skylabs.elpi.extra.extra.

Class ExtraClass := {}.

Elpi Command TestCommandUtils.
Elpi Accumulate File extra.Command.
Elpi Accumulate lp:{{
  main [] :- std.do! [
    coq.env.mk-variant "ExtraColor" ["ExtraRed", "ExtraBlue"] _,
    coq.env.add-lemma-by-ltac "extra_added_true" @opaque! {{ True }} "constructor" [] _,
    coq.TC.add-instance-skeleton "extra_class_instance" coq.locality.g 0
      {{ Build_ExtraClass }} [] _,
  ].
  main _ :- coq.error "usage: TestCommandUtils".
}}.
Elpi Export TestCommandUtils.

TestCommandUtils.

Check ExtraColor.
Check ExtraRed.
Check ExtraBlue.
Check extra_added_true.
Definition has_extra_class : ExtraClass := _.
