(*
 * Copyright (C) 2026 SkyLabs AI, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.ltac2.extra.extra.
Require Import skylabs_auto.cram.builder.prelude.

Section example.
  Import Ltac2 Builder Printf.

  Open Scope list_scope.
  Import Lists.List.ListNotations.

  Goal True.
    printf "(** Test 1 - no errors *)".
    Ltac2 Eval
    let builder :=
      let builder_a := unsafe_constr '(nat) in
      let builder_b := build_list build_nat in
      custom_list_builder builder_a builder_b in

    let trm     := run builder ( '(1), '(5), [2;3;4]) in
    Control.assert_true (Constr.equal trm '([1;5;4;3;2])).

    printf "".
    printf "(** Test 2 - error in function application *)".
    Ltac2 Eval
      let builder :=
        let builder_a := unsafe_constr '(nat) in
        let builder_b := build_list build_nat in
        faulty_list_builder builder_a builder_b in

      let trm     := run builder ( '(1), '(5), [2;3;4]) in
      Control.assert_true (Constr.equal trm '([1;5;4;3;2])).
  Abort.

End example.
