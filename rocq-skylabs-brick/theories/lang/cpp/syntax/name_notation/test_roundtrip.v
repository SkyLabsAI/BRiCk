(*
 * Copyright (c) 2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bluerock.lang.cpp.syntax.prelude.
Require Import bluerock.lang.cpp.syntax.core.
Require Import bluerock.lang.cpp.syntax.name_notation.parser.
Require Import bluerock.lang.cpp.syntax.name_notation.printer.
Require Import bluerock.lang.cpp.syntax.name_notation.test_cases.

Module Type TEST.
  Record RESULT (IN OUT : Set) : Set :=
  { input : IN ; expected : OUT ; observed : OUT }.

  Definition print_parse (nm : name) (str : PrimString.string) : list (RESULT _ _) :=
    let result : option _ := print_name nm in
    if bool_decide (result = Some str) then nil
    else {| input := nm ; expected := Some str ; observed := result |} :: nil.

  Definition parse_print (nm : name) (str : PrimString.string) : list (RESULT _ _) :=
    let result : option name := parse_name str in
    if bool_decide (result = Some nm) then nil
    else {| input := str ; expected := Some nm ; observed := result |} :: nil.

  Example TEST_print_parse : List.concat ((fun '(b,a) => print_parse a b) <$> canonical) = [].
  Proof. vm_compute. reflexivity. Qed.

  Example TEST_parse_print : List.concat ((fun '(b,a) => parse_print a b) <$> (canonical ++ parse_only)) = [].
  Proof. vm_compute. reflexivity. Qed.
End TEST.
