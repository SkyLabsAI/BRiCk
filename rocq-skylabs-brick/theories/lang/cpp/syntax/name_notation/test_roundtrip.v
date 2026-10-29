(*
 * Copyright (c) 2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import skylabs.lang.cpp.syntax.prelude.
Require Import skylabs.lang.cpp.syntax.core.
Require Import skylabs.lang.cpp.syntax.name_notation.parser.
Require Import skylabs.lang.cpp.syntax.name_notation.printer.
Require Import skylabs.lang.cpp.syntax.name_notation.test_cases.

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

  Example TEST_rejected : (parse_name <$> rejected) = repeat None (length rejected).
  Proof. vm_compute. reflexivity. Qed.

  (* The type notation is implemented by this parser, so use constructors here
     to check array dimensions and binding independently of that notation. *)
  Example TEST_array_type : parse_type "int[3][4]"%pstring = Some (Tarray (Tarray Tint 4) 3).
  Proof. vm_compute. reflexivity. Qed.

  Example TEST_array_type_print : print_type (Tarray (Tarray Tint 4) 3) = Some "int[3][4]"%pstring.
  Proof. vm_compute. reflexivity. Qed.

  Example TEST_uint_array_type :
    parse_type "unsigned int[5][10]"%pstring = Some (Tarray (Tarray Tuint 10) 5).
  Proof. vm_compute. reflexivity. Qed.

  Example TEST_uint_array_type_print :
    print_type (Tarray (Tarray Tuint 10) 5) = Some "unsigned int[5][10]"%pstring.
  Proof. vm_compute. reflexivity. Qed.

  Example TEST_uint_array_type_print_transposed :
    print_type (Tarray (Tarray Tuint 5) 10) = Some "unsigned int[10][5]"%pstring.
  Proof. vm_compute. reflexivity. Qed.

  (* The outer array contains two zero-length arrays, not the converse. *)
  Example TEST_zero_stride_array_type :
    parse_type "unsigned char[2][0]"%pstring = Some (Tarray (Tarray Tuchar 0) 2).
  Proof. vm_compute. reflexivity. Qed.

  Example TEST_zero_stride_array_type_print :
    print_type (Tarray (Tarray Tuchar 0) 2) = Some "unsigned char[2][0]"%pstring.
  Proof. vm_compute. reflexivity. Qed.

  Example TEST_array_types_parse :
    (parse_type <$> (fst <$> array_types)) = (Some <$> (snd <$> array_types)).
  Proof. vm_compute. reflexivity. Qed.

  Example TEST_array_types_print :
    (print_type <$> (snd <$> array_types)) = (Some <$> (fst <$> array_types)).
  Proof. vm_compute. reflexivity. Qed.

  Example TEST_array_types_rejected :
    (parse_type <$> rejected_array_types) = repeat None (length rejected_array_types).
  Proof. vm_compute. reflexivity. Qed.

  (* Do not emit invalid inner omitted bounds, even through qualifiers. *)
  Example TEST_inner_incomplete_array_print_rejected :
    print_type (Tincomplete_array (Tincomplete_array (Tarray Tint 4))) = None /\
    print_type (Tarray (Tconst (Tincomplete_array Tint)) 2) = None.
  Proof. vm_compute. split; reflexivity. Qed.
End TEST.
