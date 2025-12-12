(*
 * Copyright (c) 2025 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import Stdlib.Strings.String.
Require Import Corelib.Numbers.Cyclic.Int63.PrimInt63.
Require Import Stdlib.Strings.PrimString.
Require Import bluerock.prelude.base.
Require Import bluerock.prelude.uint63.
Require Import bluerock.prelude.pstring.

Definition string_to_pstring (s : String.string) : PrimString.string :=
  let byte_to_char b := Buf.Byte $ Uint63.of_Z $ Z.of_N $ Byte.to_N b in
  Buf.contents $ Buf.Concat Buf.Empty $ byte_to_char <$> String.list_byte_of_string s.

Definition pstring_to_string (s : PrimString.string) : String.string :=
  let fix aux (len : nat) (i : PrimInt63.int) acc :=
    match len with
    | 0 => acc
    | S len =>
        let c := Ascii.ascii_of_N $ Z.to_N $ Uint63.to_Z $ PrimString.get s i in
        aux len (PrimInt63.sub i 1%int63) (String c acc)
    end
  in
  let len := PrimString.length s in
  aux (Z.to_nat $ Uint63.to_Z len) (PrimInt63.sub len 1)%int63 EmptyString.

Module Type TEST.
  Notation TEST_p_to_s x := (pstring_to_string (string_to_pstring x%string) = x%string).
  Succeed Example _1 : TEST_p_to_s "hello" := ltac:(vm_compute; reflexivity).
  Succeed Example _2 : TEST_p_to_s """" := ltac:(vm_compute; reflexivity).

  Notation TEST_s_to_p x := (string_to_pstring (pstring_to_string x%pstring) = x%pstring).
  Succeed Example _1 : TEST_s_to_p "hello" := ltac:(vm_compute; reflexivity).
  Succeed Example _2 : TEST_s_to_p """" := ltac:(vm_compute; reflexivity).

End TEST.
