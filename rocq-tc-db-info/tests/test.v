(*
 * Copyright (C) BlueRock Security Inc. 2024
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import tc_db_info.tc_db_info.

Create HintDb test discriminated.
Class C (A:Type) (a:A) := MKC {}.
Definition Cu : C unit tt := MKC _ _.
Definition unit' := unit.
Definition tt' : unit' := tt.
Instance Cu' : C unit' tt' := MKC _ _.
Hint Resolve Cu Cu' : test.
Print Hint C.

HintDb Opacity Info test For C.

Module Qualified.
  #[local] Set HintDb Opacity Info Fully Qualified.
  HintDb Opacity Info test For C.
End Qualified.

Hint Mode C ! - : test.
HintDb Opacity Info test For C.

Set HintDb Opacity Info Ignore Outputs.
HintDb Opacity Info test For C.


Create HintDb opac discriminated.
Hint Opaque unit' : opac.

HintDb Opacity Info test For C With Opacity Of opac.
