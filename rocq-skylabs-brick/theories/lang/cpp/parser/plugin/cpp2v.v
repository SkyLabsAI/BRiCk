(*
 * Copyright (c) 2025 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Stdlib.Array.PArray.
Require Import Stdlib.Numbers.Cyclic.Int63.PrimInt63.
Require Import bluerock.lang.cpp.parser.

#[local] Set Printing Universes.

Register translation_unit.t as bluerock.lang.cpp.parser.translation_unit.t.
Register translation_unit._skip as bluerock.lang.cpp.parser.translation_unit.skip.
Register translation_unit.abi_type as bluerock.lang.cpp.parser.translation_unit.abi_type.
Register translation_unit.decls as bluerock.lang.cpp.parser.translation_unit.decls.

(* NOTE: This is a hack to get a universe instance *)
Definition empty_array := PArray.make 0%uint63 parser.translation_unit._skip.
Register empty_array as bluerock.lang.cpp.parser.translation_unit.empty_array.

Definition result_type : Type := translation_unit * parser.translation_unit.dup_info.
Register result_type as bluerock.lang.cpp.parser.translation_unit.result_type.

Declare ML Module "rocq-bluerock-brick.plugin".
