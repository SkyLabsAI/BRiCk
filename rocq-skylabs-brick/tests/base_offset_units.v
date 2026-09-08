(*
 * Copyright (c) 2026 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(** Regression test: [LayoutInfo.li_offset] is an offset in *bits*, for base
    classes as well as for fields.

    cpp2v reports field offsets with [ASTRecordLayout::getFieldOffset] (bits)
    but base-class offsets with [getBaseClassOffset], which yields
    [CharUnits], i.e. bytes. Emitting the latter unconverted made
    [parent_offset] compute [byteOffset / 8], collapsing every base at a byte
    offset below 8 onto offset 0. *)

Require Import skylabs.lang.cpp.parser.
Require Import skylabs.lang.cpp.parser.plugin.cpp2v.
Require Import skylabs.lang.cpp.semantics.

cpp.prog mi prog cpp:{{
  struct A { int a; };
  struct B { int b; };
  struct C : A, B { int c; };
}}.

#[local] Definition bases (tu : translation_unit) (cls : globname)
    : option (list (classname * LayoutInfo)) :=
  match tu.(types) !! cls with
  | Some (Gstruct s) => Some s.(s_bases)
  | _ => None
  end.

(** [B] follows [A], which occupies bytes [0,4): byte offset 4, bit offset 32. *)
Example mi_base_offsets_are_bits :
  bases mi "C"%cpp_name
  = Some [("A"%cpp_name, {| li_offset := 0 |});
          ("B"%cpp_name, {| li_offset := 32 |})].
Proof. vm_compute. reflexivity. Qed.

Example mi_parent_offset_is_bytes :
  (parent_offset_tu mi "C"%cpp_name "A"%cpp_name,
   parent_offset_tu mi "C"%cpp_name "B"%cpp_name)
  = (Some 0%Z, Some 4%Z).
Proof. vm_compute. reflexivity. Qed.

(** The sharpest case: with the empty base optimization, distinct base
    subobjects sit one byte apart, so a byte-valued offset would truncate to
    zero and make the two bases indistinguishable. *)
cpp.prog ebo prog cpp:{{
  struct E { };
  struct D1 : E { };
  struct D2 : E { };
  struct Diamond : D1, D2 { };
}}.

Example ebo_base_offsets_are_bits :
  bases ebo "Diamond"%cpp_name
  = Some [("D1"%cpp_name, {| li_offset := 0 |});
          ("D2"%cpp_name, {| li_offset := 8 |})].
Proof. vm_compute. reflexivity. Qed.

Example ebo_parent_offset_distinguishes_bases :
  (parent_offset_tu ebo "Diamond"%cpp_name "D1"%cpp_name,
   parent_offset_tu ebo "Diamond"%cpp_name "D2"%cpp_name)
  = (Some 0%Z, Some 1%Z).
Proof. vm_compute. reflexivity. Qed.
