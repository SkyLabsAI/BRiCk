(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

From Stdlib Require Import PrimInt63.
Require Import Stdlib.Array.PArray.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.syntax.pretty.
Require Import skylabs.lang.cpp.syntax.typed.

#[local] Open Scope array_scope.

#[local] Definition check_file : location -> PrimInt63.int := file.
#[local] Definition check_byte : location -> PrimInt63.int := byte.
#[local] Definition check_line : location -> PrimInt63.int := line.
#[local] Definition check_column : location -> PrimInt63.int := column.
#[local] Definition check_file_loc : locations -> file_location := file_loc.
#[local] Definition check_spelling_loc : locations -> location := spelling_loc.
#[local] Definition check_location_array : array location :=
  [| dummy_location | dummy_location |].

Example dummy_location_fields :
    file dummy_location = 9223372036854775807%uint63 /\
    byte dummy_location = 9223372036854775807%uint63 /\
    line dummy_location = 9223372036854775807%uint63 /\
    column dummy_location = 9223372036854775807%uint63.
Proof. repeat split. Qed.

Example dummy_locations_fields :
    file_loc dummy_locations = dummy_location /\
    spelling_loc dummy_locations = dummy_location.
Proof. split; reflexivity. Qed.

#[local] Definition bare_global : name := Nglobal (Nid "global").
#[local] Definition located_global : name := NLocInfo 0%uint63 bare_global.

#[local] Definition located_class : name :=
  NLocInfo 2%uint63 (Nglobal (ANLocInfo 2%uint63 (Nid "Point"))).
#[local] Definition located_constructor : name :=
  NLocInfo 3%uint63
    (Nscoped located_class (ANLocInfo 3%uint63 (Nctor nil))).
#[local] Definition located_destructor : name :=
  NLocInfo 4%uint63
    (Nscoped located_class (ANLocInfo 4%uint63 Ndtor)).

Example print_located_constructor :
    printN located_constructor = "Point::Point()"%pstring.
Proof. reflexivity. Qed.

Example print_located_destructor :
    printN located_destructor = "Point::~Point"%pstring.
Proof. reflexivity. Qed.

#[local] Definition located_tu : translation_unit :=
  makeTranslationUnit
    (NM.add located_global
      (Ovar Tint
        (global_init.Init (ELocInfo 1%uint63 (Eglobal bare_global Tint))))
      (NM.empty ObjValue))
    (NM.empty GlobDecl)
    (empty_tu abi.abi_default).(namespace_aliases)
    nil nil abi.abi_default
    (empty_tu abi.abi_default).(msymbols)
    (empty_tu abi.abi_default).(mtypes)
    (empty_tu abi.abi_default).(maliases)
    (empty_tu abi.abi_default).(minstances).

Example erase_translation_unit_locations :
    NM.find bare_global
      (LocInfoTU.erase_translation_unit located_tu).(symbols) =
      Some (Ovar Tint (global_init.Init (Eglobal bare_global Tint))).
Proof. vm_compute. reflexivity. Qed.

Example typed_check_erases_locations :
    trace.runO (typed.decltype.check_tu located_tu) = Some tt.
Proof. vm_compute. reflexivity. Qed.
