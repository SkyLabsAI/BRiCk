(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.lang.cpp.syntax.core.
Require Import skylabs.lang.cpp.syntax.types.
Require Import skylabs.lang.cpp.syntax.translation_unit.
Require Import skylabs.lang.cpp.semantics.sub_module.

(** Shared declaration-table selection used by both semantic parsing and
    source-location companion construction. *)
Module Selection.
  Definition merge_obj_value (incoming existing : ObjValue) : option ObjValue :=
    if sub_module.ObjValue_le incoming existing then
      Some existing
    else if sub_module.ObjValue_le existing incoming then Some incoming
         else None.

  Definition merge_glob_decl (incoming existing : GlobDecl) : option GlobDecl :=
    if sub_module.GlobDecl_le incoming existing then
      Some existing
    else if sub_module.GlobDecl_le existing incoming then Some incoming
         else None.

  Definition is_self_type_alias (n : name) (v : GlobDecl) : bool :=
    bool_decide (Gtypedef (Tnamed n) = v \/ Gtypedef (Tenum n) = v).
End Selection.
