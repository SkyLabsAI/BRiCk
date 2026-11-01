(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(** [sub_module] compares return types exactly.

    Within one translation unit, clang rejects a declaration and a definition
    whose return types differ only in cv-qualifiers ("functions that differ
    only in their return type cannot be overloaded"); across translation
    units such a pair violates [basic.link].  cpp2v resolves typedefs, so
    well-formed programs produce identical return types on both sides. *)

Require Import skylabs.lang.cpp.parser.
Require Import skylabs.lang.cpp.parser.plugin.cpp2v.
Require Import skylabs.lang.cpp.semantics.sub_module.

#[duplicates(error)]
cpp.prog decl prog cpp:{{
  typedef const int CI;
  CI f();
  struct S { const int m(); };
}}.

#[duplicates(error)]
cpp.prog def prog cpp:{{
  typedef const int CI;
  const int f() { return 0; }
  struct S { const int m() { return 0; } };
}}.

#[duplicates(error)]
cpp.prog bad prog cpp:{{
  typedef const int CI;
  int f() { return 0; }
  struct S { int m() { return 0; } };
}}.

Example decl_sub_module_def : sub_module decl def.
Proof. apply sub_module_mismatch.sound. vm_compute. reflexivity. Qed.

(** [const int] against [int] is incompatible, for functions and methods. *)
Eval vm_compute in sub_module_mismatch.compute decl bad.

Example decl_not_sub_module_bad : ~ sub_module decl bad.
Proof. apply sub_module_mismatch.not_sub_module. vm_compute. discriminate. Qed.

(** cpp2v never emits a return type that [normalize_type] changes, such as
    stacked qualifiers.  Two such spellings of one type are distinct. *)
Definition ret_fn (ret : type) : ObjValue :=
  Ofunction (Build_Func ret nil CC_C Ar_Definite exception_spec.MayThrow None).

Example stacked_qualifiers_distinct :
  ObjValue_le (ret_fn (Tqualified QC (Tqualified QV Tint))) (ret_fn (Tqualified QCV Tint)) = false.
Proof. vm_compute. reflexivity. Qed.
