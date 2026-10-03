(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(** [sub_module_mismatch.compute a b] says why [sub_module a b] fails. *)

Require Import skylabs.lang.cpp.parser.
Require Import skylabs.lang.cpp.parser.plugin.cpp2v.
Require Import skylabs.lang.cpp.semantics.sub_module.

#[duplicates(error)]
cpp.prog left prog cpp:{{
  struct P { int x; };
  int f() { return 1; }
  int only_left() { return 0; }
  static_assert(sizeof(int) >= 2, "only on the left");
}}.

#[duplicates(error)]
cpp.prog right prog cpp:{{
  struct P { long x; };               // incompatible type
  int f() { return 2; }               // incompatible symbol
}}.

(** One mismatch of each kind; the ABIs agree. *)
Eval vm_compute in sub_module_mismatch.compute left right.

Example left_not_sub_module_right : ~ sub_module left right.
Proof. apply sub_module_mismatch.not_sub_module. vm_compute. discriminate. Qed.

(** A translation unit has no mismatch with itself, and that is enough for
    [sub_module]. *)
Example left_mismatch_left : sub_module_mismatch.compute left left = sub_module_mismatch.empty.
Proof. vm_compute. reflexivity. Qed.

Example left_sub_module_left : sub_module left left.
Proof. apply sub_module_mismatch.sound. vm_compute. reflexivity. Qed.

(** * An ABI mismatch

    The same declaration, compiled for two architectures.  Their ABIs differ,
    and so do target-specific builtin types such as [__builtin_va_list]. *)

#[duplicates(error)]
cpp.prog x86 flags "-target x86_64-linux-gnu" prog cpp:{{
  int g();
}}.

#[duplicates(error)]
cpp.prog arm flags "-target aarch64-linux-gnu" prog cpp:{{
  int g();
}}.

Eval vm_compute in sub_module_mismatch.compute x86 arm.

Example x86_not_sub_module_arm : ~ sub_module x86 arm.
Proof. apply sub_module_mismatch.not_sub_module. vm_compute. discriminate. Qed.

(** * An assertion mismatch on its own

    [with_assert] has one more [static_assert] than [without_assert].  The
    relation is directional: only the side with the extra assert mismatches. *)

#[duplicates(error)]
cpp.prog without_assert prog cpp:{{
  int g();
}}.

#[duplicates(error)]
cpp.prog with_assert prog cpp:{{
  int g();
  static_assert(sizeof(char) == 1, "extra");
}}.

Eval vm_compute in sub_module_mismatch.compute with_assert without_assert.

Example with_assert_not_sub_module_without_assert : ~ sub_module with_assert without_assert.
Proof. apply sub_module_mismatch.not_sub_module. vm_compute. discriminate. Qed.

Example without_assert_sub_module_with_assert : sub_module without_assert with_assert.
Proof. apply sub_module_mismatch.sound. vm_compute. reflexivity. Qed.
