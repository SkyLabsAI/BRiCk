(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(** A header may declare an array variable without its major bound
    ([basic.link]: array types of declarations of the same object may differ
    by the presence or absence of a major array bound). *)

Require Import skylabs.lang.cpp.parser.
Require Import skylabs.lang.cpp.parser.plugin.cpp2v.
Require Import skylabs.lang.cpp.semantics.sub_module.

#[duplicates(error)]
cpp.prog header prog cpp:{{
  extern int a[];
  extern const int ca[];
  extern int m[][2];
  extern int b[3];
}}.

#[duplicates(error)]
cpp.prog source prog cpp:{{
  extern int a[];
  extern const int ca[];
  extern int m[][2];
  extern int b[3];
  int a[3] = {1, 2, 3};
  const int ca[] = {1, 2};
  int m[1][2] = {{1, 2}};
  int b[3];
}}.

Example header_sub_module_source : sub_module header source.
Proof. apply sub_module_mismatch.sound. vm_compute. reflexivity. Qed.

(** The relation is directional: a bound in the declaration is not dropped. *)
#[duplicates(error)]
cpp.prog bounded prog cpp:{{
  extern int a[3];
}}.

#[duplicates(error)]
cpp.prog unbounded prog cpp:{{
  extern int a[];
}}.

Eval vm_compute in sub_module_mismatch.compute bounded unbounded.

Example bounded_not_sub_module_unbounded : ~ sub_module bounded unbounded.
Proof. apply sub_module_mismatch.not_sub_module. vm_compute. discriminate. Qed.

(** Zero-sized arrays (a GNU extension) are excluded: their address need not
    be strictly valid, so [denoteSymbol] gives them less than an incomplete
    array declaration. *)
#[duplicates(error)]
cpp.prog z_decl prog cpp:{{
  extern int z[];
}}.

#[duplicates(error)]
cpp.prog zero_sized prog cpp:{{
  extern int z[];
  int z[0];
}}.

Eval vm_compute in sub_module_mismatch.compute z_decl zero_sized.

Example z_decl_not_sub_module_zero_sized : ~ sub_module z_decl zero_sized.
Proof. apply sub_module_mismatch.not_sub_module. vm_compute. discriminate. Qed.
