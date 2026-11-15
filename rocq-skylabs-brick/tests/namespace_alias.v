(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(** A namespace alias [namespace g = detail;] lets names written through the
    alias ([g::zero()]) resolve to the entities of the namespace it names. *)

Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.parser.plugin.cpp2v.

cpp.prog source prog cpp:{{
  namespace detail { int zero() { return 0; } struct S { int x; }; }
  namespace a { namespace b { int one() { return 1; } } }

  namespace g = detail;
  namespace ab = a::b;
  namespace gg = g;        // an alias of an alias
  int f() { namespace d = detail; return d::zero(); }
}}.

Eval vm_compute in NM.elements source.(namespace_aliases).2.

Example value_through_alias :
  resolve_value source "g::zero()" = Some "detail::zero()"%cpp_name.
Proof. vm_compute. reflexivity. Qed.

Example type_through_alias :
  resolve_type source "g::S" = Some "detail::S"%cpp_type.
Proof. vm_compute. reflexivity. Qed.

Example nested_namespace_alias :
  resolve_value source "ab::one()" = Some "a::b::one()"%cpp_name.
Proof. vm_compute. reflexivity. Qed.

Example alias_of_alias :
  resolve_value source "gg::zero()" = Some "detail::zero()"%cpp_name.
Proof. vm_compute. reflexivity. Qed.

(** Canonical names still resolve to themselves. *)
Example canonical_name :
  resolve_value source "detail::zero()" = Some "detail::zero()"%cpp_name.
Proof. vm_compute. reflexivity. Qed.
