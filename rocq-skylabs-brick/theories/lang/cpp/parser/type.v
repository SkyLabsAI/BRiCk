(*
 * Copyright (c) 2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import skylabs.lang.cpp.parser.prelude.
Require Import skylabs.lang.cpp.parser.lang.

(** * Derived types emitted by cpp2v *)

Module ParserType.
  (*
  Indicate that [underlying] is used to represent alias type [name].
  Enums are treated similarly.
  *)
  Definition Talias (name : globname) {underlying : type} : type :=
    underlying.
  Definition Tunderlying (enum : type) {underlying : type} : type :=
    underlying.
  Definition Tunary_xform (name : bs) (arg : type) {result : type} : type :=
    result.

  Notation Tfunction ty cc var ret args :=
    (normalize_type (Tfunction (@FunctionType ty cc var ret args))) (only parsing).

  Notation Tdecay_type original adjusted := (adjusted) (only parsing).

  (** Attributes on a type (or on the typedef naming it). cpp2v prints every
      attribute; those on [attr.noop_kinds] are dropped here, so the AST only
      records attributes that may matter. *)
  Definition Tattributed (attrs : list attr.t) (t : type) : type :=
    if forallb attr.noop attrs then t else skylabs.lang.cpp.syntax.core.Tattributed attrs t.

End ParserType.
