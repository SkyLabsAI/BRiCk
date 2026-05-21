(*
 * Copyright (c) 2020-2026 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Export elpi.apps.NES.NES.
Require Import stdpp.fin_maps.
Require Import skylabs.prelude.base.
Require Import skylabs.prelude.avl.
Require Import skylabs.prelude.lens.
Require Import skylabs.prelude.elpi.derive.
Require Import skylabs.prelude.elpi.derive.lens.
Require Import skylabs.prelude.pstring.
Require Import skylabs.lang.cpp.syntax.core.
Require Import skylabs.lang.cpp.syntax.types.
Require Import skylabs.lang.cpp.syntax.decl.
Require Import skylabs.lang.cpp.syntax.namemap.

(** This record contains implementation-defined information about a translation unit that is chosen by our clang.
https://eel.is/c++draft/defns.impl.defined#def:behavior,implementation-defined

TODO: maybe just ABI because we're in the context of C++.
*)
NES.Begin abi.
  Record t : Set := mkT
  { uintptr_t_rank : int_rank.t
    (* ^ the size of a pointer *)
  ; char_signed : signed
    (* ^ whether or not `char` is signed or unsigned *)
  ; wchar_signed : signed
  ; byte_order : endian
  }.
  #[only(lens,eq_dec)] derive t.

  Definition uintptr_t_type (info : t) : type :=
    Tnum info.(uintptr_t_rank) Unsigned.
  Definition pointer_size_bitsize (info : t) : bitsize :=
    int_rank.bitsize info.(uintptr_t_rank).

  (** Common Linux ABIs. Just for testing. *)

  Definition x64_linux : t :=
    mkT int_rank.Ilong Signed Signed Little.
  Definition armle64_linux : t :=
    mkT int_rank.Ilong Unsigned Unsigned Little.

  Definition abi_default : t := x64_linux.
NES.End abi.
