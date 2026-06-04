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
  ; lang_version : lang_version.t
    (* ^ the C++ language version used to compile the translation unit *)
  }.
  #[only(lens,eq_dec)] derive t.

  Definition uintptr_t_type (info : t) : type :=
    Tnum info.(uintptr_t_rank) Unsigned.
  Definition pointer_size_bitsize (info : t) : bitsize :=
    int_rank.bitsize info.(uintptr_t_rank).

  Definition signedness_of_char (info : t) (ct : char_type) : signed :=
    match ct with
    | char_type.Cchar => info.(char_signed)
    | char_type.Cwchar => info.(wchar_signed)
    | _ => Unsigned
    end.

  (** [equivalent_int_type info ct] is the integral type that is equivalent
      (in rank and signedness) to [ct].
   *)
  #[local] Definition find_equiv (ct : char_type)
    (res := find (fun a => bool_decide (char_type.bitsN ct <= int_rank.bitsN a)%N) int_rank.ranks)
    : match res with
      | None => unit
      | Some _ => int_rank.t
      end :=
    match res as X return match X with
                          | None => unit
                          | Some _ => int_rank.t
                          end with
    | None => tt
    | Some x => x
    end.

  Definition equivalent_int_type (info : t) (ct : char_type) : integral_type.t :=
    let bits :=
      (* NOTE the setup here computes the appropriate type given the size
         constraints defined in [char_type.bitsN] and [int_type.bitsN] *)
      match ct with
      | char_type.Cchar => int_rank.Ichar
      | char_type.C8 => Evaluate (find_equiv char_type.C8)
      | char_type.C16 => Evaluate (find_equiv char_type.C16)
      | char_type.C32 => Evaluate (find_equiv char_type.C32)
      | char_type.Cwchar => Evaluate (find_equiv char_type.Cwchar)
      end
    in
    integral_type.mk bits (signedness_of_char info ct).

  (** Common Linux ABIs. Just for testing. *)

  Definition x64_linux : t :=
    mkT int_rank.Ilong Signed Signed Little lang_version.Cpp17.
  Definition armle64_linux : t :=
    mkT int_rank.Ilong Unsigned Unsigned Little lang_version.Cpp17.

  Definition abi_default : t := x64_linux.
NES.End abi.
