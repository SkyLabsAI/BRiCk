(*
 * Copyright (C) 2022-2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import skylabs.ltac2.extra.internal.init.
Require Import skylabs.ltac2.extra.internal.constr.
Require Import skylabs.ltac2.extra.internal.char.
Require Import Stdlib.Strings.String.

(** Minor extensions to [Ltac2.String] *)
Module String.
  Import Ltac2 Init Ltac2.Bool.
  Export Ltac2.String.

  (** [sub s pos len] returns a new byte sequence of length len,
      containing the subsequence of s that starts at position pos and has length len.
      (Description taken from OCaml documentation of Bytes.sub)
   *)
  Ltac2 @ external sub : string -> int -> int -> string :=
    "ltac2_extensions" "string_sub".

  (** [of_char_list cs] builds a string from the list [cs]. *)
  Ltac2 of_char_list (cs : char list) : string :=
    let len := List.length cs in
    let res := String.make len (Char.of_int 0) in
    List.iteri (String.set res) cs; res.

  (** [of_string_constr t] attempts to build a string from the given Coq term
      [c], which must be a fully concrete and evaluated term of type [string]
      from the [Coq.Strings.String] module. *)
  Ltac2 of_string_constr (t : constr) : string option :=
    let rec build_string acc t :=
      lazy_match! t with
      | String ?c ?t  => Option.bind (Char.of_ascii_constr c)
                           (fun c => build_string (c :: acc) t)
      | EmptyString   => Some (of_char_list (List.rev acc))
      | _             => None
      end
    in
    build_string [] t.

  Ltac2 in_quotes (s : string) : string :=
    let q := String.make 1 (Char.of_int 34) in
    app q (app s q).

  Ltac2 newline () : string :=
    String.make 1 (Char.of_int 10).

  Ltac2 is_prefix_of (pre : string) (s : string) : bool :=
    let len_pre := String.length pre in
    let len_s := String.length s in
    Int.le len_pre len_s && String.equal pre (String.sub s 0 len_pre).

  Ltac2 is_suffix_of (suff : string) (s : string) : bool :=
    let len_suff := String.length suff in
    let len_s := String.length s in
    let len_pre := Int.sub len_s len_suff in
    Int.le len_suff len_s && String.equal suff (String.sub s len_pre len_suff).

  Ltac2 remove_prefix (pre : string) (s : string) : string option :=
    let len_pre := String.length pre in
    let len_s := String.length s in
    let len_suff := Int.sub len_s len_pre in
    if Int.le len_pre len_s &&
         String.equal pre (String.sub s 0 len_pre) then
      Some (String.sub s len_pre len_suff)
    else None.

  Ltac2 remove_suffix (suff : string) (s : string) : string option :=
    let len_suff := String.length suff in
    let len_s := String.length s in
    let len_pre := Int.sub len_s len_suff in
    if Int.le len_suff len_s &&
         String.equal suff (String.sub s len_pre len_suff) then
      Some (String.sub s 0 len_pre)
    else
      None.

  (* Synonym meant fit the same naming convention as [List] *)
  Ltac2 append := app.

End String.
