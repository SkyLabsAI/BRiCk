(*
 * Copyright (c) 2020-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bluerock.lang.cpp.syntax.
Require Import bluerock.lang.cpp.logic.

Notation boolR q v := (primR Tbool q (Vbool v)).

(* integers with implicit sizes *)
(* note(gmm): these might need to become definitions if we want to be generic
 * across sizes
 *)
Notation scharR q v := (primR Tschar q (Vint v)).
Notation ucharR q v := (primR Tuchar q (Vint v)).
Notation byteR q v := (primR Tbyte q (Vint v)) (only parsing). (* TODO: use [N]? *)

Notation sshortR q v := (primR Tshort q (Vint v)) (only parsing).
Notation ushortR q v := (primR Tushort q (Vint v)).
Notation shortR q v := (sshortR q v).


Notation sintR q v := (primR Tint q (Vint v)) (only parsing).
Notation uintR q v := (primR Tuint q (Vint v)).
Notation intR q v := (sintR q v).

Notation slongR q v := (primR Tlong q (Vint v)) (only parsing).
Notation ulongR q v := (primR Tulong q (Vint v)).
Notation longR q v := (slongR q v).
Notation size_tR q v := (primR Tsize_t q (Vint v)) (only parsing). (* TODO: use [N]? *)

Notation slonglongR q v := (primR Tlonglong q (Vint v)) (only parsing).
Notation ulonglongR q v := (primR Tulonglong q (Vint v)).
Notation longlongR q v := (slonglongR q v).

(* integers with explict sizes *)

#[deprecated(since="20240624",note="use [ucharR].")]
Notation u8R  q v := (primR Tuchar  q (Vint v)) (only parsing).
#[deprecated(since="20240624",note="use [ushortR].")]
Notation u16R q v := (primR Tushort q (Vint v)) (only parsing).
#[deprecated(since="20240624",note="use [uintR].")]
Notation u32R q v := (primR Tuint q (Vint v)) (only parsing).
#[deprecated(since="20240624",note="use [ulongR] or [ulonglongR].")]
Notation u64R q v := (primR Tulonglong q (Vint v)) (only parsing).

#[deprecated(since="20240624",note="use [scharR].")]
Notation i8R  q v := (primR Tschar  q (Vint v)) (only parsing).
#[deprecated(since="20240624",note="use [shortR].")]
Notation i16R q v := (primR Tshort q (Vint v)) (only parsing).
#[deprecated(since="20240624",note="use [intR].")]
Notation i32R q v := (primR Tint q (Vint v)) (only parsing).
#[deprecated(since="20240624",note="use [longR] or [longlongR].")]
Notation i64R q v := (primR Tlonglong q (Vint v)) (only parsing).

(** Character notations *)
Notation charR q v := (primR Tchar q (Vchar v)).
Notation wcharR q v := (primR Twchar q (Vchar v)).
Notation char32R q v := (primR Tchar32 q (Vchar v)).
Notation char16R q v := (primR Tchar16 q (Vchar v)).
Notation char8R q v := (primR Tchar8 q (Vchar v)).

Notation "'ptrR<' ty '>' q p" := (primR (Tptr ty) q (Vptr p)) (at level 10, ty at level 20, q at level 1, p at level 1, format "'ptrR<' ty '>'  q  p").

Notation "'refR<' ty '>' q p" := (primR (Tref ty) q (Vptr p)) (at level 10, ty at level 20, q at level 1, p at level 1, format "'refR<' ty '>'  q  p").
