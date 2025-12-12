(*
 * Copyright (C) 2023 BlueRock Security, Inc.

 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import elpi.apps.locker.locker.
Require Import bluerock.iris.extra.proofmode.proofmode.

Require Import bluerock.iris.extra.bi.prelude.
Require Import bluerock.iris.extra.bi.observe.
Require Import bluerock.lang.cpp.semantics.values.
Require Import bluerock.lang.cpp.logic.arr.
Require Import bluerock.lang.cpp.logic.heap_pred.

Import ChargeNotation.
#[local] Open Scope Z_scope.

(** Core C++ string theory: part of the semantics. *)

(** [strings_bytesR ct q chars] is [q] (const) fractional ownership of
    [chars] with a trailing [0].
    - Unlike [zstring.t], does not assume the contents avoid `0` elements, since that property might not be guaranteed in all character types/encodings.
    - Used for string literals of arbitrary character types.

    NOTE that [chars] is in units of *characters* using the standard
          character encoding (see [syntax/expr.v]). This is *not* the
          same as bytes, and will not be for multi-byte characters.
  *)

mlock
Definition string_bytesR `{Σ : cpp_logic} {σ : genv} (cty : char_type) (q : cQp.t) (s : literal_string.t) : Rep :=
  let ty := Tchar_ cty in
  arrayR ty (λ c, primR ty q (N_to_char cty c)) (literal_string.to_list_N s ++ [0%N]).

(* Arguments char_type.bitsN !_ /.
Arguments char_type.bytesN !_ /. *)
Lemma N_to_char_Cchar_eq (c : N) :
  (c < 2 ^ 8)%N ->
  N_to_char char_type.Cchar c = Vchar c.
Proof.
  intros.
  rewrite /N_to_char /operator.trimN/=. f_equiv.
  exact: N.mod_small.
Qed.

Section with_Σ.
  Context `{Σ : cpp_logic} {σ : genv}.

  #[global] Instance string_bytesR_timeless : Timeless3 string_bytesR.
  Proof. rewrite string_bytesR.unlock /=. apply _. Qed.

  #[global] Instance string_bytesR_cfrac cty : CFractional1 (string_bytesR cty).
  Proof. rewrite string_bytesR.unlock /=. apply _. Qed.
End with_Σ.
