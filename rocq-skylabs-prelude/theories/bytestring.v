(*
 * Copyright (c) 2020-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import stdpp.countable.
Require Import stdpp.strings.
Require Import stdpp.namespaces.
Require Export bluerock.prelude.bytestring_core.

#[local] Set Default Proof Using "Type".

(** Bytestring extensions. Integrate with stdpp and strings. *)
(** bytes *)
#[global] Instance byte_inhabited : Inhabited Byte.byte := populate Byte.x00.
#[global] Instance byte_eq_dec : EqDecision Byte.byte := Byte.byte_eq_dec.

#[global] Instance byte_countable : Countable Byte.byte.
Proof.
  apply (inj_countable Byte.to_N Byte.of_N).
  abstract (by intros []).
Defined.

#[global] Instance bytestring_eq_dec : EqDecision bs := BS.eq_dec.
#[global] Instance bytestring_inhabited : Inhabited bs. Proof. exact (populate ""%bs). Qed.

#[global] Instance byte_to_N_inj : Inj eq eq Byte.to_N.
Proof. intros ?? E; apply (inj Some). by rewrite <-!Byte.of_to_N, E. Qed.
#[global] Instance byte_of_N_surj : Surj eq Byte.of_N.
Proof.
  intros [b|]. by rewrite <-!Byte.of_to_N; eauto.
  exists 256%N. by rewrite Byte.of_N_None_iff.
Qed.

#[global] Instance bytestring_parse_print_cancel : Cancel eq BS.parse BS.print :=
  BS.print_parse_inv.
#[global] Instance bytestring_print_parse_cancel : Cancel eq BS.print BS.parse :=
  BS.parse_print_inv.
#[global] Instance bytestring_print_inj : Inj eq eq BS.print :=
  cancel_inj.
#[global] Instance bytestring_parse_inj : Inj eq eq BS.parse :=
  cancel_inj.
#[global] Instance bytestring_print_surj : Surj eq BS.print :=
  cancel_surj.
#[global] Instance bytestring_parse_surj : Surj eq BS.parse :=
  cancel_surj.


(** bytestrings *)
(** Many functions on byte strings are meant to be always used
qualified, as they conflict with similar functions from [List] or [String].

All such functions are collected in a module [BS], which is not meant
to be imported, as it defines names like [t].
*)
Module Import BS.
  Export bytestring_core.BS.

  Fixpoint to_string (b : bs) : string :=
    match b with
    | BS.EmptyString => String.EmptyString
    | BS.String x xs => String.String (Ascii.ascii_of_byte x) (to_string xs)
    end.

  Fixpoint of_string (b : string) : bs :=
    match b with
    | String.EmptyString => ""
    | String.String x xs => String (Ascii.byte_of_ascii x) (of_string xs)
    end%bs.

  Lemma of_string_to_string_inv :
    forall (b : bs),
      of_string (to_string b) = b.
  Proof.
    intros *; induction b as [| a b' IHb']; simpl.
    - by reflexivity.
    - by rewrite IHb', Ascii.byte_of_ascii_of_byte.
  Qed.

  Lemma to_string_of_string_inv :
    forall (b : string),
      to_string (of_string b) = b.
  Proof.
    intros *; induction b as [| a b' IHb']; simpl.
    - by reflexivity.
    - by rewrite IHb', Ascii.ascii_of_byte_of_ascii.
  Qed.

  Definition bytes_to_string (xs : list N) : bs :=
    BS.parse ((default Byte.x00 ∘ Byte.of_N) <$> xs).

  Definition string_to_bytes (b : bs) : list N :=
    Byte.to_N <$> BS.print b.

  #[global] Instance bytes_to_string_to_bytes : Cancel eq bytes_to_string string_to_bytes.
  Proof.
    intros bs. unfold bytes_to_string, string_to_bytes; induction bs; csimpl. done.
    by rewrite IHbs, Byte.of_to_N.
  Qed.
  (* TODO: [string_to_bytes (bytes_to_string bs) = bs], but it only holds for "valid" [bs]. *)

  #[deprecated(since="20240521", note="Use [BS.concat].")]
  Notation sepBy := BS.concat (only parsing).

  #[local]
  Fixpoint split_at_loop (n : nat) (acc b : bs) : bs * bs :=
    match n with
    | 0 => (BS.rev acc, b)
    | S n => match b with
            | BS.String x y => split_at_loop n (BS.String x acc) y
            | BS.EmptyString => (BS.rev acc, b)
            end
    end.
  Definition split_at (n : nat) (s : bs) : bs * bs := split_at_loop n "" s.

  Definition take (n : nat) (b : bs) : bs := fst $ split_at n b.
  Definition drop (n : nat) (b : bs) : bs := snd $ split_at n b.

  Fixpoint last (b : bs) (o : option Byte.byte) : option Byte.byte :=
    match b with
    | BS.EmptyString => o
    | BS.String s b => last b (Some s)
    end.

  Definition decimal_digit (i : N) : Byte.byte :=
    default Byte.x00 $ Byte.of_N $ N.add i 48.
  Fixpoint pp_N_aux (fuel : nat) (i : N) (acc : bs) : bs :=
    match fuel, i with
    | O, _ | _, N0 =>
      match acc with | BS.EmptyString => "0" | _ => acc end
    | S fuel, _ =>
      let (i, d) := N.div_eucl i 10 in
      pp_N_aux fuel i $ BS.String (decimal_digit d) acc
    end.
  Definition of_N_decimal (n : N) : bs :=
    pp_N_aux (S $ N.to_nat $ N.log2 n) n BS.EmptyString.
End BS.

#[global] Instance bytestring_countable : Countable bs.
Proof. apply (inj_countable' BS.to_string BS.of_string), BS.of_string_to_string_inv. Defined.

(* stdpp-specific. *)
Notation "N .@@ x" := (ndot (A := bs) N x%bs)
  (at level 19, left associativity, format "N .@@ x") : stdpp_scope.
Notation "(.@@)" := (ndot (A := bs)) (only parsing) : stdpp_scope.

#[deprecated(since="20240521", note="Use [BS.concat].")]
Notation sepBy := BS.concat (only parsing).
