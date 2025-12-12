(*
 * Copyright (c) 2020-2021,2023 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bluerock.prelude.list_numbers.
Require Export bluerock.prelude.arith.z_to_bytes.
Require Import stdpp.numbers.
Require Import bluerock.prelude.arith.types.
Require Import bluerock.lang.cpp.semantics.values.

Lemma N_of_nat_to_nat a b : N.of_nat a = b -> a = N.to_nat b.
Proof. intros. lia. Qed.

Section with_σ.
  Context {σ : genv}.

  Lemma _Z_to_bytes_has_type_prop (cnt : nat) (endianness : endian) sign (z : Z) :
    List.Forall (fun (v : N) => has_type_prop (Vn v) Tbyte) (_Z_to_bytes cnt endianness sign z).
  Proof.
    eapply List.Forall_impl.
    2: { exact: _Z_to_bytes_range. }
    move => ? /= ?.
    rewrite -has_int_type.
    rewrite/bitsize.bound/bitsize.min_val/bitsize.max_val/=.
    lia.
  Qed.

  Lemma _Z_from_bytes_unsigned_le_has_type_prop (sz : int_rank.t) :
    forall (bytes : list N),
      lengthN bytes = int_rank.bytesN sz ->
      has_type_prop (_Z_from_bytes_unsigned_le bytes) (Tnum sz Unsigned).
  Proof.
    intros * Hlength; rewrite -has_int_type/bitsize.bound/=.
    rewrite /lengthN/int_rank.bytesN in Hlength.
    apply N_of_nat_to_nat in Hlength.
    eapply _Z_from_bytes_unsigned_le_bound; rewrite Hlength.
    destruct sz=> /=; lia.
  Qed.

  Lemma _Z_from_bytes_le_has_type_prop (bytes : list N) (sz : int_rank.t) (sgn : signed) :
    lengthN bytes = int_rank.bytesN sz ->
    has_type_prop (_Z_from_bytes_le sgn bytes) (Tnum sz sgn).
  Proof.
    move => Hlength. rewrite /_Z_from_bytes_le.
    case_match; subst; last by apply _Z_from_bytes_unsigned_le_has_type_prop.
    rewrite /lengthN /int_rank.bytesN in Hlength. apply N_of_nat_to_nat in Hlength; rewrite Hlength.
    unfold operator.to_signed_bits.
    rewrite bool_decide_false; last by destruct sz.
    destruct sz => /=.
    all: repeat (destruct bytes as [|? bytes]; simpl in Hlength; try lia; clear Hlength).
    all: case_bool_decide; rewrite -has_int_type /bitsize.bound/=;
      try match goal with
      | |- context[Z.modulo ?a ?b] => pose proof (Z.mod_pos_bound a b ltac:(lia)); lia
      end.
  Qed.

  Lemma _Z_from_bytes_has_type_prop :
    forall (endianness : endian) (sz : int_rank.t) (sgn : signed) (bytes : list N),
      lengthN bytes = int_rank.bytesN sz ->
      has_type_prop (Vint (_Z_from_bytes endianness sgn bytes)) (Tnum sz sgn).
  Proof.
    intros * Hlength.
    rewrite _Z_from_bytes_eq/_Z_from_bytes_def.
    eapply _Z_from_bytes_le_has_type_prop.
    case_match; auto; unfold lengthN in *; by rewrite length_rev.
  Qed.
End with_σ.
