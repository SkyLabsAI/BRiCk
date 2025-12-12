(*
 * Copyright (c) 2020-23 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import elpi.apps.locker.locker.

Require Import bluerock.prelude.base.
Require Import bluerock.prelude.numbers.
Require Import bluerock.prelude.arith.operator.
Require Import bluerock.lang.cpp.syntax.
Require Import bluerock.lang.cpp.semantics.values.

#[local] Open Scope Z_scope.

(** Architecture independent character values

    To unify the *value* representation of characters, we store characters
    in an architecture-independent way as [unsigned] integers (using [N]).

    Effectively, this is like storing values of type `char` as if they were
    `unsigned char` and re-interpreting the bits as `signed char` before
    performing operations on them. Note that because this is a logical-only
    conversion, it does not require a boundedness check, i.e. for 8-bit
    characters, 255 should mean -1 on a signed platform *regardless* of the
    C++ language version.

    The conversion from this representation to its integral representation
    is typed *on both sides* meaning that you need both the source and the
    target type information in order to perfom the conversion.

    The low-level conversion functions are included here to fully document
    the representation. [conv_int] abstracts these details for use in the
    rest of the semantics.
 *)

mlock
Definition to_char (from_sz : N) (from_sgn : signed) (to_bits : N) (*to_sgn : signed*) (v : Z) : N :=
  Z.to_N $ v `mod` 2^to_bits.

mlock
Definition of_char (from_bits : N) (from_sgn : signed) (to_bits : N) (to_sgn : signed) (n : N) : Z :=
  (* first we need to sign extend using frm_sgn *)
  let n : Z :=
    if from_sgn is Signed then
      if bool_decide (n < 2^(from_bits-1)) then n else to_signed_bits from_bits n
    else n in
  if to_sgn is Signed then to_signed_bits to_bits n else to_unsigned_bits to_bits n.

(* suppose that you are in an architecture with unsigned characters
    and you wrote (128)
  *)
Module Type CHAR_TESTS.
  Goal of_char 8 Signed 32 Signed 1 = 1. Proof. by rewrite of_char.unlock. Qed.
  Goal of_char 8 Signed 32 Signed 128 = -128. Proof. by rewrite of_char.unlock. Qed.
  Goal of_char 8 Signed 32 Signed 127 = 127. Proof. by rewrite of_char.unlock. Qed.

  Goal of_char 8 Signed 16 Unsigned 128 = 65408. Proof. by rewrite of_char.unlock. Qed.
  Goal of_char 32 Signed 8 Signed 256 = 0. Proof. by rewrite of_char.unlock. Qed.
  Goal of_char 32 Signed 8 Signed 128 = -128. Proof. by rewrite of_char.unlock. Qed.
  Goal of_char 32 Signed 16 Signed 128 = 128. Proof. by rewrite of_char.unlock. Qed.
  Goal of_char 16 Signed 8 Unsigned 128 = 128. Proof. by rewrite of_char.unlock. Qed.

  (* Other tests *)
  Goal of_char 8 Signed 8 Unsigned 128 = 128. Proof. by rewrite of_char.unlock. Qed.
  Goal of_char 16 Signed 8 Unsigned 128 = 128. Proof. by rewrite of_char.unlock. Qed.

  Goal of_char 8 Signed 8 Signed 128 = -128. Proof. by rewrite of_char.unlock. Qed.
  Goal of_char 8 Signed 8 Signed 129 = -127. Proof. by rewrite of_char.unlock. Qed.

  Goal of_char 16 Signed 8 Signed 128 = -128. Proof. by rewrite of_char.unlock. Qed.
  Goal of_char 16 Signed 8 Signed 129 = -127. Proof. by rewrite of_char.unlock. Qed.

  Goal of_char 8 Unsigned 8 Signed 129 = -127. Proof. by rewrite of_char.unlock. Qed.
  Goal of_char 16 Unsigned 8 Signed 129 = -127. Proof. by rewrite of_char.unlock. Qed.

  Goal of_char 8 Unsigned 8 Signed 128 = -128. Proof. by rewrite of_char.unlock. Qed.
  Goal of_char 8 Unsigned 16 Signed 128 = 128. Proof. by rewrite of_char.unlock. Qed.

  Goal of_char 4 Signed 8 Unsigned 8 = 248. Proof. by rewrite of_char.unlock. Qed.
  Goal to_char 8 Unsigned 4 248 = 8%N. Proof. by rewrite to_char.unlock. Qed.

  Goal of_char 8 Signed 16 Signed 129 = -127%N. Proof. by rewrite of_char.unlock; compute. Qed.
  Goal to_char 16 Signed 8 (-127)%Z = 129%N. Proof. by rewrite to_char.unlock; compute. Qed.

  Goal of_char 8 Signed 4 Signed 17 = 1%N. Proof. by rewrite of_char.unlock; compute. Qed.
End CHAR_TESTS.


Lemma of_char_spec_low (from_bits : N) (from_sgn : signed)
  (to_bits : N) (to_sgn : signed) (v : N) :
  (from_bits ≤ to_bits)%Z
  -> (0 <= v < 2 ^ (from_bits - 1))%Z
  -> of_char from_bits from_sgn to_bits to_sgn v = v.
Proof.
  move=>Ho [Hlb Hub].

  have Hsz : (v < 2 ^ (to_bits - 1))%Z.
  { apply: Z.lt_le_trans; first done.
    by apply: Z.pow_le_mono; lia. }

  have Hop : (2 ^ (from_bits - 1) ≤ 2 ^ to_bits)%Z
    by apply: Z.pow_le_mono; lia.

  rewrite of_char.unlock.
  case Hs: from_sgn.
  - case: bool_decide_reflect; last by done.
    case: to_sgn=>?; first by apply: to_signed_bits_id.
    by rewrite /trim Z.mod_small; lia.
  - case: to_sgn; first by apply: to_signed_bits_id; lia.
    by rewrite /= /trim Z.mod_small //; lia.
Qed.

Definition of_char_specf from_bits from_sgn to_bits to_sgn (v : Z) : Z :=
  match to_sgn with
  | Signed => match from_sgn with
             | Signed => (v - 2 ^ from_bits)%Z
             | Unsigned =>
                 if bool_decide (from_bits = to_bits) then
                   (v - 2 ^ from_bits)%Z else v
             end
  | Unsigned => match from_sgn with
             | Signed => (v - 2 ^ from_bits + 2 ^ to_bits)%Z
             | Unsigned => v
             end
  end.

Lemma of_char_spec_high (from_bits : N) (from_sgn : signed) (to_bits : N) (to_sgn : signed) (v : N) :
  (0 < from_bits)%Z
  -> (from_bits ≤ to_bits)%Z
  -> (2 ^ (from_bits - 1) <= v < 2 ^ from_bits)%Z
  -> of_char from_bits from_sgn to_bits to_sgn v =
      of_char_specf from_bits from_sgn to_bits to_sgn v.
Proof.
  move=>Hbits Ho; rewrite of_char.unlock /of_char_specf.
  case Hfs: from_sgn.
  - case: bool_decide_reflect; first by lia.
    move=>? [??]; case Htf: to_sgn.
    + rewrite [to_signed_bits _ v]to_signed_bits_spec_high;
        try by [ lia | case: (from)].
      rewrite to_signed_bits_spec_low //; split.
      * rewrite -Z.le_add_le_sub_l.
        apply: Z.le_trans; last done.

        rewrite Z.le_add_le_sub_r Z.sub_opp_r -Z.le_sub_le_add_l.
        rewrite Z_pow2_half; last lia.
        rewrite Z.add_simpl_r; apply: Z.pow_le_mono; lia.
      * rewrite Z.lt_sub_lt_add_l.
        apply: Z.lt_le_trans; first done.
        by lia.

    + rewrite to_signed_bits_spec_high; try by [| lia].
      rewrite /trim Z_mod_big //; split; last lia.
      rewrite -Z.le_add_le_sub_l; apply: Z.le_trans; last done.


      rewrite Z_pow2_half; last lia.
      rewrite -Z.add_assoc Z.le_add_le_sub_l.
      apply: Zplus_le_compat_l; rewrite -Z.opp_le_mono;
        apply: Z.pow_le_mono; lia.

  - move: Ho=>/Zle_lt_or_eq[Hlt[??]/=|].
    + case: to_sgn.
      * rewrite to_signed_bits_spec_low.

        case: bool_decide_reflect Hlt; by [lia |].

        split; first by apply: Z.le_trans; by [| lia].
        apply: Z.lt_le_trans; first by done.
        by apply: Z.pow_le_mono; lia.

      * rewrite /trim Z.mod_small //.
        split; first by lia.
        apply: Z.lt_le_trans; first done.
        apply: Z.pow_le_mono; lia.

    + move=>Heq; rewrite Heq. move=>[??].
      case: to_sgn; last
        by rewrite /trim Z.mod_small //; lia.
      case: bool_decide_reflect Heq Hbits=>???; last done.
      rewrite to_signed_bits_spec_high; lia.
Qed.

Lemma to_char_spec_low (from_bits : N) (from_sgn : signed) (to_bits : N) (v : Z) :
  (0 <= v < 2 ^ to_bits)%Z
  -> to_char from_bits from_sgn to_bits v = Z.to_N v.
Proof.
  rewrite to_char.unlock.
  intros. by rewrite Z.mod_small.
Qed.

Lemma to_char_spec_high (from_bits : N) (from_sgn : signed) (to_bits : N) (to_sgn : signed) (v : Z) :
  (from_bits ≤ to_bits)%Z
  -> (2 ^ (from_bits - 1) <= v < 2 ^ from_bits)%Z
  -> to_char to_bits to_sgn from_bits
      (of_char_specf from_bits from_sgn to_bits to_sgn v) = (Z.to_N v).
Proof.
  move=>Ho [Hlb Hub].
  have Hpow: (2 ^ from_bits <= 2 ^ to_bits)%Z
    by apply: Z.pow_le_mono.
  have Hlt: (v < 2 ^ to_bits)%Z
    by apply: Z.lt_le_trans.

  rewrite to_char.unlock // /trim /of_char_specf.
  case Hts: to_sgn.
  + case: from_sgn; first
      by rewrite Z_mod_big; lia.
    case: bool_decide_reflect; first
      by move=>->; rewrite Z_mod_big; lia.
    by rewrite Z.mod_small; lia.
  +
    case Hfs: from_sgn; last
      by rewrite Z.mod_small; lia.

    rewrite Zplus_mod.
    have->: (2 ^ to_bits `mod` 2 ^ from_bits = 0).
    { have ->:(Z.of_N to_bits = to_bits - from_bits + from_bits)%Z by lia.
      rewrite Z.pow_add_r; try lia.
      apply: Z.mod_mul; lia. }

    rewrite Z.add_0_r Z.mod_mod; last lia.
    by rewrite Z_mod_big; lia.
Qed.

Lemma of_char_to_char (from_bits : N) (from_sgn : signed) (to_bits : N)
  (to_sgn : signed) (v : N) :
  (0 < from_bits)%Z
  -> (from_bits ≤ to_bits)%Z
  -> (0 <= v < 2 ^ from_bits)%Z
  -> to_char to_bits to_sgn from_bits
          (of_char from_bits from_sgn to_bits to_sgn v) = v.
Proof.
  move=>H0 Ho [Hlb Hub].
  case: (Z.lt_ge_cases v (2 ^ (from_bits - 1))%Z)=>[?|?].
  - by rewrite of_char_spec_low // to_char_spec_low; lia.
  - by rewrite of_char_spec_high // to_char_spec_high // N2Z.id.
Qed.

Lemma of_char_trim (from_bits to_bits : N) (v : Z) :
  (to_bits <> 0%N)
  -> (to_bits <= from_bits)%Z
  -> (2 ^ (from_bits) - 2 ^ (to_bits - 1) ≤ v < 2 ^ from_bits)
  -> of_char to_bits Signed from_bits Unsigned (Z.to_N (trim to_bits v)) = v.
Proof.
  move=>Hne Ho.
  move: (Z.mod_pos_bound v (2 ^ to_bits) ltac:(lia))=>[??].

  rewrite of_char.unlock /trim /to_signed_bits (bool_decide_false _ Hne).
  rewrite Z2N.id; last lia.
  rewrite Z.mod_mod //; last lia.

  rewrite (Z_div_mod_eq_full (2^from_bits) (2 ^ to_bits)).
  set a := (2 ^ from_bits `div` 2 ^ to_bits).
  set b := (2 ^ to_bits).
  set b_2 := (2 ^ (to_bits - 1)).

  have->: (2 ^ from_bits `mod` b = 0).
  { rewrite /b.
    have ->:(Z.of_N from_bits = from_bits - to_bits + to_bits)%Z by lia.
    rewrite Z.pow_add_r; try lia.
    apply: Z.mod_mul; lia. }
  rewrite Z.add_0_r.

  have Hb2: b_2 < b by apply: Z.pow_lt_mono_r; lia.

  move=>[Hlb Hub].

  have Heq: (v `div` b = a - 1) by apply: Z_rem_dev_eq; lia.


  case: bool_decide_reflect=>[?|].
  - move: Hlb.
    rewrite {1}(Z_div_mod_eq_full v b) Heq.
    have {1 2}-> : b = b_2 + b_2; last by lia.
    by apply: Z_pow2_half; lia.

  - have Hpow: (2 ^ Z.of_N to_bits ≤ 2 ^ Z.of_N from_bits)
      by apply: Z.pow_le_mono; lia.
    have Hq: 1 <= (2 ^ Z.of_N from_bits `div` 2 ^ Z.of_N to_bits)
      by apply: Z.div_le_lower_bound; lia.
    have Hba:  b ≤ b * a
      by rewrite {1}(_ : b = b * 1); [apply Z.mul_le_mono_pos_l|]; lia.

    move: (Z.mod_pos_bound v b ltac:(lia))=>[??].

    move=>/Znot_lt_ge Hge; rewrite (bool_decide_true _ Hge).
    rewrite {2}(Z_div_mod_eq_full v b) Heq Z_mod_big; lia.
Qed.

(* architecture-dependent domain where [to_char] is left inverse of [of_char] *)
#[program]
Definition to_char_domP (from_bits : N) (from_sgn : signed) to_bits to_sgn (v : Z) : Prop :=
  match to_sgn with
  | Signed =>  match from_sgn with
              | Signed => (- 2 ^ (to_bits - 1) <= v < 2 ^ (to_bits - 1))%Z
              | Unsigned => (2 ^ (from_bits) - 2 ^ (to_bits - 1) ≤ v < 2 ^ from_bits)
              end
  | Unsigned => match from_sgn with
               | Signed =>
                   if bool_decide (to_bits = from_bits) then
                     (- 2 ^ (to_bits - 1) <= v < 2 ^ (to_bits - 1))%Z
                   else
                     (0 <= v < 2 ^ to_bits)%Z
               | Unsigned => (0 <= v < 2 ^ to_bits)%Z
               end
  end.

Lemma to_char_of_char (from_bits : N) (from_sgn : signed) (to_bits : N)
  (to_sgn : signed) (v : Z) :
  (0 < to_bits)%Z
  -> (to_bits ≤ from_bits)%Z
  -> to_char_domP from_bits from_sgn to_bits to_sgn v
  -> of_char to_bits to_sgn from_bits from_sgn
      (to_char from_bits from_sgn to_bits v) = v.
Proof.
  move=>H0 Ho.

  have H1: (2 ^ (to_bits - 1) < 2 ^ to_bits)%Z
    by apply: Z.pow_lt_mono_r; lia.
  have H2: (2 ^ to_bits <= 2 ^ from_bits)%Z
    by apply: Z.pow_le_mono.

  rewrite to_char.unlock //.

  case: to_sgn.
  - case: from_sgn=>[/=?|[??]].

    + case: (Z.lt_ge_cases v 0)%Z=>[?|?].
      rewrite /trim Z_mod_big; last lia.
      rewrite of_char_spec_high /=; try lia.
      rewrite (Z_pow2_half to_bits); lia.
      rewrite /trim Z.mod_small; last lia.
      rewrite of_char_spec_low; lia.
    +
      case: (Z.lt_ge_cases v ((2 ^ (to_bits - 1)))%Z)=>[?|?].
      rewrite /trim Z.mod_small; last lia.
      rewrite of_char_spec_low; try lia.
      by rewrite of_char_trim; lia.

  - case: from_sgn=>[/=|[??]].
    + case: bool_decide_reflect=>[/N2Z.inj Heq [??]|Heq [??]].

      * case: (Z.lt_ge_cases v 0)%Z=>[?|?].
        rewrite /trim Z_mod_big /=; last lia.
        rewrite of_char_spec_high /=; try lia.
        case: bool_decide_reflect Heq; lia.
        rewrite (Z_pow2_half to_bits); lia.
        rewrite /trim Z.mod_small /=; last lia.
        rewrite of_char_spec_low; lia.
      * rewrite /trim Z.mod_small; last lia.
        case: (Z.lt_ge_cases v ((2 ^ (to_bits - 1)))%Z)=>[?|?].
        rewrite of_char_spec_low; lia.
        rewrite of_char_spec_high /=; try lia.
        case: bool_decide_reflect Heq; lia.
    + rewrite /trim Z.mod_small; last lia.
      case: (Z.lt_ge_cases v ((2 ^ (to_bits - 1)))%Z)=>[?|?].
      rewrite of_char_spec_low; lia.
      rewrite of_char_spec_high /=; lia.
Qed.

Lemma to_char_bounded sz sgn bits z :
  (to_char sz sgn bits z < 2^bits)%N.
Proof.
  rewrite to_char.unlock.
  generalize (Z_mod_lt z (2^bits)). lia.
Qed.

Lemma of_char_bounded (from_sz : N) from_sgn (to_sz : N) to_sgn n :
  0 < to_sz -> 0< from_sz ->
  let min_val : Z := if to_sgn is Signed then -2^(to_sz-1) else 0 in
  let max_val : Z := if to_sgn is Signed then 2^(to_sz-1) else 2^to_sz in
  min_val <= of_char from_sz from_sgn to_sz to_sgn n < max_val.
Proof.
  rewrite of_char.unlock /to_signed_bits; intros.
  assert (2^to_sz = 2 * 2^(to_sz - 1)).
  { have->: Z.of_N to_sz = Z.succ (to_sz - 1) by lia.
    rewrite Z.pow_succ_r; try lia. f_equal. f_equal. lia. }
  #[local] Ltac saturate :=
    repeat match goal with
      | |- context [ Z.modulo ?X ?Y ] =>
          lazymatch goal with
          | H : (0 <= X `mod` Y < Y)%Z |- _ => fail 1
          | |- _ => generalize (Z.mod_pos_bound X Y ltac:(lia)); intro
          end
      end.
  repeat first [ case_bool_decide | case_match ]; rewrite /trim/=; split; try rewrite Zmod_0_l ; saturate; try lia.
Qed.
