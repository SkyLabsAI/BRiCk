(*
 * Copyright (c) 2020-2025 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bluerock.prelude.base.
Require Import bluerock.prelude.arith.types.
Require Import bluerock.prelude.arith.operator.

#[local] Open Scope Z_scope.
(* see
 * https://gcc.gnu.org/onlinedocs/gcc/Other-Builtins.html
 *)

(* Returns one plus the index of the least significant 1-bit of x,
   or if x is zero, returns zero. *)
Definition first_set (sz : bitsize) (n : Z) : Z :=
  let n := trim (bitsize.bitsN sz) n in
  if Z.eqb n 0 then 0
  else
    (fix get ls : Z :=
       match ls with
       | nil => 64
       | l :: ls =>
         if Z.testbit n l
         then 1 + l
         else get ls
       end)%Z (List.map Z.of_nat (seq 0 (N.to_nat (bitsize.bitsN sz)))).
#[global] Arguments first_set : simpl never.

(* Returns the number of trailing 0-bits in x, starting at the least
   significant bit position. If x is 0, the result is undefined. *)
Definition trailing_zeros (sz : bitsize) (n : Z) : Z :=
  (fix get ls : Z :=
     match ls with
     | nil => 64
     | l :: ls =>
       if Z.testbit n l
       then l
       else get ls
     end)%Z (List.map Z.of_nat (seq 0 (N.to_nat (bitsize.bitsN sz)))).
#[global] Arguments trailing_zeros : simpl never.

(* Returns the number of leading 0-bits in x, starting at the most significant
   bit position. If x is 0, the result is undefined. *)
Definition leading_zeros (sz : bitsize) (l : Z) : Z :=
  bitsize.bitsZ sz - Z.log2 (l mod (2^64)).
#[global] Arguments leading_zeros : simpl never.

Module Import churn_bits.
(* TODO: using bool_decide would simplify this reasoning. *)
Ltac churn_bits' :=
  repeat match goal with
  | |- context[(?l <=? ?r)%Z] =>
    let Hnb := fresh "Hnb" in
    let Hn := fresh "Hn" in
    destruct (l <=? r)%Z eqn:Hnb;
      set (Hn := Hnb);
      [ apply Z.leb_le in Hn
      | apply Z.leb_gt in Hn]
  | |- context[(?l <? ?r)%Z] =>
    let Hnb := fresh "Hnb" in
    let Hn := fresh "Hn" in
    destruct (l <? r)%Z eqn:Hnb;
      set (Hn := Hnb);
      [ apply Z.ltb_lt in Hn
      | apply Z.ltb_ge in Hn]
  end; rewrite ?andb_false_l ?andb_false_r ?andb_true_l ?andb_true_r
               ?orb_false_l ?orb_false_r ?orb_true_l ?orb_true_r ?Z.bits_0 //=;
               try lia.

Ltac churn_bits :=
  apply Z.bits_inj'=> n ?;
  repeat (rewrite ?Z.lor_spec ?Z.shiftl_spec ?Z.land_spec ?Z.shiftr_spec; try lia);
  rewrite !Z.testbit_ones; try lia;
  churn_bits'.
End churn_bits.

Section BitsTheory.
  Lemma log2_lt_pow2ge:
    ∀ a b : Z,
      0 <= a →
      Z.log2 a < b ->
      a < 2 ^ b.
  Proof.
    intros.
    assert (a=0 \/ 0 < a) as [Hc | Hc] by lia.
    {
      subst.
      simpl in *.
      apply Z.pow_pos_nonneg; lia.
    }
    {
      apply Z.log2_lt_pow2; auto.
    }
  Qed.

  Lemma ZlogLtPow2:   forall (a w: Z),
      0 < w ->
      0 ≤ a < 2 ^ w → Z.log2 a < w.
  Proof.
    intros.
    assert (a=0 \/ 0 < a) as Hc by lia.
    destruct Hc as [Hc | Hc]; [subst; simpl; lia | ].
    apply Z.log2_lt_pow2; lia.
  Qed.

  Lemma ZlorRange:
    forall (a b: Z) (w : N),
      0 <= a < (2 ^ Z.of_N w) ->
      0 <= b < (2 ^ Z.of_N w) ->
      0 <= Z.lor a b < (2 ^ Z.of_N w).
  Proof.
    intros.
    assert (w=0 \/ 0 < w)%N as [Hc | Hc] by lia.
    {
      subst.  simpl in *.
      assert (a=0) by lia.
      assert (b=0) by lia.
      subst.
      simpl.
      compute. firstorder.
    }
    apply and_wlog_r; [apply Z.lor_nonneg; lia | ].
    intros.
    apply log2_lt_pow2ge; [assumption | ].
    rewrite -> Z.log2_lor by lia.
    apply ZlogLtPow2 in H; try lia.
    apply ZlogLtPow2 in H0;  lia.
  Qed.
End BitsTheory.

Section Byte.
  Definition _get_byte (x: Z) (n: nat): Z := Z.land (x ≫ (8 * n)) (Z.ones 8).
  Definition _set_byte (x: Z) (n: nat): Z := (Z.land (Z.ones 8) x) ≪ (8 * n).

  Section Theory.
    Lemma _get_byte_0:
      forall (idx: nat),
        _get_byte 0 idx = 0.
    Proof. intros; by rewrite /_get_byte Z.shiftr_0_l Z.land_0_l. Qed.

    Lemma _set_byte_0:
      forall (idx: nat),
        _set_byte 0 idx = 0.
    Proof. intros; by rewrite /_set_byte Z.shiftl_0_l. Qed.

    #[local] Lemma Z_mul_of_nat_S (z : Z) (n : nat) : (z * S n)%Z = (z + z * n)%Z.
    Proof. lia. Qed.

    Lemma _get_byte_S_idx:
      forall (v: Z) (idx: nat),
        _get_byte v (S idx) = _get_byte (v ≫ 8) idx.
    Proof.
      intros; rewrite /_get_byte.
      by rewrite Z.shiftr_shiftr ?Z_mul_of_nat_S; lia.
    Qed.

    Lemma _get_byte_lor:
      forall (v v': Z) (idx: nat),
        _get_byte (Z.lor v v') idx =
        Z.lor (_get_byte v idx) (_get_byte v' idx).
    Proof. intros *; rewrite /_get_byte; churn_bits. Qed.

    Lemma _set_byte_S_idx:
      forall (v: Z) (idx: nat),
        _set_byte v (S idx) = ((_set_byte v idx) ≪ 8)%Z.
    Proof.
      intros; rewrite /_set_byte.
      by rewrite Z.shiftl_shiftl ?Z_mul_of_nat_S ?(Z.add_comm 8); lia.
    Qed.

    Lemma _set_byte_lor:
      forall (v v': Z) (idx: nat),
        _set_byte (Z.lor v v') idx =
        Z.lor (_set_byte v idx) (_set_byte v' idx).
    Proof. intros *; rewrite /_set_byte; churn_bits. Qed.

    Lemma _set_byte_shiftl_idx:
      forall (idx idx': nat) shift v,
        idx' <= idx ->
        (shift = 8 * Z.of_nat idx')%Z ->
        (_set_byte v idx ≫ shift)%Z = _set_byte v (idx - idx').
    Proof.
      intros * Hidx Hshift; rewrite /_set_byte; subst; churn_bits.
      f_equal; lia.
    Qed.

    Lemma _get_byte_bound:
      forall (v : Z) (idx : nat),
        (0 <= _get_byte v idx < 256)%Z.
    Proof.
      intros *; rewrite /_get_byte Z.land_ones; try lia.
      pose proof (Z.mod_pos_bound (v ≫ (8 * idx)) 256) as [? ?]; try lia.
      now replace (2 ^ 8) with 256%Z by lia.
    Qed.

    Lemma _get_byte_nonneg:
      forall (v: Z) (idx: nat),
        (0 <= _get_byte v idx)%Z.
    Proof. intros *; pose proof (_get_byte_bound v idx); lia. Qed.

    Lemma _set_byte_bound:
      forall (v : Z) (idx : nat),
        (0 <= _set_byte v idx < 2 ^ (8 * (idx + 1)))%Z.
    Proof.
      intros; rewrite /_set_byte Z.land_comm Z.land_ones; try lia.
      rewrite Z.shiftl_mul_pow2; try lia.
      pose proof (Z.mod_pos_bound v 256) as [? ?]; try lia.
      replace (2 ^ (8 * (idx + 1))) with ((2 ^ 8) * (2 ^ (8 * idx)))
        by (rewrite Z.mul_add_distr_l Zpower_exp; lia).
      replace (2 ^ 8) with 256%Z by lia.
      split.
      - apply Z.mul_nonneg_nonneg; auto.
        apply Z.pow_nonneg; lia.
      - apply Zmult_lt_compat_r; auto.
        apply Z.pow_pos_nonneg; lia.
    Qed.

    Lemma _set_byte_nonneg:
      forall (v: Z) (idx: nat),
        (0 <= _set_byte v idx)%Z.
    Proof. intros *; pose proof (_set_byte_bound v idx); lia. Qed.

    Lemma _set_byte_testbit_low:
      forall idx v n,
        0 <= n ->
        n < 8 * Z.of_nat idx ->
        Z.testbit (_set_byte v idx) n = false.
    Proof.
      intros * Hnonneg Hn.
      repeat (rewrite ?Z.lor_spec ?Z.shiftl_spec ?Z.land_spec ?Z.shiftr_spec; try lia).
      rewrite !Z.testbit_ones; lia.
    Qed.

    Lemma _set_byte_testbit_high:
      forall idx' idx v n,
        (idx' < idx)%nat ->
        8 * Z.of_nat idx <= n ->
        Z.testbit (_set_byte v idx') n = false.
    Proof.
      intros * Hidx Hn.
      repeat (rewrite ?Z.lor_spec ?Z.shiftl_spec ?Z.land_spec ?Z.shiftr_spec; try lia).
      rewrite !Z.testbit_ones; lia.
    Qed.

    Lemma _set_byte_land_no_overlap:
      forall (idx idx': nat) mask v,
        idx <> idx' ->
        (mask = Z.ones 8 ≪ (8 * Z.of_nat idx'))%Z ->
        Z.land (_set_byte v idx) mask = 0.
    Proof. intros * Hidx Hmask; rewrite /_set_byte; subst; churn_bits. Qed.

    Lemma _set_byte_land_useless:
      forall idx mask v,
        (mask = Z.ones 8 ≪ (8 * Z.of_nat idx))%Z ->
        Z.land (_set_byte v idx) mask =
        _set_byte v idx.
    Proof. intros * Hmask; rewrite /_set_byte; subst; churn_bits. Qed.

    Lemma _set_byte_shiftr_big:
      forall (idx: nat) (idx': Z) v,
        (Z.of_nat idx < idx')%Z ->
        (_set_byte v idx ≫ (8 * idx'))%Z = 0.
    Proof. intros * Hidx; rewrite /_set_byte; churn_bits. Qed.

    Lemma _get_0_set_0_eq:
      forall v,
        _get_byte v 0 = _set_byte v 0.
    Proof. intros *; rewrite /_get_byte/_set_byte; churn_bits. Qed.

    Lemma _set_get_0:
      forall v idx,
        _set_byte (_get_byte v 0) idx = _set_byte v idx.
    Proof.
      intros *; rewrite /_get_byte/_set_byte.
      apply Z.bits_inj'=> n ?.
      repeat (rewrite ?Z.lor_spec ?Z.land_spec; try lia).
      repeat (rewrite ?Z.shiftl_spec; try lia).
      repeat (rewrite ?Z.lor_spec ?Z.land_spec; try lia).
      assert (n < 8 * idx \/ 8 * idx <= n) as [Hn | Hn] by lia.
      - rewrite !Z.testbit_neg_r; [reflexivity | lia.. ].
      - rewrite !Z.shiftr_spec; try lia.
        rewrite !Z.testbit_ones; try lia.
        churn_bits'.
    Qed.

    Lemma _get_set_byte_no_overlap:
      forall (v: Z) (idx idx': nat),
        idx <> idx' ->
        _get_byte (_set_byte v idx) idx' = 0.
    Proof. intros * Hidx; rewrite /_get_byte/_set_byte; churn_bits. Qed.

    Lemma _get_set_byte_roundtrip:
      forall (v: Z) (idx: nat),
        _get_byte (_set_byte v idx) idx = _get_byte v 0.
    Proof.
      intros *; rewrite /_get_byte/_set_byte; churn_bits.
      f_equal; lia.
    Qed.

    Lemma _set_get_byte_roundtrip:
      forall (v: Z) (idx: nat),
        _set_byte (_get_byte v idx) idx =
        _get_byte v idx ≪ (8 * idx).
    Proof.
      intros *; rewrite /_get_byte/_set_byte.

      apply Z.bits_inj' => n ?.
      repeat (rewrite ?Z.lor_spec ?Z.land_spec; try lia).
      repeat (rewrite ?Z.shiftl_spec; try lia).
      repeat (rewrite ?Z.lor_spec ?Z.land_spec; try lia).
      assert (n < 8 * idx \/ 8 * idx <= n) as [Hn | Hn] by lia.
      - rewrite !Z.testbit_neg_r; [reflexivity | lia.. ].
      - rewrite !Z.shiftr_spec; try lia.
        rewrite !Z.testbit_ones; try lia.
        churn_bits'.
    Qed.
  End Theory.

  Section split.
    Lemma split8:
      forall z,
        0 <= z < 2^bitsize.bitsZ bitsize.W8 ->
        z = _set_byte (_get_byte z 0) 0.
    Proof.
      intros * Hbounds; rewrite _set_get_0.
      rewrite /_set_byte Z.shiftl_0_r.
      rewrite Z.land_comm Z.land_ones; try lia.
      symmetry; now apply Z.mod_small.
    Qed.

    Lemma split16:
      forall z,
        0 <= z < 2^bitsize.bitsZ bitsize.W16 ->
        z = Z.lor (_set_byte (_get_byte z 0) 0)
                  (_set_byte (_get_byte z 1) 1).
    Proof.
      intros * Hbounds; simpl in Hbounds.
      apply Z.bits_inj'=> n ?.
      assert (n < 8 * 1%nat \/ 8 * 1%nat <= n < 8 * 2%nat \/ 8 * 2%nat <= n)
        as [Hn | [Hn | Hn]]
        by lia; rewrite !Z.lor_spec;
        [ rewrite (_set_byte_testbit_low 1); auto; try lia
        | rewrite (_set_byte_testbit_high 0 1); auto; try lia
        | rewrite (_set_byte_testbit_high 0 2); auto; try lia;
            rewrite (_set_byte_testbit_high 1 2); auto; try lia;
            apply Z.testbit_false; [by lia |];
            rewrite Z.div_small; [apply Z.mod_0_l; lia |];
            pose proof (Z.pow_le_mono_r 2 16 n ltac:(lia) ltac:(auto)); lia
        ]; rewrite ?orb_false_l ?orb_false_r;
        repeat (rewrite ?Z.lor_spec ?Z.shiftl_spec ?Z.land_spec ?Z.shiftr_spec; try lia);
        rewrite !Z.testbit_ones; try lia;
        churn_bits'; now rewrite Z.sub_add.
    Qed.

    Lemma split32:
      forall z,
        0 <= z < 2^bitsize.bitsZ bitsize.W32 ->
        z = Z.lor (_set_byte (_get_byte z 0) 0)
            (Z.lor (_set_byte (_get_byte z 1) 1)
             (Z.lor (_set_byte (_get_byte z 2) 2)
                    (_set_byte (_get_byte z 3) 3))).
    Proof.
      intros * Hbounds; simpl in Hbounds.
      apply Z.bits_inj'=> n ?.
      assert (n < 8 * 1%nat \/
              8 * 1%nat <= n < 8 * 2%nat \/
              8 * 2%nat <= n < 8 * 3%nat \/
              8 * 3%nat <= n < 8 * 4%nat \/
              8 * 4%nat <= n)
        as [Hn | [Hn | [Hn | [Hn | Hn]]]]
        by lia; rewrite !Z.lor_spec;
        [ rewrite (_set_byte_testbit_low 1); auto; try lia;
            rewrite (_set_byte_testbit_low 2); auto; try lia;
            rewrite (_set_byte_testbit_low 3); auto; try lia
        | rewrite (_set_byte_testbit_high 0 1); auto; try lia;
            rewrite (_set_byte_testbit_low 2); auto; try lia;
            rewrite (_set_byte_testbit_low 3); auto; try lia
        | rewrite (_set_byte_testbit_high 0 2); auto; try lia;
            rewrite (_set_byte_testbit_high 1 2); auto; try lia;
            rewrite (_set_byte_testbit_low 3); auto; try lia
        | rewrite (_set_byte_testbit_high 0 3); auto; try lia;
            rewrite (_set_byte_testbit_high 1 3); auto; try lia;
            rewrite (_set_byte_testbit_high 2 3); auto; try lia
        | rewrite (_set_byte_testbit_high 0 4); auto; try lia;
            rewrite (_set_byte_testbit_high 1 4); auto; try lia;
            rewrite (_set_byte_testbit_high 2 4); auto; try lia;
            rewrite (_set_byte_testbit_high 3 4); auto; try lia;
            apply Z.testbit_false; [by lia |];
            rewrite Z.div_small; [apply Z.mod_0_l; lia |];
            pose proof (Z.pow_le_mono_r 2 32 n ltac:(lia) ltac:(auto)); lia
        ]; rewrite ?orb_false_l ?orb_false_r;
        repeat (rewrite ?Z.lor_spec ?Z.shiftl_spec ?Z.land_spec ?Z.shiftr_spec; try lia);
        rewrite !Z.testbit_ones; try lia;
        churn_bits'; now rewrite Z.sub_add.
    Qed.

    Lemma split64:
      forall z,
        0 <= z < 2^bitsize.bitsZ bitsize.W64 ->
        z = Z.lor (_set_byte (_get_byte z 0) 0)
            (Z.lor (_set_byte (_get_byte z 1) 1)
             (Z.lor (_set_byte (_get_byte z 2) 2)
              (Z.lor (_set_byte (_get_byte z 3) 3)
               (Z.lor (_set_byte (_get_byte z 4) 4)
                (Z.lor (_set_byte (_get_byte z 5) 5)
                 (Z.lor (_set_byte (_get_byte z 6) 6)
                        (_set_byte (_get_byte z 7) 7))))))).
    Proof.
      intros * Hbounds; simpl in Hbounds.
      apply Z.bits_inj'=> n ?.
      assert (n < 8 * 1%nat \/
              8 * 1%nat <= n < 8 * 2%nat \/
              8 * 2%nat <= n < 8 * 3%nat \/
              8 * 3%nat <= n < 8 * 4%nat \/
              8 * 4%nat <= n < 8 * 5%nat \/
              8 * 5%nat <= n < 8 * 6%nat \/
              8 * 6%nat <= n < 8 * 7%nat \/
              8 * 7%nat <= n < 8 * 8%nat \/
              8 * 8%nat <= n)
        as [Hn | [Hn | [Hn | [Hn | [Hn | [Hn | [Hn | [Hn | Hn]]]]]]]]
        by lia; rewrite !Z.lor_spec;
        [ rewrite (_set_byte_testbit_low 1); auto; try lia;
            rewrite (_set_byte_testbit_low 2); auto; try lia;
            rewrite (_set_byte_testbit_low 3); auto; try lia;
            rewrite (_set_byte_testbit_low 4); auto; try lia;
            rewrite (_set_byte_testbit_low 5); auto; try lia;
            rewrite (_set_byte_testbit_low 6); auto; try lia;
            rewrite (_set_byte_testbit_low 7); auto; try lia
        | rewrite (_set_byte_testbit_high 0 1); auto; try lia;
            rewrite (_set_byte_testbit_low 2); auto; try lia;
            rewrite (_set_byte_testbit_low 3); auto; try lia;
            rewrite (_set_byte_testbit_low 4); auto; try lia;
            rewrite (_set_byte_testbit_low 5); auto; try lia;
            rewrite (_set_byte_testbit_low 6); auto; try lia;
            rewrite (_set_byte_testbit_low 7); auto; try lia
        | rewrite (_set_byte_testbit_high 0 2); auto; try lia;
            rewrite (_set_byte_testbit_high 1 2); auto; try lia;
            rewrite (_set_byte_testbit_low 3); auto; try lia;
            rewrite (_set_byte_testbit_low 4); auto; try lia;
            rewrite (_set_byte_testbit_low 5); auto; try lia;
            rewrite (_set_byte_testbit_low 6); auto; try lia;
            rewrite (_set_byte_testbit_low 7); auto; try lia
        | rewrite (_set_byte_testbit_high 0 3); auto; try lia;
            rewrite (_set_byte_testbit_high 1 3); auto; try lia;
            rewrite (_set_byte_testbit_high 2 3); auto; try lia;
            rewrite (_set_byte_testbit_low 4); auto; try lia;
            rewrite (_set_byte_testbit_low 5); auto; try lia;
            rewrite (_set_byte_testbit_low 6); auto; try lia;
            rewrite (_set_byte_testbit_low 7); auto; try lia
        | rewrite (_set_byte_testbit_high 0 4); auto; try lia;
            rewrite (_set_byte_testbit_high 1 4); auto; try lia;
            rewrite (_set_byte_testbit_high 2 4); auto; try lia;
            rewrite (_set_byte_testbit_high 3 4); auto; try lia;
            rewrite (_set_byte_testbit_low 5); auto; try lia;
            rewrite (_set_byte_testbit_low 6); auto; try lia;
            rewrite (_set_byte_testbit_low 7); auto; try lia
        | rewrite (_set_byte_testbit_high 0 5); auto; try lia;
            rewrite (_set_byte_testbit_high 1 5); auto; try lia;
            rewrite (_set_byte_testbit_high 2 5); auto; try lia;
            rewrite (_set_byte_testbit_high 3 5); auto; try lia;
            rewrite (_set_byte_testbit_high 4 5); auto; try lia;
            rewrite (_set_byte_testbit_low 6); auto; try lia;
            rewrite (_set_byte_testbit_low 7); auto; try lia
        | rewrite (_set_byte_testbit_high 0 6); auto; try lia;
            rewrite (_set_byte_testbit_high 1 6); auto; try lia;
            rewrite (_set_byte_testbit_high 2 6); auto; try lia;
            rewrite (_set_byte_testbit_high 3 6); auto; try lia;
            rewrite (_set_byte_testbit_high 4 6); auto; try lia;
            rewrite (_set_byte_testbit_high 5 6); auto; try lia;
            rewrite (_set_byte_testbit_low 7); auto; try lia
        | rewrite (_set_byte_testbit_high 0 7); auto; try lia;
            rewrite (_set_byte_testbit_high 1 7); auto; try lia;
            rewrite (_set_byte_testbit_high 2 7); auto; try lia;
            rewrite (_set_byte_testbit_high 3 7); auto; try lia;
            rewrite (_set_byte_testbit_high 4 7); auto; try lia;
            rewrite (_set_byte_testbit_high 5 7); auto; try lia;
            rewrite (_set_byte_testbit_high 6 7); auto; try lia
        | rewrite (_set_byte_testbit_high 0 8); auto; try lia;
            rewrite (_set_byte_testbit_high 1 8); auto; try lia;
            rewrite (_set_byte_testbit_high 2 8); auto; try lia;
            rewrite (_set_byte_testbit_high 3 8); auto; try lia;
            rewrite (_set_byte_testbit_high 4 8); auto; try lia;
            rewrite (_set_byte_testbit_high 5 8); auto; try lia;
            rewrite (_set_byte_testbit_high 6 8); auto; try lia;
            rewrite (_set_byte_testbit_high 7 8); auto; try lia;
            apply Z.testbit_false; [by lia |];
            rewrite Z.div_small; [apply Z.mod_0_l; lia |];
            pose proof (Z.pow_le_mono_r 2 64 n ltac:(lia) ltac:(auto)); lia
        ]; rewrite ?orb_false_l ?orb_false_r;
        repeat (rewrite ?Z.lor_spec ?Z.shiftl_spec ?Z.land_spec ?Z.shiftr_spec; try lia);
        rewrite !Z.testbit_ones; try lia;
        churn_bits'; now rewrite Z.sub_add.
    Qed.

    Lemma split128:
      forall z,
        0 <= z < 2^bitsize.bitsZ bitsize.W128 ->
        z = Z.lor (_set_byte (_get_byte z 0) 0)
            (Z.lor (_set_byte (_get_byte z 1) 1)
             (Z.lor (_set_byte (_get_byte z 2) 2)
              (Z.lor (_set_byte (_get_byte z 3) 3)
               (Z.lor (_set_byte (_get_byte z 4) 4)
                (Z.lor (_set_byte (_get_byte z 5) 5)
                 (Z.lor (_set_byte (_get_byte z 6) 6)
                  (Z.lor (_set_byte (_get_byte z 7) 7)
                   (Z.lor (_set_byte (_get_byte z 8) 8)
                    (Z.lor (_set_byte (_get_byte z 9) 9)
                     (Z.lor (_set_byte (_get_byte z 10) 10)
                      (Z.lor (_set_byte (_get_byte z 11) 11)
                       (Z.lor (_set_byte (_get_byte z 12) 12)
                        (Z.lor (_set_byte (_get_byte z 13) 13)
                         (Z.lor (_set_byte (_get_byte z 14) 14)
                                (_set_byte (_get_byte z 15) 15))))))))))))))).
    Proof.
      intros * Hbounds; simpl in Hbounds.
      apply Z.bits_inj'=> n ?.
      assert (n < 8 * 1%nat \/
              8 * 1%nat <= n < 8 * 2%nat \/
              8 * 2%nat <= n < 8 * 3%nat \/
              8 * 3%nat <= n < 8 * 4%nat \/
              8 * 4%nat <= n < 8 * 5%nat \/
              8 * 5%nat <= n < 8 * 6%nat \/
              8 * 6%nat <= n < 8 * 7%nat \/
              8 * 7%nat <= n < 8 * 8%nat \/
              8 * 8%nat <= n < 8 * 9%nat \/
              8 * 9%nat <= n < 8 * 10%nat \/
              8 * 10%nat <= n < 8 * 11%nat \/
              8 * 11%nat <= n < 8 * 12%nat \/
              8 * 12%nat <= n < 8 * 13%nat \/
              8 * 13%nat <= n < 8 * 14%nat \/
              8 * 14%nat <= n < 8 * 15%nat \/
              8 * 15%nat <= n < 8 * 16%nat \/
              8 * 16%nat <= n)
        as [Hn | [Hn | [Hn | [Hn | [Hn | [Hn | [Hn | [Hn | [Hn | [Hn | [Hn | [Hn | [Hn | [Hn | [Hn | [Hn | Hn]]]]]]]]]]]]]]]]
        by lia; rewrite !Z.lor_spec;
        [ rewrite (_set_byte_testbit_low 1); auto; try lia;
            rewrite (_set_byte_testbit_low 2); auto; try lia;
            rewrite (_set_byte_testbit_low 3); auto; try lia;
            rewrite (_set_byte_testbit_low 4); auto; try lia;
            rewrite (_set_byte_testbit_low 5); auto; try lia;
            rewrite (_set_byte_testbit_low 6); auto; try lia;
            rewrite (_set_byte_testbit_low 7); auto; try lia;
            rewrite (_set_byte_testbit_low 8); auto; try lia;
            rewrite (_set_byte_testbit_low 9); auto; try lia;
            rewrite (_set_byte_testbit_low 10); auto; try lia;
            rewrite (_set_byte_testbit_low 11); auto; try lia;
            rewrite (_set_byte_testbit_low 12); auto; try lia;
            rewrite (_set_byte_testbit_low 13); auto; try lia;
            rewrite (_set_byte_testbit_low 14); auto; try lia;
            rewrite (_set_byte_testbit_low 15); auto; try lia
        | rewrite (_set_byte_testbit_high 0 1); auto; try lia;
            rewrite (_set_byte_testbit_low 2); auto; try lia;
            rewrite (_set_byte_testbit_low 3); auto; try lia;
            rewrite (_set_byte_testbit_low 4); auto; try lia;
            rewrite (_set_byte_testbit_low 5); auto; try lia;
            rewrite (_set_byte_testbit_low 6); auto; try lia;
            rewrite (_set_byte_testbit_low 7); auto; try lia;
            rewrite (_set_byte_testbit_low 8); auto; try lia;
            rewrite (_set_byte_testbit_low 9); auto; try lia;
            rewrite (_set_byte_testbit_low 10); auto; try lia;
            rewrite (_set_byte_testbit_low 11); auto; try lia;
            rewrite (_set_byte_testbit_low 12); auto; try lia;
            rewrite (_set_byte_testbit_low 13); auto; try lia;
            rewrite (_set_byte_testbit_low 14); auto; try lia;
            rewrite (_set_byte_testbit_low 15); auto; try lia
        | rewrite (_set_byte_testbit_high 0 2); auto; try lia;
            rewrite (_set_byte_testbit_high 1 2); auto; try lia;
            rewrite (_set_byte_testbit_low 3); auto; try lia;
            rewrite (_set_byte_testbit_low 4); auto; try lia;
            rewrite (_set_byte_testbit_low 5); auto; try lia;
            rewrite (_set_byte_testbit_low 6); auto; try lia;
            rewrite (_set_byte_testbit_low 7); auto; try lia;
            rewrite (_set_byte_testbit_low 8); auto; try lia;
            rewrite (_set_byte_testbit_low 9); auto; try lia;
            rewrite (_set_byte_testbit_low 10); auto; try lia;
            rewrite (_set_byte_testbit_low 11); auto; try lia;
            rewrite (_set_byte_testbit_low 12); auto; try lia;
            rewrite (_set_byte_testbit_low 13); auto; try lia;
            rewrite (_set_byte_testbit_low 14); auto; try lia;
            rewrite (_set_byte_testbit_low 15); auto; try lia
        | rewrite (_set_byte_testbit_high 0 3); auto; try lia;
            rewrite (_set_byte_testbit_high 1 3); auto; try lia;
            rewrite (_set_byte_testbit_high 2 3); auto; try lia;
            rewrite (_set_byte_testbit_low 4); auto; try lia;
            rewrite (_set_byte_testbit_low 5); auto; try lia;
            rewrite (_set_byte_testbit_low 6); auto; try lia;
            rewrite (_set_byte_testbit_low 7); auto; try lia;
            rewrite (_set_byte_testbit_low 8); auto; try lia;
            rewrite (_set_byte_testbit_low 9); auto; try lia;
            rewrite (_set_byte_testbit_low 10); auto; try lia;
            rewrite (_set_byte_testbit_low 11); auto; try lia;
            rewrite (_set_byte_testbit_low 12); auto; try lia;
            rewrite (_set_byte_testbit_low 13); auto; try lia;
            rewrite (_set_byte_testbit_low 14); auto; try lia;
            rewrite (_set_byte_testbit_low 15); auto; try lia
        | rewrite (_set_byte_testbit_high 0 4); auto; try lia;
            rewrite (_set_byte_testbit_high 1 4); auto; try lia;
            rewrite (_set_byte_testbit_high 2 4); auto; try lia;
            rewrite (_set_byte_testbit_high 3 4); auto; try lia;
            rewrite (_set_byte_testbit_low 5); auto; try lia;
            rewrite (_set_byte_testbit_low 6); auto; try lia;
            rewrite (_set_byte_testbit_low 7); auto; try lia;
            rewrite (_set_byte_testbit_low 8); auto; try lia;
            rewrite (_set_byte_testbit_low 9); auto; try lia;
            rewrite (_set_byte_testbit_low 10); auto; try lia;
            rewrite (_set_byte_testbit_low 11); auto; try lia;
            rewrite (_set_byte_testbit_low 12); auto; try lia;
            rewrite (_set_byte_testbit_low 13); auto; try lia;
            rewrite (_set_byte_testbit_low 14); auto; try lia;
            rewrite (_set_byte_testbit_low 15); auto; try lia
        | rewrite (_set_byte_testbit_high 0 5); auto; try lia;
            rewrite (_set_byte_testbit_high 1 5); auto; try lia;
            rewrite (_set_byte_testbit_high 2 5); auto; try lia;
            rewrite (_set_byte_testbit_high 3 5); auto; try lia;
            rewrite (_set_byte_testbit_high 4 5); auto; try lia;
            rewrite (_set_byte_testbit_low 6); auto; try lia;
            rewrite (_set_byte_testbit_low 7); auto; try lia;
            rewrite (_set_byte_testbit_low 8); auto; try lia;
            rewrite (_set_byte_testbit_low 9); auto; try lia;
            rewrite (_set_byte_testbit_low 10); auto; try lia;
            rewrite (_set_byte_testbit_low 11); auto; try lia;
            rewrite (_set_byte_testbit_low 12); auto; try lia;
            rewrite (_set_byte_testbit_low 13); auto; try lia;
            rewrite (_set_byte_testbit_low 14); auto; try lia;
            rewrite (_set_byte_testbit_low 15); auto; try lia
        | rewrite (_set_byte_testbit_high 0 6); auto; try lia;
            rewrite (_set_byte_testbit_high 1 6); auto; try lia;
            rewrite (_set_byte_testbit_high 2 6); auto; try lia;
            rewrite (_set_byte_testbit_high 3 6); auto; try lia;
            rewrite (_set_byte_testbit_high 4 6); auto; try lia;
            rewrite (_set_byte_testbit_high 5 6); auto; try lia;
            rewrite (_set_byte_testbit_low 7); auto; try lia;
            rewrite (_set_byte_testbit_low 8); auto; try lia;
            rewrite (_set_byte_testbit_low 9); auto; try lia;
            rewrite (_set_byte_testbit_low 10); auto; try lia;
            rewrite (_set_byte_testbit_low 11); auto; try lia;
            rewrite (_set_byte_testbit_low 12); auto; try lia;
            rewrite (_set_byte_testbit_low 13); auto; try lia;
            rewrite (_set_byte_testbit_low 14); auto; try lia;
            rewrite (_set_byte_testbit_low 15); auto; try lia
        | rewrite (_set_byte_testbit_high 0 7); auto; try lia;
            rewrite (_set_byte_testbit_high 1 7); auto; try lia;
            rewrite (_set_byte_testbit_high 2 7); auto; try lia;
            rewrite (_set_byte_testbit_high 3 7); auto; try lia;
            rewrite (_set_byte_testbit_high 4 7); auto; try lia;
            rewrite (_set_byte_testbit_high 5 7); auto; try lia;
            rewrite (_set_byte_testbit_high 6 7); auto; try lia;
            rewrite (_set_byte_testbit_low 8); auto; try lia;
            rewrite (_set_byte_testbit_low 9); auto; try lia;
            rewrite (_set_byte_testbit_low 10); auto; try lia;
            rewrite (_set_byte_testbit_low 11); auto; try lia;
            rewrite (_set_byte_testbit_low 12); auto; try lia;
            rewrite (_set_byte_testbit_low 13); auto; try lia;
            rewrite (_set_byte_testbit_low 14); auto; try lia;
            rewrite (_set_byte_testbit_low 15); auto; try lia
        | rewrite (_set_byte_testbit_high 0 8); auto; try lia;
            rewrite (_set_byte_testbit_high 1 8); auto; try lia;
            rewrite (_set_byte_testbit_high 2 8); auto; try lia;
            rewrite (_set_byte_testbit_high 3 8); auto; try lia;
            rewrite (_set_byte_testbit_high 4 8); auto; try lia;
            rewrite (_set_byte_testbit_high 5 8); auto; try lia;
            rewrite (_set_byte_testbit_high 6 8); auto; try lia;
            rewrite (_set_byte_testbit_high 7 8); auto; try lia;
            rewrite (_set_byte_testbit_low 9); auto; try lia;
            rewrite (_set_byte_testbit_low 10); auto; try lia;
            rewrite (_set_byte_testbit_low 11); auto; try lia;
            rewrite (_set_byte_testbit_low 12); auto; try lia;
            rewrite (_set_byte_testbit_low 13); auto; try lia;
            rewrite (_set_byte_testbit_low 14); auto; try lia;
            rewrite (_set_byte_testbit_low 15); auto; try lia
        | rewrite (_set_byte_testbit_high 0 9); auto; try lia;
            rewrite (_set_byte_testbit_high 1 9); auto; try lia;
            rewrite (_set_byte_testbit_high 2 9); auto; try lia;
            rewrite (_set_byte_testbit_high 3 9); auto; try lia;
            rewrite (_set_byte_testbit_high 4 9); auto; try lia;
            rewrite (_set_byte_testbit_high 5 9); auto; try lia;
            rewrite (_set_byte_testbit_high 6 9); auto; try lia;
            rewrite (_set_byte_testbit_high 7 9); auto; try lia;
            rewrite (_set_byte_testbit_high 8 9); auto; try lia;
            rewrite (_set_byte_testbit_low 10); auto; try lia;
            rewrite (_set_byte_testbit_low 11); auto; try lia;
            rewrite (_set_byte_testbit_low 12); auto; try lia;
            rewrite (_set_byte_testbit_low 13); auto; try lia;
            rewrite (_set_byte_testbit_low 14); auto; try lia;
            rewrite (_set_byte_testbit_low 15); auto; try lia
        | rewrite (_set_byte_testbit_high 0 10); auto; try lia;
            rewrite (_set_byte_testbit_high 1 10); auto; try lia;
            rewrite (_set_byte_testbit_high 2 10); auto; try lia;
            rewrite (_set_byte_testbit_high 3 10); auto; try lia;
            rewrite (_set_byte_testbit_high 4 10); auto; try lia;
            rewrite (_set_byte_testbit_high 5 10); auto; try lia;
            rewrite (_set_byte_testbit_high 6 10); auto; try lia;
            rewrite (_set_byte_testbit_high 7 10); auto; try lia;
            rewrite (_set_byte_testbit_high 8 10); auto; try lia;
            rewrite (_set_byte_testbit_high 9 10); auto; try lia;
            rewrite (_set_byte_testbit_low 11); auto; try lia;
            rewrite (_set_byte_testbit_low 12); auto; try lia;
            rewrite (_set_byte_testbit_low 13); auto; try lia;
            rewrite (_set_byte_testbit_low 14); auto; try lia;
            rewrite (_set_byte_testbit_low 15); auto; try lia
        | rewrite (_set_byte_testbit_high 0 11); auto; try lia;
            rewrite (_set_byte_testbit_high 1 11); auto; try lia;
            rewrite (_set_byte_testbit_high 2 11); auto; try lia;
            rewrite (_set_byte_testbit_high 3 11); auto; try lia;
            rewrite (_set_byte_testbit_high 4 11); auto; try lia;
            rewrite (_set_byte_testbit_high 5 11); auto; try lia;
            rewrite (_set_byte_testbit_high 6 11); auto; try lia;
            rewrite (_set_byte_testbit_high 7 11); auto; try lia;
            rewrite (_set_byte_testbit_high 8 11); auto; try lia;
            rewrite (_set_byte_testbit_high 9 11); auto; try lia;
            rewrite (_set_byte_testbit_high 10 11); auto; try lia;
            rewrite (_set_byte_testbit_low 12); auto; try lia;
            rewrite (_set_byte_testbit_low 13); auto; try lia;
            rewrite (_set_byte_testbit_low 14); auto; try lia;
            rewrite (_set_byte_testbit_low 15); auto; try lia
        | rewrite (_set_byte_testbit_high 0 12); auto; try lia;
            rewrite (_set_byte_testbit_high 1 12); auto; try lia;
            rewrite (_set_byte_testbit_high 2 12); auto; try lia;
            rewrite (_set_byte_testbit_high 3 12); auto; try lia;
            rewrite (_set_byte_testbit_high 4 12); auto; try lia;
            rewrite (_set_byte_testbit_high 5 12); auto; try lia;
            rewrite (_set_byte_testbit_high 6 12); auto; try lia;
            rewrite (_set_byte_testbit_high 7 12); auto; try lia;
            rewrite (_set_byte_testbit_high 8 12); auto; try lia;
            rewrite (_set_byte_testbit_high 9 12); auto; try lia;
            rewrite (_set_byte_testbit_high 10 12); auto; try lia;
            rewrite (_set_byte_testbit_high 11 12); auto; try lia;
            rewrite (_set_byte_testbit_low 13); auto; try lia;
            rewrite (_set_byte_testbit_low 14); auto; try lia;
            rewrite (_set_byte_testbit_low 15); auto; try lia
        | rewrite (_set_byte_testbit_high 0 13); auto; try lia;
            rewrite (_set_byte_testbit_high 1 13); auto; try lia;
            rewrite (_set_byte_testbit_high 2 13); auto; try lia;
            rewrite (_set_byte_testbit_high 3 13); auto; try lia;
            rewrite (_set_byte_testbit_high 4 13); auto; try lia;
            rewrite (_set_byte_testbit_high 5 13); auto; try lia;
            rewrite (_set_byte_testbit_high 6 13); auto; try lia;
            rewrite (_set_byte_testbit_high 7 13); auto; try lia;
            rewrite (_set_byte_testbit_high 8 13); auto; try lia;
            rewrite (_set_byte_testbit_high 9 13); auto; try lia;
            rewrite (_set_byte_testbit_high 10 13); auto; try lia;
            rewrite (_set_byte_testbit_high 11 13); auto; try lia;
            rewrite (_set_byte_testbit_high 12 13); auto; try lia;
            rewrite (_set_byte_testbit_low 14); auto; try lia;
            rewrite (_set_byte_testbit_low 15); auto; try lia
        | rewrite (_set_byte_testbit_high 0 14); auto; try lia;
            rewrite (_set_byte_testbit_high 1 14); auto; try lia;
            rewrite (_set_byte_testbit_high 2 14); auto; try lia;
            rewrite (_set_byte_testbit_high 3 14); auto; try lia;
            rewrite (_set_byte_testbit_high 4 14); auto; try lia;
            rewrite (_set_byte_testbit_high 5 14); auto; try lia;
            rewrite (_set_byte_testbit_high 6 14); auto; try lia;
            rewrite (_set_byte_testbit_high 7 14); auto; try lia;
            rewrite (_set_byte_testbit_high 8 14); auto; try lia;
            rewrite (_set_byte_testbit_high 9 14); auto; try lia;
            rewrite (_set_byte_testbit_high 10 14); auto; try lia;
            rewrite (_set_byte_testbit_high 11 14); auto; try lia;
            rewrite (_set_byte_testbit_high 12 14); auto; try lia;
            rewrite (_set_byte_testbit_high 13 14); auto; try lia;
            rewrite (_set_byte_testbit_low 15); auto; try lia
        | rewrite (_set_byte_testbit_high 0 15); auto; try lia;
            rewrite (_set_byte_testbit_high 1 15); auto; try lia;
            rewrite (_set_byte_testbit_high 2 15); auto; try lia;
            rewrite (_set_byte_testbit_high 3 15); auto; try lia;
            rewrite (_set_byte_testbit_high 4 15); auto; try lia;
            rewrite (_set_byte_testbit_high 5 15); auto; try lia;
            rewrite (_set_byte_testbit_high 6 15); auto; try lia;
            rewrite (_set_byte_testbit_high 7 15); auto; try lia;
            rewrite (_set_byte_testbit_high 8 15); auto; try lia;
            rewrite (_set_byte_testbit_high 9 15); auto; try lia;
            rewrite (_set_byte_testbit_high 10 15); auto; try lia;
            rewrite (_set_byte_testbit_high 11 15); auto; try lia;
            rewrite (_set_byte_testbit_high 12 15); auto; try lia;
            rewrite (_set_byte_testbit_high 13 15); auto; try lia;
            rewrite (_set_byte_testbit_high 14 15); auto; try lia
        | rewrite (_set_byte_testbit_high 0 16); auto; try lia;
            rewrite (_set_byte_testbit_high 1 16); auto; try lia;
            rewrite (_set_byte_testbit_high 2 16); auto; try lia;
            rewrite (_set_byte_testbit_high 3 16); auto; try lia;
            rewrite (_set_byte_testbit_high 4 16); auto; try lia;
            rewrite (_set_byte_testbit_high 5 16); auto; try lia;
            rewrite (_set_byte_testbit_high 6 16); auto; try lia;
            rewrite (_set_byte_testbit_high 7 16); auto; try lia;
            rewrite (_set_byte_testbit_high 8 16); auto; try lia;
            rewrite (_set_byte_testbit_high 9 16); auto; try lia;
            rewrite (_set_byte_testbit_high 10 16); auto; try lia;
            rewrite (_set_byte_testbit_high 11 16); auto; try lia;
            rewrite (_set_byte_testbit_high 12 16); auto; try lia;
            rewrite (_set_byte_testbit_high 13 16); auto; try lia;
            rewrite (_set_byte_testbit_high 14 16); auto; try lia;
            rewrite (_set_byte_testbit_high 15 16); auto; try lia;
            apply Z.testbit_false; [by lia |];
            rewrite Z.div_small; [apply Z.mod_0_l; lia |];
            pose proof (Z.pow_le_mono_r 2 128 n ltac:(lia) ltac:(auto)); lia
        ]; rewrite ?orb_false_l ?orb_false_r;
        repeat (rewrite ?Z.lor_spec ?Z.shiftl_spec ?Z.land_spec ?Z.shiftr_spec; try lia);
        rewrite !Z.testbit_ones; try lia;
        churn_bits'; now rewrite Z.sub_add.
    Qed.
  End split.
End Byte.

#[global] Opaque _get_byte _set_byte.

Section Bswap.
  #[local] Definition bswap_idxs (bytes: nat) :=
    let idxs := seq 0 bytes in
    zip idxs (rev idxs).

  #[local] Definition bswap_ (bytes: nat) (n: Z): Z :=
    fold_left (fun acc '(getIdx, setIdx) =>
                 Z.lor acc (_set_byte (_get_byte n getIdx) setIdx))
              (bswap_idxs bytes)
              0.

  Definition bswap (sz : bitsize) : Z -> Z := bswap_ (bitsize.bytesNat sz).

  Section test.
    Local Definition bytes (ls : list Z) :=
      fold_left (fun a b => a * 256 + b)%Z ls 0%Z.
    Arguments bytes _%_Z.

    Local Definition _bswap16_test : bswap bitsize.W16 (bytes (1::2::nil)%Z) = bytes (2::1::nil)%Z := eq_refl.
    Local Definition _bswap32_test :
      bswap bitsize.W32 (bytes (1::2::3::4::nil)%Z) = bytes (4::3::2::1::nil)%Z := eq_refl.
    Local Definition _bswap64_test :
      bswap bitsize.W64 (bytes (1::2::3::4::5::6::7::8::nil)%Z) = bytes (8::7::6::5::4::3::2::1::nil)%Z := eq_refl.
  End test.
End Bswap.

Notation bswap8 := (bswap bitsize.W8) (only parsing).
Notation bswap16 := (bswap bitsize.W16) (only parsing).
Notation bswap32 := (bswap bitsize.W32) (only parsing).
Notation bswap64 := (bswap bitsize.W64) (only parsing).
Notation bswap128 := (bswap bitsize.W128) (only parsing).

#[global] Opaque bswap.

Section Bswap.
  Section Theory.
    Section bounded.
      #[local] Transparent bswap.

      Lemma bswap8_bounded:
        forall v,
          0 <= bswap8 v < 256.
      Proof.
        intros *; rewrite /bswap/bswap_/= Z.lor_0_l.
        pose proof (_set_byte_bound (_get_byte v 0) 0).
        lia.
      Qed.

      Lemma bswap16_bounded:
        ∀ v,
         0 ≤ bswap16 v < 65536.
      Proof.
        intros *; rewrite /bswap/bswap_/= Z.lor_0_l.
        pose proof (_set_byte_bound (_get_byte v 0) 1).
        pose proof (_set_byte_bound (_get_byte v 1) 0).
        repeat (try apply ZlorRange with (w:=16%N)); lia.
      Qed.

      Lemma bswap32_bounded:
        forall v,
          0 ≤ bswap32 v < 4294967296.
      Proof.
        intros *; rewrite /bswap/bswap_/= Z.lor_0_l.
        pose proof (_set_byte_bound (_get_byte v 0) 3).
        pose proof (_set_byte_bound (_get_byte v 1) 2).
        pose proof (_set_byte_bound (_get_byte v 2) 1).
        pose proof (_set_byte_bound (_get_byte v 3) 0).
        repeat (try apply ZlorRange with (w:=32%N)); lia.
      Qed.

      Lemma bswap64_bounded:
        forall v,
          0 ≤ bswap64 v < 18446744073709551616.
      Proof.
        intros *; rewrite /bswap/bswap_/= Z.lor_0_l.
        pose proof (_set_byte_bound (_get_byte v 0) 7).
        pose proof (_set_byte_bound (_get_byte v 1) 6).
        pose proof (_set_byte_bound (_get_byte v 2) 5).
        pose proof (_set_byte_bound (_get_byte v 3) 4).
        pose proof (_set_byte_bound (_get_byte v 4) 3).
        pose proof (_set_byte_bound (_get_byte v 5) 2).
        pose proof (_set_byte_bound (_get_byte v 6) 1).
        pose proof (_set_byte_bound (_get_byte v 7) 0).
        repeat (try apply ZlorRange with (w:=64%N)); lia.
      Qed.

      Lemma bswap128_bounded:
        forall v,
          0 ≤ bswap128 v < ltac:(let x := eval cbv in (2^128) in exact x).
      Proof.
        intros *; rewrite /bswap/bswap_/= Z.lor_0_l.
        pose proof (_set_byte_bound (_get_byte v 0) 15).
        pose proof (_set_byte_bound (_get_byte v 1) 14).
        pose proof (_set_byte_bound (_get_byte v 2) 13).
        pose proof (_set_byte_bound (_get_byte v 3) 12).
        pose proof (_set_byte_bound (_get_byte v 4) 11).
        pose proof (_set_byte_bound (_get_byte v 5) 10).
        pose proof (_set_byte_bound (_get_byte v 6) 9).
        pose proof (_set_byte_bound (_get_byte v 7) 8).
        pose proof (_set_byte_bound (_get_byte v 8) 7).
        pose proof (_set_byte_bound (_get_byte v 9) 6).
        pose proof (_set_byte_bound (_get_byte v 10) 5).
        pose proof (_set_byte_bound (_get_byte v 11) 4).
        pose proof (_set_byte_bound (_get_byte v 12) 3).
        pose proof (_set_byte_bound (_get_byte v 13) 2).
        pose proof (_set_byte_bound (_get_byte v 14) 1).
        pose proof (_set_byte_bound (_get_byte v 15) 0).
        repeat (try apply ZlorRange with (w:=128%N)); lia.
      Qed.
    End bounded.

    Lemma bswap_bounded:
      forall sz v,
        0 <= bswap sz v < 2^(bitsize.bitsZ sz).
    Proof.
      intros *; destruct sz;
        eauto using
              bswap8_bounded,
              bswap16_bounded,
              bswap32_bounded,
              bswap64_bounded,
              bswap128_bounded.
    Qed.
  End Theory.
End Bswap.

Section Bswap.
  Section Theory.
    Section useless_lor.
      #[local] Transparent _get_byte _set_byte bswap.

      Lemma bswap8_useless_lor:
        forall v v' idx,
          (idx >= 1)%nat ->
          bswap8 (Z.lor v (_set_byte v' idx)) =
          bswap8 v.
      Proof.
        move=> v v' idx Hidx.
        rewrite /bswap8/bswap/bswap_/_get_byte/=; f_equal.
        rewrite /_set_byte; churn_bits.
      Qed.

      Lemma bswap16_useless_lor:
        forall v v' idx,
          (idx >= 2)%nat ->
          bswap16 (Z.lor v (_set_byte v' idx)) =
          bswap16 v.
      Proof.
        move=> v v' idx Hidx.
        rewrite /bswap16/bswap/bswap_/_get_byte/=.
        do 1 (f_equal; [| f_equal; rewrite /_set_byte; churn_bits]).
        f_equal; f_equal; rewrite /_set_byte; churn_bits.
      Qed.

      Lemma bswap32_useless_lor:
        forall v v' idx,
          (idx >= 4)%nat ->
          bswap32 (Z.lor v (_set_byte v' idx)) =
          bswap32 v.
      Proof.
        move=> v v' idx Hidx.
        rewrite /bswap32/bswap/bswap_/_get_byte/=.
        do 3 (f_equal; [| f_equal; rewrite /_set_byte; churn_bits]).
        f_equal; f_equal; rewrite /_set_byte; churn_bits.
      Qed.

      Lemma bswap64_useless_lor:
        forall v v' idx,
          (idx >= 8)%nat ->
          bswap64 (Z.lor v (_set_byte v' idx)) =
          bswap64 v.
      Proof.
        move=> v v' idx Hidx.
        rewrite /bswap64/bswap/bswap_/_get_byte/=.
        do 7 (f_equal; [| f_equal; rewrite /_set_byte; churn_bits]).
        f_equal; f_equal; rewrite /_set_byte; churn_bits.
      Qed.

      Lemma bswap128_useless_lor:
        forall v v' idx,
          (idx >= 16)%nat ->
          bswap128 (Z.lor v (_set_byte v' idx)) =
          bswap128 v.
      Proof.
        move=> v v' idx Hidx.
        rewrite /bswap128/bswap/bswap_/_get_byte/=.
        do 15 (f_equal; [| f_equal; rewrite /_set_byte; churn_bits]).
        f_equal; f_equal; rewrite /_set_byte; churn_bits.
      Qed.
    End useless_lor.

    Lemma bswap_useless_lor:
      forall sz v v' idx,
        (bitsize.bytesNat sz <= idx)%nat ->
        bswap sz (Z.lor v (_set_byte v' idx)) =
        bswap sz v.
    Proof.
      intros [] v v' idx Hidx; simpl in *;
        eauto using
              bswap8_useless_lor,
              bswap16_useless_lor,
              bswap32_useless_lor,
              bswap64_useless_lor,
              bswap128_useless_lor.
    Qed.

    Section _set_byte_reverse.
      #[local] Transparent _get_byte _set_byte bswap.

      Lemma bswap8_set_byte_reverse:
        forall x,
          bswap8 (_set_byte x 0) =
          _set_byte x 0.
      Proof.
        intros *.
        rewrite /bswap8/bswap/bswap_/=.
        rewrite !_set_get_byte_roundtrip !Z.shiftl_0_r !Z.lor_0_l.
        rewrite _get_set_byte_roundtrip; now apply _get_0_set_0_eq.
      Qed.

      Lemma bswap16_set_byte_reverse:
        forall x1 x2,
          bswap16 (Z.lor (_set_byte x1 0)
                         (_set_byte x2 1)) =
          Z.lor (_set_byte x2 0)
                (_set_byte x1 1).
      Proof.
        intros *.
        rewrite /bswap16/bswap/bswap_/=.
        rewrite {1}Z.lor_comm; f_equal;
          try (rewrite !_get_byte_lor !_set_byte_lor
                       !_get_set_byte_roundtrip !_get_set_byte_no_overlap
                       ?_set_byte_0 ?Z.lor_0_r ?Z.lor_0_l ?_set_get_0 //).
      Qed.

      Lemma bswap32_set_byte_reverse:
        forall x1 x2 x3 x4,
          bswap32 (Z.lor (_set_byte x1 0)
                   (Z.lor (_set_byte x2 1)
                    (Z.lor (_set_byte x3 2)
                           (_set_byte x4 3)))) =
          Z.lor (_set_byte x4 0)
          (Z.lor (_set_byte x3 1)
           (Z.lor (_set_byte x2 2)
                  (_set_byte x1 3))).
      Proof.
        intros *.
        rewrite /bswap32/bswap/bswap_/=.
        rewrite {1}Z.lor_comm; f_equal;
          try (rewrite !_get_byte_lor !_set_byte_lor
                       !_get_set_byte_roundtrip !_get_set_byte_no_overlap
                       ?_set_byte_0 ?Z.lor_0_r ?Z.lor_0_l ?_set_get_0 //);
          repeat (rewrite {1}Z.lor_comm; f_equal).
      Qed.

      Lemma bswap64_set_byte_reverse:
        forall x1 x2 x3 x4 x5 x6 x7 x8,
          bswap64 (Z.lor (_set_byte x1 0)
                   (Z.lor (_set_byte x2 1)
                    (Z.lor (_set_byte x3 2)
                     (Z.lor (_set_byte x4 3)
                      (Z.lor (_set_byte x5 4)
                       (Z.lor (_set_byte x6 5)
                        (Z.lor (_set_byte x7 6)
                               (_set_byte x8 7)))))))) =
          Z.lor (_set_byte x8 0)
          (Z.lor (_set_byte x7 1)
           (Z.lor (_set_byte x6 2)
            (Z.lor (_set_byte x5 3)
             (Z.lor (_set_byte x4 4)
              (Z.lor (_set_byte x3 5)
               (Z.lor (_set_byte x2 6)
                      (_set_byte x1 7))))))).
      Proof.
        intros *.
        rewrite /bswap64/bswap/bswap_/=.
        repeat (rewrite {1}Z.lor_comm; f_equal;
                [now (rewrite !_get_byte_lor !_set_byte_lor
                              !_get_set_byte_roundtrip !_get_set_byte_no_overlap
                              ?_set_byte_0 ?Z.lor_0_r ?Z.lor_0_l ?_set_get_0 //) |]).
        rewrite !_get_byte_lor !_set_byte_lor
                !_get_set_byte_roundtrip !_get_set_byte_no_overlap
                ?_set_byte_0 ?Z.lor_0_r ?Z.lor_0_l ?_set_get_0 //.
      Qed.

      Lemma bswap128_set_byte_reverse:
        forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16,
          bswap128 (Z.lor (_set_byte x1 0)
                    (Z.lor (_set_byte x2 1)
                     (Z.lor (_set_byte x3 2)
                      (Z.lor (_set_byte x4 3)
                       (Z.lor (_set_byte x5 4)
                        (Z.lor (_set_byte x6 5)
                         (Z.lor (_set_byte x7 6)
                          (Z.lor (_set_byte x8 7)
                           (Z.lor (_set_byte x9 8)
                            (Z.lor (_set_byte x10 9)
                             (Z.lor (_set_byte x11 10)
                              (Z.lor (_set_byte x12 11)
                               (Z.lor (_set_byte x13 12)
                                (Z.lor (_set_byte x14 13)
                                 (Z.lor (_set_byte x15 14)
                                        (_set_byte x16 15)))))))))))))))) =
          Z.lor (_set_byte x16 0)
           (Z.lor (_set_byte x15 1)
            (Z.lor (_set_byte x14 2)
             (Z.lor (_set_byte x13 3)
              (Z.lor (_set_byte x12 4)
               (Z.lor (_set_byte x11 5)
                (Z.lor (_set_byte x10 6)
                 (Z.lor (_set_byte x9 7)
                  (Z.lor (_set_byte x8 8)
                   (Z.lor (_set_byte x7 9)
                    (Z.lor (_set_byte x6 10)
                     (Z.lor (_set_byte x5 11)
                      (Z.lor (_set_byte x4 12)
                       (Z.lor (_set_byte x3 13)
                        (Z.lor (_set_byte x2 14)
                               (_set_byte x1 15))))))))))))))).
      Proof.
        intros *.
        rewrite /bswap128/bswap/bswap_/=.
        repeat (rewrite {1}Z.lor_comm; f_equal;
                [now (rewrite !_get_byte_lor !_set_byte_lor
                              !_get_set_byte_roundtrip !_get_set_byte_no_overlap
                              ?_set_byte_0 ?Z.lor_0_r ?Z.lor_0_l ?_set_get_0 //) |]).
        rewrite !_get_byte_lor !_set_byte_lor
                !_get_set_byte_roundtrip !_get_set_byte_no_overlap
                ?_set_byte_0 ?Z.lor_0_r ?Z.lor_0_l ?_set_get_0 //.
      Qed.
    End _set_byte_reverse.

    Section larger.
      #[local] Transparent _get_byte _set_byte bswap.

      Lemma bswap8_larger z:
        0 <= z ->
        bswap8 z = bswap8 (Z.land z (Z.ones 8)).
      Proof.
        intros; rewrite /bswap8/bswap/bswap_/= ?Z.lor_0_l ?Z.lor_0_r.
        f_equal; rewrite /_get_byte; churn_bits.
      Qed.

      Lemma bswap16_larger z:
        0 <= z ->
        bswap16 z = bswap16 (Z.land z (Z.ones 16)).
      Proof.
        intros; rewrite /bswap16/bswap/bswap_/= ?Z.lor_0_l ?Z.lor_0_r.
        do 1 (f_equal; [| f_equal; rewrite /_get_byte; churn_bits]).
        f_equal; rewrite /_get_byte; churn_bits.
      Qed.

      Lemma bswap32_larger z:
        0 <= z ->
        bswap32 z = bswap32 (Z.land z (Z.ones 32)).
      Proof.
        intros; rewrite /bswap32/bswap/bswap_/= ?Z.lor_0_l ?Z.lor_0_r.
        do 3 (f_equal; [| f_equal; rewrite /_get_byte; churn_bits]).
        f_equal; rewrite /_get_byte; churn_bits.
      Qed.

      Lemma bswap64_larger z:
        0 <= z ->
        bswap64 z = bswap64 (Z.land z (Z.ones 64)).
      Proof.
        intros; rewrite /bswap64/bswap/bswap_/= ?Z.lor_0_l ?Z.lor_0_r.
        do 7 (f_equal; [| f_equal; rewrite /_get_byte; churn_bits]).
        f_equal; rewrite /_get_byte; churn_bits.
      Qed.

      Lemma bswap128_larger z:
        0 <= z ->
        bswap128 z = bswap128 (Z.land z (Z.ones 128)).
      Proof.
        intros; rewrite /bswap128/bswap/bswap_/= ?Z.lor_0_l ?Z.lor_0_r.
        do 15 (f_equal; [| f_equal; rewrite /_get_byte; churn_bits]).
        f_equal; rewrite /_get_byte; churn_bits.
      Qed.
    End larger.

    Lemma bswap_larger sz z:
      0 <= z ->
      bswap sz z = bswap sz (Z.land z (Z.ones (bitsize.bitsZ sz))).
    Proof.
      intros; destruct sz;
        eauto using
              bswap8_larger,
              bswap16_larger,
              bswap32_larger,
              bswap64_larger,
              bswap128_larger.
    Qed.

    Section involutive.
      Lemma bswap8_involutive:
        forall z,
          0 <= z < 2^bitsize.bitsZ bitsize.W8 ->
          bswap8 (bswap8 z) = z.
      Proof.
        intros * Hbounds.
        rewrite (split8 z); auto.
        now rewrite 2!bswap8_set_byte_reverse.
      Qed.

      Lemma bswap8_involutive_land:
        forall z,
          0 <= z < 2^bitsize.bitsZ bitsize.W8 ->
          bswap8 (bswap8 z) = Z.land z (Z.ones (bitsize.bitsZ bitsize.W8)).
      Proof.
        intros * Hbounds; simpl in *.
        rewrite bswap8_involutive; auto.
        rewrite -> Z.land_ones by lia.
        rewrite Z.mod_small; auto.
      Qed.

      Lemma bswap16_involutive:
        forall z,
          0 <= z < 2^bitsize.bitsZ bitsize.W16 ->
          bswap16 (bswap16 z) = z.
      Proof.
        intros * Hbounds.
        rewrite (split16 z); auto.
        now rewrite 2!bswap16_set_byte_reverse.
      Qed.

      Lemma bswap16_involutive_land:
        forall z,
          0 <= z < 2^bitsize.bitsZ bitsize.W16 ->
          bswap16 (bswap16 z) = Z.land z (Z.ones (bitsize.bitsZ bitsize.W16)).
      Proof.
        intros * Hbounds; simpl in *.
        rewrite bswap16_involutive; auto.
        rewrite -> Z.land_ones by lia.
        rewrite Z.mod_small; auto.
      Qed.

      Lemma bswap32_involutive:
        forall z,
          0 <= z < 2^bitsize.bitsZ bitsize.W32 ->
          bswap32 (bswap32 z) = z.
      Proof.
        intros * Hbounds.
        rewrite (split32 z); auto.
        now rewrite 2!bswap32_set_byte_reverse.
      Qed.

      Lemma bswap32_involutive_land:
        forall z,
          0 <= z < 2^bitsize.bitsZ bitsize.W32 ->
          bswap32 (bswap32 z) = Z.land z (Z.ones (bitsize.bitsZ bitsize.W32)).
      Proof.
        intros * Hbounds; simpl in *.
        rewrite bswap32_involutive; auto.
        rewrite -> Z.land_ones by lia.
        rewrite Z.mod_small; auto.
      Qed.

      Lemma bswap64_involutive:
        forall z,
          0 <= z < 2^bitsize.bitsZ bitsize.W64 ->
          bswap64 (bswap64 z) = z.
      Proof.
        intros * Hbounds.
        rewrite (split64 z); auto.
        now rewrite 2!bswap64_set_byte_reverse.
      Qed.

      Lemma bswap64_involutive_land:
        forall z,
          0 <= z < 2^bitsize.bitsZ bitsize.W64 ->
          bswap64 (bswap64 z) = Z.land z (Z.ones (bitsize.bitsZ bitsize.W64)).
      Proof.
        intros * Hbounds; simpl in *.
        rewrite bswap64_involutive; auto.
        rewrite -> Z.land_ones by lia.
        rewrite Z.mod_small; auto.
      Qed.

      Lemma bswap128_involutive:
        forall z,
          0 <= z < 2^bitsize.bitsZ bitsize.W128 ->
          bswap128 (bswap128 z) = z.
      Proof.
        intros * Hbounds.
        rewrite (split128 z); auto.
        now rewrite 2!bswap128_set_byte_reverse.
      Qed.

      Lemma bswap128_involutive_land:
        forall z,
          0 <= z < 2^bitsize.bitsZ bitsize.W128 ->
          bswap128 (bswap128 z) = Z.land z (Z.ones (bitsize.bitsZ bitsize.W128)).
      Proof.
        intros * Hbounds; simpl in *.
        rewrite bswap128_involutive; auto.
        rewrite -> Z.land_ones by lia.
        rewrite Z.mod_small; auto.
      Qed.
    End involutive.

    Lemma bswap_involutive:
      forall sz z,
        0 <= z < 2^bitsize.bitsZ sz ->
        bswap sz (bswap sz z) = z.
    Proof.
      intros * Hbounds; destruct sz;
        eauto using
              bswap8_involutive,
              bswap16_involutive,
              bswap32_involutive,
              bswap64_involutive,
              bswap128_involutive.
    Qed.

    Lemma bswap_involutive_land:
      forall sz z,
        0 <= z < 2^bitsize.bitsZ sz ->
        bswap sz (bswap sz z) = Z.land z (Z.ones (bitsize.bitsZ sz)).
    Proof.
      intros * Hbounds; destruct sz;
        eauto using
              bswap8_involutive_land,
              bswap16_involutive_land,
              bswap32_involutive_land,
              bswap64_involutive_land,
              bswap128_involutive_land.
    Qed.
  End Theory.
End Bswap.
