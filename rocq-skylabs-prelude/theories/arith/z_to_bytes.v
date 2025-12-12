(*
 * Copyright (c) 2020-2025 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bluerock.prelude.base.
Require Import bluerock.prelude.list_numbers.
Require Import bluerock.prelude.arith.types.
Require Import bluerock.prelude.arith.builtins.
Require Import bluerock.prelude.arith.operator.

Import arith.builtins.churn_bits.

Section FromToBytes.
  Section ExtraFacts.
    Lemma repeat_cons_app:
      forall (A: Type) (a: A) (cnt: nat),
        (a :: repeat a cnt) = repeat a cnt ++ [a].
    Proof.
      induction cnt => //=.
      by rewrite IHcnt.
    Qed.

    Lemma rev_repeat:
      forall (A: Type) (a: A) (cnt: nat),
        rev (repeat a cnt) = repeat a cnt.
    Proof.
      induction cnt => //=.
      by rewrite IHcnt repeat_cons_app.
    Qed.

    Lemma Z_shiftr_small:
      forall v e,
        (0 <= e)%Z ->
        (0 <= v)%Z ->
        (v < 2 ^ e)%Z ->
        (v ≫ e = 0)%Z.
    Proof.
      intros; rewrite Z.shiftr_div_pow2; try lia.
      rewrite Z.div_small; lia.
    Qed.

    Lemma Z_pow2_trans_nat_l:
      forall v (a b: nat),
        (v < 2 ^ (8 * b))%Z ->
        (v < 2 ^ (8 * (a + b)%nat))%Z.
    Proof.
      intros; destruct a.
      - by replace (8 * (0%nat + b))%Z with (8 * b)%Z by lia.
      - eapply Z.lt_trans; eauto; apply Z.pow_lt_mono_r; lia.
    Qed.

    Lemma Z_pow2_trans_nat_r:
      forall v (a b: nat),
        (v < 2 ^ (8 * a))%Z ->
        (v < 2 ^ (8 * (a + b)%nat))%Z.
    Proof.
      intros; destruct b.
      - by rewrite -plus_n_O.
      - eapply Z.lt_trans; eauto; apply Z.pow_lt_mono_r; lia.
    Qed.

    Lemma Z_land_ldiff_no_overlap (mask offset v: Z) :
        (0 < mask)%Z ->
        (0 <= offset)%Z ->
        (0 <= v)%Z ->
        Z.land (mask ≪ offset) (Z.ldiff v (Z.ones offset)) = Z.land (mask ≪ offset) v.
    Proof.
    (* Intuition: the ldiff is going to remove the lowest
         (idx+cnt) bytes, but the `255 ≪ (8 * (idx+cnt))`
         mask doesn't overlap with any of those bits
         so it is effectively a no-op.
     *)
      intros **.
      apply Z.bits_inj' => n ?.
      rewrite !Z.land_spec Z.ldiff_spec Z.shiftl_spec // Z.testbit_ones_nonneg; try lia.
      destruct (n <? offset)%Z eqn:Hn => /=; rewrite ?andb_true_r //.
      move: Hn => /Z.ltb_lt?.
      rewrite !andb_false_r Z.testbit_neg_r //. lia.
    Qed.

    Lemma Z_land_ldiff_upper_byte (offset v: Z) :
        (0 <= offset)%Z ->
        (2^(8*offset) <= v)%Z ->
        (v < 2^(8*Z.succ offset))%Z ->
        Z.ldiff v (Z.ones (8 * offset)) = Z.land (255 ≪ (8 * offset)) v.
    Proof.
    (* Intuition: since `v < 2^(8*(idx+S cnt))`, we know
         that there aren't going to be any bits
         beyond the `255 ≪ (8 * (idx+cnt))` mask
         which will be introduced by the change to ldiff.
     *)
      intros.
      apply Z.bits_inj' => n ?.
      rewrite !Z.land_spec Z.ldiff_spec Z.shiftl_spec // Z.testbit_ones_nonneg; try lia.
      destruct (n <? 8*offset)%Z eqn:Hn => //=; rewrite ?andb_true_r ?andb_false_r //.
      - apply Z.ltb_lt in Hn; rewrite Z.testbit_neg_r ?andb_false_l //=; lia.
      - apply Z.ltb_ge in Hn.
        replace (8 * Z.succ offset)%Z with (8 + (8 * offset))%Z in H1 by lia.
        change (255)%Z with (Z.ones 8).
        destruct (8 + (8 * offset) <? n)%Z eqn:Hn' => //=.
        + rewrite Z.bits_above_log2 ?andb_false_r //.
          * apply Z.le_trans with (m := (2^(8*offset))%Z); try apply Z.pow_nonneg; lia.
          * apply Z.log2_lt_pow2.
            -- eapply Z.lt_le_trans; eauto; apply Z.pow_pos_nonneg; lia.
            -- eapply Z.lt_trans; eauto.
               apply Z.ltb_lt in Hn'.
               apply Z.pow_lt_mono_r; try lia.
        + apply Z.ltb_ge in Hn'.
          destruct (8 + (8 * offset) =? n)%Z eqn:Hn'' => //=.
          * apply Z.eqb_eq in Hn''; subst.
            rewrite Z.bits_above_log2 ?andb_false_l ?andb_false_r //.
            -- apply Z.le_trans with (m := (2^(8*offset))%Z);
                 eauto; apply Z.pow_nonneg; lia.
            -- apply Z.log2_lt_pow2; lia.
          * apply Z.eqb_neq in Hn''.
            assert (n < 8 + 8 * offset)%Z as Hn''' by lia.
            rewrite Z.ones_spec_low ?andb_true_l //; lia.
    Qed.

    Lemma Z_ldiff_split:
      forall (cnt idx: nat) (v: Z),
        (0 <= v)%Z ->
        (v < 2^(8*(idx+S cnt)))%Z ->
        Z.ldiff v (Z.ones (8 * idx)) =
        Z.lor (Z.land (Z.ones (8 * cnt) ≪ (8 * idx)) v)
              (Z.land (Z.ones 8 ≪ (8 * (idx + cnt)%nat)) v).
    Proof.
      intros cnt idx v Hlower Hupper.
      assert (v = 0 \/ 0 < v)%Z as [Hlower' | Hlower'] by lia;
        [subst; by rewrite !Z.land_0_r Z.lor_diag Z.ldiff_0_l | clear Hlower].
      apply Z.bits_inj'=> n ?.
      rewrite Z.lor_spec Z.ldiff_spec !Z.land_spec !Z.shiftl_spec; try lia.
      rewrite !Z.testbit_ones; try lia.
      churn_bits'.
      apply Z.bits_above_log2; try lia.
      assert (8 * (idx+S cnt)%nat <= n)%Z by lia.
      eapply Z.lt_le_trans; eauto.
      apply Z.log2_lt_pow2; try lia.
    Qed.
  End ExtraFacts.

  Section ToBytes_internal.
    Definition _Z_to_bytes_unsigned_le' (idx: nat) (cnt: nat) (v: Z): list N :=
      map (Z.to_N ∘ _get_byte v) $ seq idx cnt.

    Definition _Z_to_bytes_unsigned_le (cnt: nat) (v: Z): list N :=
      _Z_to_bytes_unsigned_le' 0 cnt v.

    Definition _Z_to_bytes_le (cnt: nat) (sgn: signed) (v: Z): list N :=
      _Z_to_bytes_unsigned_le
        cnt (match sgn with
             | Signed   => to_unsigned_bits (8 * N.of_nat cnt) v
             | Unsigned => v
             end).

    (* NOTE: This will be sealed once we finish the proofs for this section. *)
    Definition _Z_to_bytes_def (cnt: nat) (endianness: endian) (sgn: signed) (v: Z): list N :=
      let little := _Z_to_bytes_le cnt sgn v in
      match endianness with
      | Little => little
      | Big => List.rev little
      end.
  End ToBytes_internal.

  Section ToBytesFacts_internal.
    #[local] Transparent _get_byte _set_byte.

    Lemma _Z_to_bytes_unsigned_le'_length:
      forall idx cnt v,
        length (_Z_to_bytes_unsigned_le' idx cnt v) = cnt.
    Proof.
      rewrite /_Z_to_bytes_unsigned_le' => idx cnt v //=;
        by rewrite length_map length_seq.
    Qed.

    Definition _Z_to_bytes_unsigned_le_length:
      forall cnt v,
        length (_Z_to_bytes_unsigned_le cnt v) = cnt.
    Proof.
      rewrite /_Z_to_bytes_unsigned_le => * //=;
        by apply _Z_to_bytes_unsigned_le'_length.
    Qed.

    Lemma _Z_to_bytes_le_length:
      forall cnt sgn v,
        length (_Z_to_bytes_le cnt sgn v) = cnt.
    Proof.
      rewrite /_Z_to_bytes_le => * //=;
        by apply _Z_to_bytes_unsigned_le_length.
    Qed.

    Lemma _Z_to_bytes_def_length:
      forall cnt endianness sgn v,
        length (_Z_to_bytes_def cnt endianness sgn v) = cnt.
    Proof.
      rewrite /_Z_to_bytes_def => cnt [ | ] sgn v //=;
        try rewrite length_rev;
        by apply _Z_to_bytes_le_length.
    Qed.

    Lemma _Z_to_bytes_unsigned_le'_0_bytes:
      forall (idx: nat) (v: Z),
        _Z_to_bytes_unsigned_le' idx 0 v = [].
    Proof. done. Qed.

    Lemma _Z_to_bytes_unsigned_le_0_bytes:
      forall (v: Z),
        _Z_to_bytes_unsigned_le 0 v = [].
    Proof. apply (_Z_to_bytes_unsigned_le'_0_bytes 0). Qed.

    Lemma _Z_to_bytes_le_0_bytes:
      forall sgn (v: Z),
        _Z_to_bytes_le 0 sgn v = [].
    Proof.
      move=> [ | ] v; rewrite /_Z_to_bytes_le;
        [rewrite N.mul_0_r trim_0_l | ];
        apply _Z_to_bytes_unsigned_le_0_bytes.
    Qed.

    Lemma _Z_to_bytes_def_0_bytes:
      forall endianness sgn (v: Z),
        _Z_to_bytes_def 0 endianness sgn v = [].
    Proof.
      move=> [ | ] sgn v;
        by rewrite /_Z_to_bytes_def _Z_to_bytes_le_0_bytes //=.
    Qed.

    Lemma _Z_to_bytes_unsigned_le'_0_value:
      forall (idx cnt: nat),
        _Z_to_bytes_unsigned_le' idx cnt 0 = repeat 0%N cnt.
    Proof.
      induction cnt => //=.
      rewrite /_Z_to_bytes_unsigned_le'.
      rewrite seq_S map_app repeat_cons_app //=.
      rewrite _get_byte_0; f_equal=> //=.
    Qed.

    Lemma _Z_to_bytes_unsigned_le_0_value:
      forall (cnt: nat),
        _Z_to_bytes_unsigned_le cnt 0 = repeat 0%N cnt.
    Proof. apply _Z_to_bytes_unsigned_le'_0_value. Qed.

    Lemma _Z_to_bytes_le_0_value:
      forall (cnt: nat) sgn,
        _Z_to_bytes_le cnt sgn 0 = repeat 0%N cnt.
    Proof.
      move=> cnt [ | ]; rewrite /_Z_to_bytes_le;
        [rewrite trim_0_r | ];
        apply _Z_to_bytes_unsigned_le_0_value.
    Qed.

    Lemma _Z_to_bytes_def_0_value:
      forall sgn endianness (cnt: nat),
        _Z_to_bytes_def cnt endianness sgn 0 = repeat 0%N cnt.
    Proof.
      move=> sgn [ | ] cnt;
        rewrite /_Z_to_bytes_def
                _Z_to_bytes_le_0_value //=;
        by rewrite rev_repeat.
    Qed.

    Lemma _Z_to_bytes_unsigned_le'_S_cnt:
      forall (idx cnt: nat) (v: Z),
        _Z_to_bytes_unsigned_le' idx (S cnt) v =
        _Z_to_bytes_unsigned_le' idx cnt v ++
        _Z_to_bytes_unsigned_le' (idx+cnt) 1 v.
    Proof.
      intros; generalize dependent idx;
        induction cnt; intros=> //=.
      - by rewrite Nat.add_0_r.
      - rewrite /_Z_to_bytes_unsigned_le'.
        rewrite seq_S map_app //=.
    Qed.

    Lemma _Z_to_bytes_unsigned_le_S_cnt:
      forall (cnt: nat) (v: Z),
        _Z_to_bytes_unsigned_le (S cnt) v =
        _Z_to_bytes_unsigned_le' 0 cnt v ++
        _Z_to_bytes_unsigned_le' cnt 1 v.
    Proof. apply _Z_to_bytes_unsigned_le'_S_cnt. Qed.

    Lemma _Z_to_bytes_unsigned_le'_small:
      forall (idx cnt: nat) (v: Z),
        (0 <= v)%Z ->
        (v < 2^(8*idx))%Z ->
        _Z_to_bytes_unsigned_le' idx cnt v =
        repeat 0%N cnt.
    Proof.
      intros; generalize dependent idx;
        induction cnt ; intros=> //=.
      rewrite _Z_to_bytes_unsigned_le'_S_cnt
              /_Z_to_bytes_unsigned_le'
              repeat_cons_app //=; f_equal.
      - erewrite <- IHcnt; eauto.
      - rewrite /_get_byte Z_shiftr_small; try lia;
          [ rewrite Z.land_0_l
          | apply Z_pow2_trans_nat_r]=> //=.
    Qed.

    Lemma _Z_to_bytes_unsigned_le'_shrink_cnt:
      forall (idx cnt cnt': nat) (v: Z),
        (0 <= v)%Z ->
        (v < 2^(8*cnt))%Z ->
        cnt < cnt' ->
        _Z_to_bytes_unsigned_le' idx cnt' v =
        _Z_to_bytes_unsigned_le' idx cnt v ++ repeat 0%N (cnt' - cnt).
    Proof.
      intros; generalize dependent idx; generalize dependent cnt;
        induction cnt'; intros=> //=; [lia | ].
      replace (S cnt' - cnt) with (S (cnt' - cnt)) by lia; simpl.
      assert (cnt = cnt' \/ cnt < cnt') as [Hcnt | Hcnt] by lia.
      - subst; rewrite _Z_to_bytes_unsigned_le'_S_cnt; f_equal.
        rewrite Nat.sub_diag /_Z_to_bytes_unsigned_le' //=.
        rewrite /_get_byte Z_shiftr_small; try lia;
          [ rewrite Z.land_0_l
          | apply Z_pow2_trans_nat_l]=> //=.
      - rewrite repeat_cons_app app_assoc.
        rewrite -IHcnt'; try lia.
        rewrite _Z_to_bytes_unsigned_le'_S_cnt //=; f_equal.
        rewrite /_Z_to_bytes_unsigned_le' //=.
        rewrite /_get_byte Z_shiftr_small; try lia;
          [ rewrite Z.land_0_l
          | eapply Z.lt_trans; eauto; apply Z.pow_lt_mono_r; lia]=> //=.
    Qed.

    Lemma _Z_to_bytes_unsigned_le_shrink_cnt:
      forall (cnt cnt': nat) (v: Z),
        (0 <= v)%Z ->
        (v < 2^(8*cnt))%Z ->
        cnt < cnt' ->
        _Z_to_bytes_unsigned_le cnt' v =
        _Z_to_bytes_unsigned_le cnt v ++ repeat 0%N (cnt' - cnt).
    Proof. apply _Z_to_bytes_unsigned_le'_shrink_cnt. Qed.

    Lemma _Z_to_bytes_unsigned_le'_S_idx:
      forall (idx cnt: nat) (v: Z),
        (0 <= v)%Z ->
        _Z_to_bytes_unsigned_le' (S idx) cnt v =
        _Z_to_bytes_unsigned_le' idx cnt (v ≫ 8).
    Proof.
      intros idx cnt v Hlower; generalize dependent idx;
        induction cnt; intros=> //=.
      rewrite /_Z_to_bytes_unsigned_le' //=; f_equal.
      - rewrite /_get_byte Z.shiftr_shiftr; try lia.
        by replace (8 + 8 * idx)%Z with (8 * S idx)%Z by lia.
      - fold (_Z_to_bytes_unsigned_le' (S (S idx)) cnt v).
        fold (_Z_to_bytes_unsigned_le' (S idx) cnt (v ≫ 8)).
        assert (v < 2^(8*cnt) \/ 2^(8*cnt) <= v)%Z as [Hv | Hv] by lia.
        + by apply IHcnt.
        + rewrite /_Z_to_bytes_unsigned_le' //=.
          rewrite -seq_shift map_map.
          generalize (seq (S idx) cnt); induction l=> //=; f_equal.
          * rewrite /_get_byte Z.shiftr_shiftr; try lia.
            by replace (8 + 8 * a)%Z with (8 * S a)%Z by lia.
          * apply IHl.
    Qed.
  End ToBytesFacts_internal.

  Section FromBytes_internal.
    Definition _Z_from_bytes_unsigned_le' (idx: nat) (bytes: list N): Z :=
      foldr (fun '(idx, byte) acc => Z.lor (_set_byte (Z.of_N byte) idx) acc)
            0%Z (zip (seq idx (length bytes)) bytes).

    Definition _Z_from_bytes_unsigned_le (bytes: list N): Z :=
      _Z_from_bytes_unsigned_le' 0 bytes.

    Definition _Z_from_bytes_le (sgn: signed) (bytes: list N): Z :=
      let unsigned := _Z_from_bytes_unsigned_le bytes in
      match sgn with
      | Signed => to_signed_bits (8 * N.of_nat (length bytes)) unsigned
      | Unsigned => unsigned
      end.

    (* NOTE: This will be sealed once we finish the proofs for this section. *)
    Definition _Z_from_bytes_def (endianness: endian) (sgn: signed) (bytes: list N): Z :=
      _Z_from_bytes_le
        sgn match endianness with
            | Little => bytes
            | Big    => List.rev bytes
            end.
  End FromBytes_internal.

  Section FromBytesFacts_internal.
    Lemma _Z_from_bytes_unsigned_le'_nil:
      forall (idx: nat),
        _Z_from_bytes_unsigned_le' idx [] = 0%Z.
    Proof. rewrite /_Z_from_bytes_unsigned_le' //=. Qed.

    Lemma _Z_from_bytes_unsigned_le_nil:
      _Z_from_bytes_unsigned_le [] = 0%Z.
    Proof. apply _Z_from_bytes_unsigned_le'_nil. Qed.

    Lemma _Z_from_bytes_le_nil:
      forall sgn,
      _Z_from_bytes_le sgn [] = 0%Z.
    Proof.
      move=> [ | ];
        rewrite /_Z_from_bytes_le
                _Z_from_bytes_unsigned_le_nil //=.
    Qed.

    Lemma _Z_from_bytes_def_nil:
      forall endianness sgn,
        _Z_from_bytes_def endianness sgn [] = 0%Z.
    Proof.
      move=> [ | ] sgn;
        by rewrite /_Z_from_bytes_def /rev
                   _Z_from_bytes_le_nil.
    Qed.

    Lemma _Z_from_bytes_unsigned_le'_cons:
      forall (idx: nat) (byte: N) (bytes: list N),
        _Z_from_bytes_unsigned_le' idx (byte :: bytes) =
        Z.lor (_Z_from_bytes_unsigned_le' idx [byte])
              (_Z_from_bytes_unsigned_le' (S idx) bytes).
    Proof.
      intros; generalize dependent idx; generalize dependent byte;
        induction bytes => //=; intros.
      - rewrite _Z_from_bytes_unsigned_le'_nil Z.lor_0_r; lia.
      - rewrite /_Z_from_bytes_unsigned_le' //=.
        by rewrite Z.lor_0_r.
    Qed.

    Lemma _Z_from_bytes_unsigned_le_cons:
      forall (byte: N) (bytes: list N),
        _Z_from_bytes_unsigned_le (byte :: bytes) =
        Z.lor (_Z_from_bytes_unsigned_le' 0 [byte])
              (_Z_from_bytes_unsigned_le' 1 bytes).
    Proof. apply _Z_from_bytes_unsigned_le'_cons. Qed.

    Lemma _Z_from_bytes_unsigned_le'_app:
      forall (idx: nat) (bs1 bs2: list N),
        _Z_from_bytes_unsigned_le' idx (bs1 ++ bs2) =
        Z.lor (_Z_from_bytes_unsigned_le' idx bs1)
              (_Z_from_bytes_unsigned_le' (idx + length bs1) bs2).
    Proof.
      intros; generalize dependent idx; generalize dependent bs2;
        induction bs1 => //=; intros.
      - repeat rewrite _Z_from_bytes_unsigned_le'_nil.
        replace (idx + 0) with idx by lia.
        by rewrite Z.lor_0_l.
      - rewrite _Z_from_bytes_unsigned_le'_cons.
        rewrite (_Z_from_bytes_unsigned_le'_cons idx a bs1).
        rewrite IHbs1.
        rewrite Nat.add_succ_r.
        by rewrite Z.lor_assoc.
    Qed.

    Lemma _Z_from_bytes_unsigned_le_app:
      forall (bs1 bs2: list N),
        _Z_from_bytes_unsigned_le (bs1 ++ bs2) =
        Z.lor (_Z_from_bytes_unsigned_le' 0 bs1)
              (_Z_from_bytes_unsigned_le' (length bs1) bs2).
    Proof. apply _Z_from_bytes_unsigned_le'_app. Qed.

    Lemma _Z_from_bytes_unsigned_le'_0s:
      forall (idx cnt: nat),
        _Z_from_bytes_unsigned_le' idx (repeat 0%N cnt) = 0%Z.
    Proof.
      intros; generalize dependent idx.
      induction cnt => idx //=.
      rewrite _Z_from_bytes_unsigned_le'_cons.
      rewrite IHcnt.
      rewrite /_Z_from_bytes_unsigned_le' //=.
      by rewrite _set_byte_0 !Z.lor_0_r.
    Qed.

    Lemma _Z_from_bytes_unsigned_le_0s:
      forall (cnt: nat),
        _Z_from_bytes_unsigned_le (repeat 0%N cnt) = 0%Z.
    Proof. apply _Z_from_bytes_unsigned_le'_0s. Qed.

    Lemma _Z_from_bytes_le_0s:
      forall sgn (cnt: nat),
        _Z_from_bytes_le sgn (repeat 0%N cnt) = 0%Z.
    Proof.
      move=> [ | ] cnt; rewrite /_Z_from_bytes_le.
      - rewrite repeat_length _Z_from_bytes_unsigned_le_0s.
        assert (8 * N.of_nat cnt = 0 \/ 0 < 8 * N.of_nat cnt)%N as [Hcnt | Hcnt] by lia.
        + rewrite /to_signed_bits bool_decide_eq_true_2; by lia.
        + rewrite to_signed_bits_id; intuition; [by reflexivity | ].
          apply Z.pow_pos_nonneg; lia.
      - apply _Z_from_bytes_unsigned_le_0s.
    Qed.

    Lemma _Z_from_bytes_def_0s:
      forall endianness sgn (cnt: nat),
        _Z_from_bytes_def endianness sgn (repeat 0%N cnt) = 0%Z.
    Proof.
      move=> [ | ] sgn cnt; rewrite /_Z_from_bytes_def ?rev_repeat;
        apply _Z_from_bytes_le_0s.
    Qed.

    Lemma _Z_from_bytes_unsigned_le'_S_idx:
      forall (idx: nat) (bytes: list N),
        (_Z_from_bytes_unsigned_le' (S idx) (bytes) =
         _Z_from_bytes_unsigned_le' idx bytes ≪ 8)%Z.
    Proof.
      intros idx bytes; generalize dependent idx;
        induction bytes; intros=> //=.
      rewrite /_Z_from_bytes_unsigned_le' //=.
      fold (_Z_from_bytes_unsigned_le' (S (S idx)) bytes).
      fold (_Z_from_bytes_unsigned_le' (S idx) bytes).
      rewrite Z.shiftl_lor.
      by rewrite IHbytes _set_byte_S_idx.
    Qed.

    #[local] Lemma length_1_inv:
      forall {A} (l : list A),
        length l = 1%nat ->
        exists x0,
          l = [x0].
    Proof. intros; do 2 (try destruct l)=> //; do 1 eexists; eauto. Qed.
    #[local] Lemma length_2_inv:
      forall {A} (l : list A),
        length l = 2%nat ->
        exists x0 x1,
          l = [x0; x1].
    Proof. intros; do 3 (try destruct l)=> //; do 2 eexists; eauto. Qed.
    #[local] Lemma length_4_inv:
      forall {A} (l : list A),
        length l = 4%nat ->
        exists x0 x1 x2 x3,
          l = [x0; x1; x2; x3].
    Proof. intros; do 5 (try destruct l)=> //; do 4 eexists; eauto. Qed.
    #[local] Lemma length_8_inv:
      forall {A} (l : list A),
        length l = 8%nat ->
        exists x0 x1 x2 x3 x4 x5 x6 x7,
          l = [x0; x1; x2; x3; x4; x5; x6; x7].
    Proof. intros; do 9 (try destruct l)=> //; do 8 eexists; eauto. Qed.
    #[local] Lemma length_16_inv:
      forall {A} (l : list A),
        length l = 16%nat ->
        exists x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15,
          l = [x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13; x14; x15].
    Proof. intros; do 17 (try destruct l)=> //; do 16 eexists; eauto. Qed.

    Lemma _Z_from_bytes_unsigned_le_bswap:
      forall bsz sz (bytes: list N) v,
        Datatypes.length bytes = sz ->
        bitsize.bytesNat bsz = sz ->
        _Z_from_bytes_unsigned_le bytes = v ->
        _Z_from_bytes_unsigned_le (rev bytes) = bswap bsz v.
    Proof.
      rewrite /_Z_from_bytes_unsigned_le/_Z_from_bytes_unsigned_le';
        move=> bsz sz bytes v Hlen Hsz Hdecodes; destruct bsz;
        simpl in *; rewrite -Hsz in Hlen; subst;
        [ apply length_1_inv  in Hlen as [? Hbytes]
        | apply length_2_inv  in Hlen as [? [? Hbytes]]
        | apply length_4_inv  in Hlen as [? [? [? [? Hbytes]]]]
        | apply length_8_inv  in Hlen as [? [? [? [? [? [? [? [? Hbytes]]]]]]]]
        | apply length_16_inv in Hlen as [? [? [? [? [? [? [? [?
                                            [? [? [? [? [? [? [? [? Hbytes]]]]]]]]]]]]]]]]];
        rewrite Hbytes //= !Z.lor_0_r.
      - now rewrite bswap8_set_byte_reverse.
      - now rewrite bswap16_set_byte_reverse.
      - now rewrite bswap32_set_byte_reverse.
      - now rewrite bswap64_set_byte_reverse.
      - now rewrite bswap128_set_byte_reverse.
    Qed.

    Lemma _Z_from_bytes_unsigned_le'_singleton idx a :
      _Z_from_bytes_unsigned_le' idx [a] = (_set_byte (Z.of_N a) idx).
    Proof.
      rewrite/_Z_from_bytes_unsigned_le'.
      cbn.
      by rewrite Z.lor_0_r.
    Qed.

    Lemma _Z_from_bytes_unsigned_le_singleton a :
      _Z_from_bytes_unsigned_le [a] = (_get_byte (Z.of_N a) 0).
    Proof.
      by rewrite /_Z_from_bytes_unsigned_le _Z_from_bytes_unsigned_le'_singleton _get_0_set_0_eq.
    Qed.

    Lemma _Z_from_bytes_le_singleton sgn a :
      _Z_from_bytes_le sgn [a] =
        match sgn with
        | Signed => to_signed_bits 8 (_get_byte a 0)
        | Unsigned => _get_byte a 0
        end.
    Proof.
      rewrite /_Z_from_bytes_le _Z_from_bytes_unsigned_le_singleton.
      by rewrite /= N.mul_1_r.
    Qed.

    Lemma _Z_from_bytes_def_singleton endianness sgn a :
      _Z_from_bytes_def endianness sgn [a] =
        match sgn with
        | Signed => to_signed_bits 8 (_get_byte a 0)
        | Unsigned => _get_byte a 0
        end.
    Proof.
      rewrite /_Z_from_bytes_def /=.
      by destruct endianness; rewrite _Z_from_bytes_le_singleton.
    Qed.

    Lemma _Z_from_bytes_unsigned_le'_bounds bytes idx b :
      (256 ^ (length bytes + Z.of_nat idx)%Z <= b)%Z ->
      (0 ≤ _Z_from_bytes_unsigned_le' idx bytes < b)%Z.
    Proof.
      move: b idx.
      elim bytes.
      {
        move => ? ?.
        rewrite Z.add_0_l.
        move => ?.
        split; [by []|].
        cbn.
        eapply Z.lt_le_trans.
        2: { eassumption. }
        apply Z.pow_pos_nonneg; [ by[] | ].
        exact: Zle_0_nat.
      }
      move => a l IH b idx /= H.
      rewrite _Z_from_bytes_unsigned_le'_cons.
      rewrite _Z_from_bytes_unsigned_le'_S_idx.
      assert (
          (0
             ≤ Z.lor (_Z_from_bytes_unsigned_le' idx [a]) (_Z_from_bytes_unsigned_le' idx l ≪ 8) <
             2 ^ (Z.of_N $ N.of_nat (8 * (S (length l) + idx))))%Z
        ) as H1.
      {
        apply ZlorRange.
        {
          rewrite _Z_from_bytes_unsigned_le'_singleton.
          move: (_set_byte_bound (Z.of_N a) idx) => [L0 L1].
          split; first assumption.
          eapply Z.lt_le_trans; first eassumption.
          apply Z.pow_le_mono_r; first done.
          lia.
        }
        move: (IH (2 ^ Z.of_N (N.of_nat (8 * (S (length l) + idx))))%Z (S idx)).
        rewrite _Z_from_bytes_unsigned_le'_S_idx.
        apply.
        rewrite nat_N_Z.
        rewrite Nat2Z.inj_mul.
        rewrite Z.pow_mul_r //.
        apply: Z.pow_le_mono.
        1: done.
        lia.
      }
      split; first tauto.
      eapply Z.lt_le_trans.
      {
        move: H1 => [_ max].
        eassumption.
      }
      rewrite nat_N_Z.
      rewrite Nat2Z.inj_mul.
      rewrite Z.pow_mul_r //.
      cbn.
      eapply Z.le_trans.
      2: eassumption.
      apply: Z.pow_le_mono.
      1: done.
      lia.
    Qed.

    Lemma _Z_from_bytes_unsigned_le'_bound bytes idx b :
      (256 ^ (length bytes + Z.of_nat idx)%Z - 1 <= b)%Z ->
      (0 ≤ _Z_from_bytes_unsigned_le' idx bytes ≤ b)%Z.
    Proof.
      pose proof (_Z_from_bytes_unsigned_le'_bounds bytes idx
                    (256 ^ (length bytes + Z.of_nat idx)%Z)%Z
                    ltac:(lia))
        as Hbound'.
      lia.
    Qed.

    Lemma _Z_from_bytes_unsigned_le_bounds bytes b :
      (256 ^ length bytes <= b)%Z ->
      (0 <= _Z_from_bytes_unsigned_le bytes < b)%Z.
    Proof.
      move => H.
      apply _Z_from_bytes_unsigned_le'_bounds.
      by rewrite Z.add_0_r.
    Qed.

    Lemma _Z_from_bytes_unsigned_le_bound bytes b :
      (256 ^ length bytes - 1 <= b)%Z ->
      (0 <= _Z_from_bytes_unsigned_le bytes <= b)%Z.
    Proof.
      pose proof (_Z_from_bytes_unsigned_le_bounds bytes
                    (256 ^ (length bytes))
                    ltac:(lia))
        as Hbound'.
      lia.
    Qed.

  End FromBytesFacts_internal.

  Section FromToFacts_internal.
    #[local] Transparent _get_byte _set_byte.

    Lemma _Z_from_to_bytes_unsigned_le'_overflow:
      forall (idx cnt: nat) (v: Z),
        (2^(8*(idx+cnt)) <= v)%Z ->
        _Z_from_bytes_unsigned_le' idx (_Z_to_bytes_unsigned_le' idx cnt v) =
        Z.land ((Z.ones (8*cnt)) ≪ (8*idx)) v.
    Proof.
      intros idx cnt v Hlower;
        generalize dependent idx;
        generalize dependent v;
        induction cnt; intros=> //=.
      - rewrite /Z.ones Z.mul_0_r Z.shiftl_0_r
                _Z_to_bytes_unsigned_le'_0_bytes
                _Z_from_bytes_unsigned_le'_nil.
        by rewrite Z.shiftl_0_l Z.land_0_l.
      - rewrite _Z_to_bytes_unsigned_le'_S_cnt
                _Z_from_bytes_unsigned_le'_app
                _Z_to_bytes_unsigned_le'_length.
        rewrite [_Z_to_bytes_unsigned_le' _ 1 _]/_Z_to_bytes_unsigned_le' //=.
        rewrite [_Z_from_bytes_unsigned_le' _ [_]]/_Z_from_bytes_unsigned_le' //=.
        rewrite Z.lor_0_r.
        rewrite Z2N.id; [ | apply _get_byte_nonneg].
        rewrite _set_get_byte_roundtrip/_get_byte.
        assert (2^(8*(idx+cnt)) <= v)%Z as Hlower'. {
          etrans; last eapply Hlower;
            apply Z.pow_le_mono_r; lia.
        }
        specialize (IHcnt v idx Hlower'); rewrite IHcnt //=.
        apply Z.bits_inj'=> n ?.
        repeat (rewrite ?Z.lor_spec ?Z.land_spec; try lia).
        rewrite Z.shiftl_land -Z.ldiff_ones_r; try lia.
        repeat (rewrite ?Z.lor_spec ?Z.land_spec ?Z.shiftl_spec ?Z.ldiff_spec; try lia).
        rewrite !Z.testbit_ones; try lia.
        churn_bits'.
    Qed.

    Lemma _Z_from_to_bytes_unsigned_le'_roundtrip:
      forall (idx cnt: nat) (v: Z),
        (0 <= v)%Z ->
        (v < 2^(8*(idx+cnt)))%Z ->
        _Z_from_bytes_unsigned_le' idx (_Z_to_bytes_unsigned_le' idx cnt v) =
        (v - v `mod` 2^(8*idx))%Z.
    Proof.
      intros idx cnt v Hlower Hupper;
        generalize dependent idx;
        generalize dependent v;
        induction cnt; intros=> //=.
      - rewrite Z.add_0_r in Hupper.
        rewrite _Z_to_bytes_unsigned_le'_0_bytes
                _Z_from_bytes_unsigned_le'_nil.
        rewrite Zmod_small; try intuition; lia.
      - assert (v < 2^(8*(idx+cnt)) \/ 2^(8*(idx+cnt)) <= v)%Z as [Hv | Hv] by lia.
        + rewrite _Z_to_bytes_unsigned_le'_S_cnt
                  _Z_from_bytes_unsigned_le'_app
                  _Z_to_bytes_unsigned_le'_length
                  IHcnt; try lia.
          rewrite _Z_to_bytes_unsigned_le'_small; try lia.
          1: by rewrite _Z_from_bytes_unsigned_le'_0s Z.lor_0_r.
        + clear IHcnt.
          rewrite Zmod_eq_full.
          2: pose proof (Z.pow_pos_nonneg
                           2 (8 * idx)
                           ltac:(lia) ltac:(lia)); lia.
          rewrite -Z.shiftr_div_pow2; try lia.
          rewrite -Z.shiftl_mul_pow2; try lia.
          rewrite -Z.ldiff_ones_r; try lia.
          rewrite _Z_to_bytes_unsigned_le'_S_cnt
                  _Z_from_bytes_unsigned_le'_app
                  _Z_to_bytes_unsigned_le'_length.
          rewrite Z.sub_sub_distr Z.sub_diag Z.add_0_l.
          rewrite [_Z_to_bytes_unsigned_le' _ 1 _]/_Z_to_bytes_unsigned_le' //=.
          rewrite [_Z_from_bytes_unsigned_le' _ [_]]/_Z_from_bytes_unsigned_le' //=.
          rewrite Z.lor_0_r.
          rewrite Z2N.id; [ | apply _get_byte_nonneg].
          rewrite _set_get_byte_roundtrip/_get_byte Z.shiftl_land.
          rewrite _Z_from_to_bytes_unsigned_le'_overflow; try lia.
          erewrite Z_ldiff_split; eauto; f_equal.
          rewrite -Z.ldiff_ones_r; try lia.
          rewrite Z.land_comm.

          apply Z.bits_inj'=> n ?.
          repeat (rewrite ?Z.lor_spec ?Z.land_spec ?Z.shiftl_spec ?Z.ldiff_spec; try lia).
          rewrite !Z.testbit_ones; try lia.
          churn_bits'.
    Qed.

    Lemma _Z_from_to_bytes_unsigned_le_roundtrip:
      forall (cnt: nat) (v: Z),
        (0 <= v)%Z ->
        (v < 2^(8*cnt))%Z ->
        _Z_from_bytes_unsigned_le (_Z_to_bytes_unsigned_le cnt v) = v.
    Proof.
      intros cnt v Hlower Hupper.
      pose proof (_Z_from_to_bytes_unsigned_le'_roundtrip 0 cnt v Hlower) as Hpf.
      rewrite Z.add_0_l in Hpf.
      specialize (Hpf Hupper).
      rewrite /_Z_from_bytes_unsigned_le
              /_Z_to_bytes_unsigned_le Hpf.
      rewrite Z.mul_0_r Z.pow_0_r Zmod_1_r; lia.
    Qed.

    Lemma _get_set_later_bytes_irrelevant idx start lst :
      (idx < start)%nat ->
      _get_byte
          (foldr
            (λ '(idx0, byte) (acc : Z),
               (_set_byte (Z.of_N byte) idx0 `lor` acc)%Z) 0%Z
            (zip (seq start (length lst)) lst)) idx = 0%Z.
    Proof.
      move: idx start.
      induction lst.
      {
        move => ? ? ?.
        by rewrite _get_byte_0.
      }
      move => ? ? ?.
      cbn.
      rewrite _get_byte_lor.
      rewrite _get_set_byte_no_overlap.
      2: lia.
      rewrite Z.lor_0_l.
      apply: IHlst.
      lia.
    Qed.

    Lemma _get_byte_0_small_id (z : Z) :
      _get_byte z 0 = Z.modulo z 256.
    Proof. by rewrite/_get_byte /Z.of_nat Z.mul_0_r Z.shiftr_0_r Z.land_ones. Qed.

    Lemma _Z_to_from_bytes_unsigned_le'_roundtrip (bytes : list N) (idx cnt : nat) :
      Forall (λ b : N, (b < 256)%N) bytes →
      cnt = length bytes →
      _Z_to_bytes_unsigned_le' idx cnt (_Z_from_bytes_unsigned_le' idx bytes) = bytes.
    Proof.
      move: idx bytes.
      induction cnt.
      { by move => ? []. }
      move => idx [].
      { done. }
      move => hd tl smallH.
      apply Forall_cons_1 in smallH.
      move: smallH => [small_hdH small_tlH].
      move => [] cnt_eq.
      rewrite/_Z_to_bytes_unsigned_le'.
      cbn.
      f_equal.
      {
        rewrite _get_byte_lor _get_set_later_bytes_irrelevant.
        2: lia.
        rewrite Z.lor_0_r _get_set_byte_roundtrip _get_byte_0_small_id Z2N.inj_mod.
        2: lia.
        2: lia.
        by rewrite N2Z.id N.mod_small.
      }
      move: (IHcnt (S idx) tl small_tlH cnt_eq).
      rewrite /_Z_to_bytes_unsigned_le' /_Z_from_bytes_unsigned_le'.
      move => IH.
      rewrite -{3}IH.
      apply: map_ext_Forall.
      rewrite Forall_seq.
      move => ? ?.
      cbn.
      f_equal.
      rewrite _get_byte_lor _get_set_byte_no_overlap.
      2: lia.
      by rewrite Z.lor_0_l.
    Qed.

    Lemma _Z_to_from_bytes_unsigned_le_roundtrip (bytes : list N) (cnt : nat) :
      Forall (fun b => b < 256)%N bytes ->
      cnt = length bytes ->
      (_Z_to_bytes_unsigned_le cnt $ _Z_from_bytes_unsigned_le bytes) = bytes.
    Proof.
      move => ? ?.
      by rewrite/_Z_to_bytes_unsigned_le/_Z_from_bytes_unsigned_le
        _Z_to_from_bytes_unsigned_le'_roundtrip.
    Qed.

    Lemma _Z_from_to_bytes_le_roundtrip:
      forall (cnt: nat) (sgn: signed) (v: Z),
        match sgn with
        | Signed   => -2^((8*cnt)-1) <= v /\ v <= 2^((8*cnt)-1) - 1
        | Unsigned => 0 <= v /\ v < 2^(8*cnt)
        end%Z ->
        _Z_from_bytes_le sgn (_Z_to_bytes_le cnt sgn v) = v.
    Proof.
      destruct sgn; intros v [Hlower Hupper];
        [ | by apply _Z_from_to_bytes_unsigned_le_roundtrip].
      rewrite /_Z_from_bytes_le /_Z_to_bytes_le _Z_to_bytes_unsigned_le_length.
      assert (v < 0 \/ 0 <= v)%Z as [Hv | Hv] by lia.
      - rewrite _Z_from_to_bytes_unsigned_le_roundtrip.
        + apply to_signed_unsigned_bits_roundtrip; intuition;
            replace (Z.of_N (8 * N.of_nat cnt) - 1)%Z
              with (8 * cnt - 1)%Z; lia.
        + rewrite /trim; apply Z.mod_pos;
            apply Z.pow_pos_nonneg; lia.
        + rewrite /trim.
          replace (Z.of_N (8 * N.of_nat cnt))
            with (8 * cnt)%Z by lia.
          by pose proof (Z_mod_lt v (2^(8*cnt))%Z
                                   ltac:(apply Z.lt_gt; apply Z.pow_pos_nonneg; lia))
            as [? ?].
      - rewrite /trim Zmod_small; intuition; try lia.
        + rewrite _Z_from_to_bytes_unsigned_le_roundtrip; try lia.
          * apply to_signed_bits_id; intuition.
            eapply Z.le_lt_trans; eauto.
            replace (Z.of_N (8 * N.of_nat cnt) - 1)%Z
              with (8 * cnt - 1)%Z; lia.
          * eapply Z.le_lt_trans; eauto.
            match goal with
            | |- (_ < ?r)%Z => replace r with (r - 0)%Z by lia
            end.
            apply Z.sub_lt_le_mono; try apply Z.pow_lt_mono_r; lia.
        + eapply Z.le_lt_trans; eauto.
          match goal with
          | |- (_ < ?r)%Z => replace r with (r - 0)%Z by lia
          end.
          apply Z.sub_lt_le_mono; try apply Z.pow_lt_mono_r; lia.
    Qed.

    Lemma _Z_from_unsigned_to_signed_bytes_le:
      forall (cnt: nat) (v: Z),
        (-2^((8*cnt)-1) <= v)%Z ->
        (v <= 2^((8*cnt)-1) - 1)%Z ->
        _Z_from_bytes_le Unsigned (_Z_to_bytes_le cnt Signed v) =
        to_unsigned_bits (8*N.of_nat cnt) v.
    Proof.
      move=> cnt v Hlower Hupper.
      rewrite /trim /_Z_from_bytes_le /_Z_to_bytes_le.
      rewrite _Z_from_to_bytes_unsigned_le_roundtrip /trim //.
      - apply Z_mod_lt; rewrite Z.gt_lt_iff;
          apply Z.pow_pos_nonneg; lia.
      - replace (Z.of_N (8 * N.of_nat cnt)) with (8 * cnt)%Z by lia;
          apply Z_mod_lt; rewrite Z.gt_lt_iff;
          apply Z.pow_pos_nonneg; lia.
    Qed.

    Lemma _Z_from_signed_to_unsigned_bytes_le:
      forall (cnt: nat) (v: Z),
        (0 <= v)%Z ->
        (v < 2^(8*cnt))%Z ->
        _Z_from_bytes_le Signed (_Z_to_bytes_le cnt Unsigned v) =
        to_signed_bits (8*N.of_nat cnt) v.
    Proof.
      move=> cnt v Hlower Hupper.
      rewrite /_Z_from_bytes_le /_Z_to_bytes_le
              _Z_to_bytes_unsigned_le_length
              _Z_from_to_bytes_unsigned_le_roundtrip //.
    Qed.

    Lemma _Z_from_to_bytes_def_roundtrip:
      forall (cnt: nat) (endianness: endian) (sgn: signed) (v: Z),
        match sgn with
        | Signed   => -2^((8*cnt)-1) <= v /\ v <= 2^((8*cnt)-1) - 1
        | Unsigned => 0 <= v /\ v < 2^(8*cnt)
        end%Z ->
        _Z_from_bytes_def endianness sgn (_Z_to_bytes_def cnt endianness sgn v) = v.
    Proof.
      rewrite /_Z_from_bytes_def /_Z_to_bytes_def;
        intros cnt [ | ] sgn v H;
        try rewrite rev_involutive;
        by apply _Z_from_to_bytes_le_roundtrip.
    Qed.

    Lemma _Z_to_from_bytes_le_round_trip sgn cnt bytes :
      Forall (λ b : N, (b < 256)%N) bytes ->
      cnt = length bytes ->
      _Z_to_bytes_le cnt sgn (_Z_from_bytes_le sgn bytes) = bytes.
    Proof.
      move => small cntH.
      move: sgn => [].
      2: {
        cbn.
        rewrite/_Z_to_bytes_le.
        by apply: _Z_to_from_bytes_unsigned_le_roundtrip.
      }
      rewrite/_Z_to_bytes_le.
      cbn.
      rewrite !cntH.
      rewrite trim_to_signed_bits_agree.
      rewrite to_unsigned_bits_id.
      { by apply: _Z_to_from_bytes_unsigned_le_roundtrip. }
      apply: _Z_from_bytes_unsigned_le_bounds.
      rewrite -(Z.pow_mul_r 2 8).
      2: done.
      2: lia.
      apply: Z.eq_le_incl.
      f_equal.
      rewrite -nat_N_Z.
      case (N.of_nat (length bytes)).
      { lia. }
      move => ?.
      lia.
    Qed.

    Lemma _Z_to_from_bytes_def_roundtrip bytes sgn endianness cnt :
      Forall (λ b : N, (b < 256)%N) bytes →
      cnt = length bytes →
      _Z_to_bytes_def cnt endianness sgn (_Z_from_bytes_def endianness sgn bytes) = bytes.
    Proof.
      move => small cntH.
      rewrite/_Z_from_bytes_def/_Z_to_bytes_def.
      move: endianness => [].
      { exact: _Z_to_from_bytes_le_round_trip. }
      rewrite _Z_to_from_bytes_le_round_trip.
      { exact: rev_involutive. }
      { exact: Forall_rev. }
      by rewrite length_rev.
    Qed.

    Lemma _Z_from_unsigned_to_signed_bytes_def:
      forall (cnt: nat) (endianness: endian) (v: Z),
        (-2^((8*cnt)-1) <= v)%Z ->
        (v <= 2^((8*cnt)-1) - 1)%Z ->
        _Z_from_bytes_def endianness Unsigned (_Z_to_bytes_def cnt endianness Signed v) =
        to_unsigned_bits (8*N.of_nat cnt) v.
    Proof.
      rewrite /_Z_from_bytes_def /_Z_to_bytes_def;
        intros cnt [ | ] v Hlower Hupper;
        try rewrite rev_involutive;
        by apply _Z_from_unsigned_to_signed_bytes_le.
    Qed.

    Lemma _Z_from_signed_to_unsigned_bytes_def:
      forall (cnt: nat) (endianness: endian) (v: Z),
        (0 <= v)%Z ->
        (v < 2^(8*cnt))%Z ->
        _Z_from_bytes_def endianness Signed (_Z_to_bytes_def cnt endianness Unsigned v) =
        to_signed_bits (8*N.of_nat cnt) v.
    Proof.
      rewrite /_Z_from_bytes_def /_Z_to_bytes_def;
        intros cnt [ | ] v Hlower Hupper;
        try rewrite rev_involutive;
        by apply _Z_from_signed_to_unsigned_bytes_le.
    Qed.

    Lemma _Z_from_bytes_Unsigned_bound_internal (endianness : endian) :
      forall lst,
        (0 <= _Z_from_bytes_def endianness Unsigned (rev lst) < 256 ^ (length $ rev lst))%Z.
    Proof.
      rewrite/_Z_from_bytes_def.
      rewrite/_Z_from_bytes_le.
      move => lst.
      apply _Z_from_bytes_unsigned_le_bounds.
      case_match; by rewrite !length_rev.
    Qed.
  End FromToFacts_internal.

  Section ToBytes_external.
    Definition _Z_to_bytes_aux : seal (_Z_to_bytes_def). Proof. by eexists. Qed.
    Definition _Z_to_bytes := _Z_to_bytes_aux.(unseal).
    Definition _Z_to_bytes_eq: _Z_to_bytes = _ := _Z_to_bytes_aux.(seal_eq).
  End ToBytes_external.

  Section ToBytesFacts_external.
    Lemma _Z_to_bytes_length:
      forall (cnt: nat) endianness sgn v,
        length (_Z_to_bytes cnt endianness sgn v) = cnt.
    Proof. move=> *; rewrite _Z_to_bytes_eq; apply _Z_to_bytes_def_length. Qed.
    Lemma _Z_to_bytes_lengthN:
      forall (cnt: nat) endianness sgn v,
        lengthN (_Z_to_bytes cnt endianness sgn v) = N.of_nat cnt.
    Proof.
      intros.
      by rewrite/lengthN _Z_to_bytes_length.
    Qed.

    Lemma _Z_to_bytes_0_bytes:
      forall sgn endianness v,
        _Z_to_bytes 0 endianness sgn v = [].
    Proof. move=> *; rewrite _Z_to_bytes_eq; apply _Z_to_bytes_def_0_bytes. Qed.

    Lemma _Z_to_bytes_0_value:
      forall (cnt: nat) endianness sgn,
        _Z_to_bytes cnt endianness sgn 0%Z = repeat 0%N cnt.
    Proof. move=> *; rewrite _Z_to_bytes_eq; apply _Z_to_bytes_def_0_value. Qed.

    Lemma _Z_to_bytes_unsigned_le_range cnt v :
      Forall (λ v : N, (v < 256)%N) (_Z_to_bytes_unsigned_le cnt v).
    Proof.
      rewrite/_Z_to_bytes_unsigned_le/_Z_to_bytes_unsigned_le'.
      rewrite Forall_map.
      apply: Forall_true.
      move => x.
      move: (_get_byte_bound v x).
      cbn.
      lia.
    Qed.

    Lemma _Z_to_bytes_le_range z cnt sign :
      Forall (λ v : N, v < 256)%N (_Z_to_bytes_le cnt sign z).
    Proof.
      rewrite/_Z_to_bytes_le.
      move: sign => []; exact: _Z_to_bytes_unsigned_le_range.
    Qed.

    Lemma _Z_to_bytes_range z cnt endianness sign:
      Forall (λ v : N, v < 256)%N (_Z_to_bytes cnt endianness sign z).
    Proof.
      rewrite _Z_to_bytes_eq/_Z_to_bytes_def.
      move: endianness => [].
      { exact: _Z_to_bytes_le_range. }
      apply: Forall_rev.
      exact: _Z_to_bytes_le_range.
    Qed.

  End ToBytesFacts_external.

  Section FromBytes_external.
    Definition _Z_from_bytes_aux: seal _Z_from_bytes_def. Proof. by eexists. Qed.
    Definition _Z_from_bytes := _Z_from_bytes_aux.(unseal).
    Definition _Z_from_bytes_eq: @_Z_from_bytes = _ := _Z_from_bytes_aux.(seal_eq).
  End FromBytes_external.

  Section FromBytesFacts_external.
    Lemma _Z_from_bytes_nil:
      forall endianness sgn,
        _Z_from_bytes endianness sgn [] = 0%Z.
    Proof. move=> *; rewrite _Z_from_bytes_eq; apply _Z_from_bytes_def_nil. Qed.

    Lemma _Z_from_bytes_0s:
      forall endianness sgn (cnt: nat),
        _Z_from_bytes endianness sgn (repeat 0%N cnt) = 0%Z.
    Proof. move=> *; rewrite _Z_from_bytes_eq; apply _Z_from_bytes_def_0s. Qed.
    Lemma _Z_from_bytes_Unsigned_bound (endianness : endian) :
      forall lst,
        (0 <= _Z_from_bytes endianness Unsigned lst < 256 ^ (length lst))%Z.
    Proof.
      move => lst.
      rewrite -[lst]rev_involutive.
      rewrite _Z_from_bytes_eq.
      exact: _Z_from_bytes_Unsigned_bound_internal.
    Qed.
    Lemma _Z_from_bytes_Unsigned_boundN (endianness : endian) :
      forall lst,
        (0 <= _Z_from_bytes endianness Unsigned lst < 256 ^ (lengthN lst))%Z.
    Proof.
      move=> *; rewrite/lengthN length_lengthN Nat2N.id nat_N_Z.
      exact: _Z_from_bytes_Unsigned_bound.
    Qed.

    Lemma _Z_from_bytes_singleton endianness sgn a :
      _Z_from_bytes endianness sgn [a] =
        match sgn with
        | Signed => to_signed_bits 8 (_get_byte a 0)
        | Unsigned => _get_byte a 0
        end.
    Proof.
      rewrite _Z_from_bytes_eq.
      exact: _Z_from_bytes_def_singleton.
    Qed.
  End FromBytesFacts_external.

  Section FromToFacts_external.
    Lemma _Z_from_to_bytes_roundtrip:
      forall (cnt: nat) (endianness: endian) (sgn: signed) (v: Z),
        match sgn with
        | Signed   => -2^((8*cnt)-1) <= v /\ v <= 2^((8*cnt)-1) - 1
        | Unsigned => 0 <= v /\ v < 2^(8*cnt)
        end%Z ->
        _Z_from_bytes endianness sgn (_Z_to_bytes cnt endianness sgn v) = v.
    Proof.
      move=> *; rewrite _Z_from_bytes_eq _Z_to_bytes_eq;
        by apply _Z_from_to_bytes_def_roundtrip.
    Qed.

    Lemma _Z_to_from_bytes_roundtrip bytes sgn endianness cnt :
      Forall (λ b : N, (b < 256)%N) bytes →
      cnt = length bytes →
      _Z_to_bytes cnt endianness sgn (_Z_from_bytes endianness sgn bytes) = bytes.
    Proof.
      move=> *; rewrite _Z_from_bytes_eq _Z_to_bytes_eq;
        by apply _Z_to_from_bytes_def_roundtrip.
    Qed.

    Lemma _Z_from_unsigned_to_signed_bytes:
      forall (cnt: nat) (endianness: endian) (v: Z),
        (-2^((8*cnt)-1) <= v)%Z ->
        (v <= 2^((8*cnt)-1) - 1)%Z ->
        _Z_from_bytes endianness Unsigned (_Z_to_bytes cnt endianness Signed v) =
        to_unsigned_bits (8*N.of_nat cnt) v.
    Proof.
      move=> *; rewrite _Z_from_bytes_eq _Z_to_bytes_eq;
        by apply _Z_from_unsigned_to_signed_bytes_def.
    Qed.

    Lemma _Z_from_signed_to_unsigned_bytes:
      forall (cnt: nat) (endianness: endian) (v: Z),
        (0 <= v)%Z ->
        (v < 2^(8*cnt))%Z ->
        _Z_from_bytes endianness Signed (_Z_to_bytes cnt endianness Unsigned v) =
        to_signed_bits (8*N.of_nat cnt) v.
    Proof.
      move=> *; rewrite _Z_from_bytes_eq _Z_to_bytes_eq;
        by apply _Z_from_signed_to_unsigned_bytes_def.
    Qed.
  End FromToFacts_external.
End FromToBytes.
