(*
 * Copyright (c) 2025 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import Stdlib.NArith.NArith.
Require Import bluerock.lang.cpp.syntax.prelude.
Require Export bluerock.lang.cpp.syntax.preliminary.
Import Uint63.

(** [Encoded.t] represents string literals containing characters of arbitrary
    byte width. The encoding is big endian, i.e. multi-byte characters are
    encoded from MSB to LSB. *)
Module Encoded.
  #[local] Open Scope uint63_scope.
  Definition t := PrimString.string.

  Definition num_bytes_int : t -> Uint63.int :=
    PrimString.length.
  Definition num_bytes_N : t -> N :=
    fun v => Z.to_N $ Uint63.to_Z $ num_bytes_int v.
  Definition compare : t -> t -> comparison :=
    PrimString.compare.

  (** [of_N bpc n] produces a primitive string containing exactly one encoded
      character of [bpc] many bytes taken from [n].
      Examples:
      - [of_N 1 97%N] -> "a"
      - [of_N 2 97%N] -> "\0x00a" ("\0x00" stands in for the actual NULL byte)
      - [of_N 1 0x61FF] -> "a" (0x61=97, the suffix is ignored)
   *)
  Definition of_N : forall (bpc : nat) (n : N), t :=
    fix go bpc n :=
      match bpc, n with
      | 0, _ => PrimString.make 0 0%uint63
      | S bpc, _ as n =>
          let (n, r) := N.div_eucl n 256%N in
          let c := PrimString.make 1%uint63 (Uint63.of_Z $ Z.of_N $ r) in
          go bpc n ++ c
      end%pstring.

  (** [of_list_N bpc ls] produces a primitive string that contains exactly one
      encoded character of byte-width [bpc] for every item in [ls]. *)
  Definition of_list_N (bpc : nat) : forall (chars : list N), t :=
    fix go chars :=
      match chars with
      | [] => ""%pstring
      | c :: chars =>
          let c := of_N bpc c in
          c ++ go chars
      end%pstring.
  Definition to_N (bpc : nat) (acc : N) (offset : Uint63.int) (s : t) : N :=
    (fix go acc i bpc :=
       match bpc with
       | 0 => acc
       | S bpc =>
           let acc := (acc*256 + (Z.to_N $ to_Z $ PrimString.get s i))%N in
           go acc (i + 1)%uint63 bpc
       end) acc offset bpc.

  Definition to_list_N'
    (bpc : nat)
    (incr : int)
    (s : t) :
    forall (len : nat) (offset : int), list N :=
    (fix go len i :=
       match len with
       | 0 => []
       | S len =>
           let c := to_N bpc 0 i s in
           let i := (i + incr)%uint63 in
           c :: go len i
       end
    ).

  (** [to_list_N bpc s] converts the encoded string [s] back to integers, i.e.
      it produces [num_bytes_N s / bpc] many characters in integer form. *)
  Definition to_list_N bpc s :=
    let incr := of_Z $ Z.of_nat bpc in
    let plen := num_bytes_int s in
    let len := Z.to_nat $ to_Z $ (div plen incr) in
    to_list_N' bpc incr s len 0.

  (* upstream *)
  Lemma pstring_app_empty_l s : ("" ++ s = s)%pstring.
  Proof.
    apply PString.to_list_inj.
    apply PString.to_list_cat.
    have:= PString.valid_length s.
    cbn [PrimString.length].
    lia.
  Qed.

  (* true but useless *)
  Lemma to_N_app_l (bpc : nat) acc offset (s1 s2 : t) :
    (0 <= Z.of_nat bpc + to_Z offset <= (to_Z $ PrimString.length s1))%Z ->
    to_N bpc acc offset (s1 ++ s2)%pstring =
      to_N bpc acc offset s1.
  Proof.
    elim: bpc acc offset s1 s2 => [|bpc IH] acc offset s1 s2 Hoff.
    - done.
    - simpl.
      rewrite IH.
      + f_equal. f_equal. f_equal. f_equal.
        rewrite PString.cat_get_spec_l; [done|lia].
      + rewrite add_spec Z.mod_small; lia.
  Qed.

  (* true but useless *)
  Lemma to_N_app_r (bpc : nat) acc offset (s1 s2 : t) :
    ((to_Z $ PrimString.length s1) <= to_Z offset)%Z ->
    (Z.of_nat bpc + to_Z offset < to_Z PrimString.max_length)%Z ->
    to_N bpc acc offset (s1 ++ s2)%pstring =
      to_N bpc acc (offset - PrimString.length s1) s2.
  Proof.
    elim: bpc acc offset s1 s2 => [|bpc IH] acc offset s1 s2 Hoff1 Hoff2.
    - done.
    - simpl.
      (* case: (Z_lt_ge_dec (bpc + to_Z (offset) + 1) (to_Z (PrimString.max_length))%Z); intros. *)
      rewrite IH.
      + f_equal.
        * f_equal. f_equal. f_equal.
          rewrite PString.cat_get_spec_r; [done|lia|lia].
        * apply to_Z_inj.
          have := PString.valid_length s1.
          rewrite !(add_spec, sub_spec, Z.mod_small); lia.
        + rewrite add_spec Z.mod_small; lia.
        + rewrite add_spec Z.mod_small; lia.
  Qed.

  #[local] Arguments Nat.min : simpl nomatch.

  (* true but useless *)
  Lemma to_N_app (bpc : nat) acc offset (s1 s2 : t) :
    (Z.of_nat bpc + to_Z offset < to_Z (PrimString.length s1))%Z ->
    (to_Z (PrimString.length s1) + to_Z (PrimString.length s2) <= to_Z PrimString.max_length)%Z ->
    to_N bpc acc offset (s1 ++ s2)%pstring =
      to_N (bpc - Z.to_nat (to_Z $ PrimString.length s1))%nat (to_N bpc acc offset (s1 ++ s2)%pstring) (offset - PrimString.length s1) s2.
  Proof.
    elim: bpc acc offset s1 s2 => [|bpc IH] acc offset s1 s2 *.
    - done.
    - simpl.
      have ? := PString.valid_length s1.
      rewrite IH //; try lia; last first.
      { rewrite add_spec Z.mod_small; lia. }

      case: (Z.lt_trichotomy (Z.of_nat bpc) (to_Z (PrimString.length s1))) => [H|[H|H]].
      + have ->: (bpc - to_nat (PrimString.length s1))%nat = 0%nat by lia.
        have ->: (S bpc - to_nat (PrimString.length s1))%nat = 0%nat by lia.
        done.
      + have ->: (bpc - to_nat (PrimString.length s1))%nat = 0%nat by lia.
        simpl.
        have ->: (S bpc - to_nat (PrimString.length s1))%nat = 1%nat by lia.
        simpl.
        subst. lia.
      + lia.
  Qed.


  Lemma N_div_eucl_remainder:
    ∀ (a : N) (b : N), b ≠ 0%N → ((N.div_eucl a b).2 < b)%N.
  Proof.
    intros. unfold N.div_eucl.
    case_match; cbn; [lia|].
    case_match; cbn; [lia|].
    apply N.pos_div_eucl_remainder.
    lia.
  Qed.

  Lemma of_N_spec bpc n:
    (Z.of_nat bpc <= to_Z PrimString.max_length)%Z ->
    PrimStringAxioms.to_list (of_N bpc n) =
      List.rev (map (fun i => of_Z (Z.of_N (N.modulo (N.shiftr n (N.of_nat i * 8)) 256))) (seq 0 bpc)).
  Proof.
    elim: bpc n => [//|bpc IH] n Hb.
    cbn.
    pose (H := N.div_eucl_spec n 256). move: H.
    pose (H := N_div_eucl_remainder n 256). move: H.
    case: (N.div_eucl n 256) => [m r] /= ? ?. subst.
    rewrite PrimStringAxioms.cat_spec.
    rewrite PrimStringAxioms.make_spec.
    simpl.
    rewrite take_ge; last first.
    { rewrite length_app. rewrite IH; last lia.
      rewrite length_rev length_map length_seq.
      cbn. lia. }
    rewrite IH; last lia.
    f_equal.
    + apply rev_inj. rewrite !rev_involutive.
      have ->: (forall n, seq (S n) bpc = map S (seq n bpc)).
      { clear. elim: bpc => [|bpc IH] n; [done|by rewrite /= IH]. }
      rewrite map_map.
      apply map_ext_in_iff => i /in_seq Hi.
      rewrite Nat2N.inj_succ.
      rewrite N.mul_succ_l.
      rewrite [(_ + 8)%N]N.add_comm.
      rewrite -N.shiftr_shiftr.
      rewrite [N.shiftr _ 8]N.shiftr_div_pow2.
      have ->: ((256 * m + r) `div` 2 ^ 8 = m)%N.
      { rewrite N.mul_comm (N.div_add_l _ _ r) //.
        rewrite N.div_small; lia. }
      done.
    + f_equal. apply to_Z_inj.
      rewrite N.mul_0_l N.shiftr_0_r.
      rewrite land_spec'.
      rewrite !of_Z_spec.
      rewrite N.add_comm N.mul_comm.
      rewrite N.Div0.mod_add.
      rewrite N.mod_small; [|lia].
      rewrite Z.mod_small; [|lia].
      have ->: (to_Z 255 = (Z.ones 8))%N by done.
      rewrite Z.land_ones; [|lia].
      rewrite Z.mod_small; lia.
  Qed.

  Lemma of_N_length bpc n :
    (Z.of_nat bpc <= to_Z PrimString.max_length)%Z ->
    length (PrimStringAxioms.to_list (of_N bpc n)) = bpc.
  Proof.
    intros.
    rewrite of_N_spec //.
    by rewrite length_rev length_map length_seq.
  Qed.

  Lemma of_N_length_int bpc n :
    (Z.of_nat bpc <= to_Z PrimString.max_length)%Z ->
    PrimString.length (of_N bpc n) = of_nat bpc.
  Proof.
    intros.
    rewrite PString.length_spec_int.
    by rewrite of_N_length.
  Qed.

  Lemma to_N_spec bpc acc off s :
    (Z.of_nat bpc + to_Z off <= to_Z (PrimString.length s))%Z ->
    to_N bpc acc off s =
      foldl (fun acc r => acc * 256 + Z.to_N (to_Z r))%N acc (take bpc $ drop (Z.to_nat (to_Z off)) (PrimStringAxioms.to_list s)).
  Proof.
    elim: bpc acc off s => [//|bpc IH] acc off s Hbo.
    simpl.
    rewrite IH /=; [| |lia..].
    2: { rewrite add_spec Z.mod_small; lia. }
    have H:
      (drop (to_nat off) (PrimStringAxioms.to_list s)) =
        (PrimString.get s off) :: (drop (to_nat (off + 1)) (PrimStringAxioms.to_list s)).
    { rewrite {1}(PString.to_list_firstn_skipn_middle _ off); [|lia].
      rewrite drop_app.
      rewrite skipn_firstn_comm.
      rewrite length_take Nat.min_l; last first.
      { rewrite -PrimStringAxioms.length_spec. lia. }
      have ->: (to_nat off - to_nat off = 0)%nat by lia.
      done.
    }
    by rewrite {}H.
  Qed.

  Lemma rev_seq_cons start len :
    rev (seq start (S len)) =
      (start + len)%nat :: rev (seq start len).
  Proof.
    elim: len start => [//=|len IH] start.
    - f_equal. lia.
    - cbn.
      rewrite app_comm_cons.
      f_equal.
      specialize (IH (S start)). cbn in IH.
      rewrite IH.
      f_equal. lia.
  Qed.

  Lemma to_of_N bpc acc n :
    (Z.of_nat bpc <= to_Z PrimString.max_length)%Z ->
    to_N bpc acc 0 (of_N bpc n) =
      (acc * N.pow 256 (N.of_nat bpc) +
       N.modulo n (N.pow 256 (N.of_nat bpc)))%N.
  Proof.
    intros Hb.
    rewrite to_N_spec; last first.
    - rewrite PString.length_spec_Z. rewrite of_N_spec; [|lia].
      rewrite length_rev length_map length_seq. lia.
    - rewrite of_N_spec; [|lia].

      rewrite drop_0.
      rewrite -map_rev.
      elim: bpc acc n Hb => [|bpc IH] acc n Hb.
      + simpl.
        have ->: (256 ^ 0 = 1)%N by lia.
        rewrite N.mod_1_r. lia.
      + rewrite rev_seq_cons. simpl.
        rewrite {}IH; [|lia].
        have ->: N.pos (Pos.of_succ_nat bpc) = (1 + N.of_nat bpc)%N by lia.
        ring_simplify.
        rewrite N.pow_add_r. ring_simplify.
        rewrite N.pow_1_r. ring_simplify.
        rewrite -!N.add_assoc. f_equal.
        rewrite of_Z_spec.
        rewrite Z.mod_small.
        2: {
          split.
          * apply N2Z.is_nonneg.
          * rewrite N2Z.inj_mod N2Z.inj_shiftr.
            etrans; [apply Z_mod_lt|]; lia.
        }
        rewrite N2Z.id.
        (* rewrite N.Div0.mod_mul_r. *)
        rewrite N.shiftr_div_pow2.
        rewrite [(N.of_nat _ * 8)%N]N.mul_comm.
        rewrite N.pow_mul_r.
        have ->: (2 ^ 8 = 256)%N by done.
        move: bpc Hb (N.of_nat bpc) => _ _ b.
        rewrite !N.Div0.mod_eq.
        have ->: (256 * 256 ^ ?[x] = 2 ^ (8 * (1 + ?x)))%N.
        { intros. rewrite N.pow_mul_r. rewrite N.pow_add_r. done. }
        have ->: (256 ^ ?[x] = 2 ^ (8 * ?x))%N.
        { intros. rewrite N.pow_mul_r. done. }
        have ->: (256 = 2 ^ 8)%N by done.
        rewrite -!N.shiftr_div_pow2.
        rewrite N.shiftr_shiftr.
        have ->: (8 * b + 8 = 8 * (1 + b))%N by lia.
        rewrite {1}N.mul_sub_distr_l.
        apply N2Z.inj'.
        rewrite ?(N2Z.inj_sub,N2Z.inj_mul,N2Z.inj_add, N2Z.inj_pow).
        {
          rewrite !N.mul_add_distr_l.
          simpl.
          ring_simplify.
          f_equal.
          have <-: (8 * Z.of_N b + 8 = 8 * (1 + Z.of_N b))%Z by lia.
          rewrite Z.pow_add_r; [|lia..].
          ring_simplify.
          done.
        }
        {
        rewrite N.shiftr_div_pow2.
        by apply N.Div0.mul_div_le.
        }
        {
        rewrite N.shiftr_div_pow2.
        by apply N.Div0.mul_div_le.
        }
        {
        rewrite !N.shiftr_div_pow2.
        apply N.mul_le_mono_l.
        etrans.
        apply N.Div0.div_mul_le.
        have ->: (2^(8 * (1+b)) = (2^8)*(2^(8*b)))%N.
        { rewrite ?(N.pow_add_r, N.pow_mul_r). lia. }
        rewrite -N.Div0.div_div.
        rewrite N.mul_comm N.div_mul; lia.
        }
  Qed.

  Lemma of_list_N_spec bpc ls:
    (List.length ls * Z.of_nat bpc <= to_Z PrimString.max_length)%Z ->
    PrimStringAxioms.to_list (of_list_N bpc ls) =
      List.concat (map (fun n =>
             List.rev (map (fun i => of_Z (Z.of_N (N.modulo (N.shiftr n (N.of_nat i * 8)) 256))) (seq 0 bpc))
        ) ls).
  Proof.
    elim: ls bpc => [//|c ls IH] bpc /= Hb.
    cbn. rewrite -IH; [|lia].
    rewrite PrimStringAxioms.cat_spec.
    rewrite take_ge; last first.
    { rewrite length_app {}IH; [|lia].
      rewrite of_N_length; [|lia].
      rewrite length_concat.
      rewrite (_ : list_sum _ = length ls * bpc)%nat; [lia|].
      clear. elim: ls => [|c ls IH] //=. rewrite {}IH.
      rewrite length_rev length_map length_seq. lia.
    }
    clear IH.
    rewrite of_N_spec //.
    lia.
  Qed.


  Lemma of_list_N_length bpc ls:
    (List.length ls * Z.of_nat bpc <= to_Z PrimString.max_length)%Z ->
    to_Z (PrimString.length (of_list_N bpc ls)) = (List.length ls * bpc)%Z.
  Proof.
    intros.
    induction ls; simpl in *; [done|].
    rewrite PString.length_spec_int.
    rewrite PString.to_list_cat; last first.
    { rewrite PString.length_spec_Z of_N_length; [|lia].
      rewrite IHls; lia. }
    rewrite length_app.
    rewrite of_N_length; [|lia].
    rewrite -PrimStringAxioms.length_spec.
    rewrite {}IHls; [|lia].
    rewrite of_Z_spec Z.mod_small; lia.
  Qed.

  Lemma to_list_N'_plus bpc incr s x y off :
    (0 < bpc)%nat ->
    (to_Z incr = Z.of_nat bpc)%Z ->
    (0 <= to_Z off)%Z ->
    (Z.of_nat bpc * Z.of_nat x + to_Z off <= to_Z (PrimString.length s))%Z ->
    to_list_N' bpc incr s (x + y) off =
    to_list_N' bpc incr s (x) off ++
    to_list_N' bpc incr s (y) (off + of_nat x * of_nat bpc).
  Proof.
    elim: x bpc incr s y off => [|x IH] bpc incr s y off Hb0 Hb Hoff0 H.
    - simpl. f_equal. apply to_Z_inj.
      rewrite ?(add_spec, mul_spec) !Z.mod_small; lia.
    - simpl.
      f_equal.
      rewrite IH; [|try lia..]; last first.
      { rewrite add_spec Z.mod_small; lia. }
      { rewrite add_spec Z.mod_small; lia. }
      f_equal.
      f_equal.
      apply to_Z_inj.
      rewrite ?(add_spec, mul_spec, Z.mod_small, of_Z_spec, of_pos_rec_spec); lia.
  Qed.

  Lemma to_list_N'_spec bpc incr len off s :
    (to_Z incr = Z.of_nat bpc)%Z ->
    (Z.of_nat len * Z.of_nat bpc + to_Z off <= to_Z (PrimString.length s))%Z ->
    to_list_N' bpc incr s len off =
      map (fun ls =>
      foldl (fun acc r => acc * 256 + Z.to_N (to_Z r))%N 0%N ( ls))
        (reshape
           (repeat bpc len)
           (drop (Z.to_nat (to_Z off)) (PrimStringAxioms.to_list s))
        ).
  Proof.
    elim: len bpc incr off s => [|len IH] bpc incr off s Hb * //=.
    rewrite to_N_spec; [|lia..].
    f_equal.
    rewrite IH; [|try lia..].
    - rewrite drop_drop. repeat f_equal.
      rewrite ?(add_spec, Z.mod_small); lia.
    - rewrite ?(add_spec, Z.mod_small); lia.
  Qed.

  Lemma reshape_app {X:Type} (ls1 ls2 : list X) segs segs1 segs2 :
    segs = segs1 ++ segs2 ->
    list_sum segs1 = length ls1 ->
    reshape segs (ls1 ++ ls2) = reshape segs1 ls1 ++ reshape segs2 ls2.
  Proof.
    intros Hs Hsum. subst.
    elim: segs1 segs2 ls1 ls2 Hsum => [|x segs1 IH] segs2 ls1 ls2 Hsum.
    - case: ls1 Hsum; simpl in *; intros; [done|lia].
    - simpl in *.
      rewrite take_app drop_app.
      have ->: (x - length ls1 = 0)%nat by lia.
      rewrite take_0 drop_0 app_nil_r. f_equal.
      rewrite IH //.
      rewrite length_drop. lia.
  Qed.

  Lemma to_of_list_N (bpc : nat) ls:
    (0 < bpc)%Z ->
    (length ls * bpc ≤ to_Z (PrimString.max_length))%Z ->
    to_list_N bpc (of_list_N bpc ls) =
      map (fun c => c `mod` 256 ^ N.of_nat bpc)%N ls.
  Proof.
    elim: ls bpc => [//=|c ls IH] bpc Hbpc Hlsb.
    - rewrite /to_list_N /num_bytes_int.
      rewrite /to_list_N' /=.
      by rewrite div_spec Zdiv_0_l.
    - simpl in *. rewrite /to_list_N /=.
      rewrite to_list_N'_spec; [|try lia..]; cycle 1.
      { rewrite of_Z_spec Z.mod_small; lia. }
      { rewrite /num_bytes_int /=.
        rewrite PString.cat_length_spec.
        rewrite !PString.length_spec_int.
        rewrite div_spec.
        rewrite of_Z_spec Z.mod_small; [|lia].
        rewrite {2}[to_Z _](Z_div_mod_eq_full _ bpc).
        rewrite of_N_spec; [|lia].
        rewrite length_rev length_map length_seq.
        rewrite of_list_N_spec; [|lia].
        rewrite length_concat.
        rewrite map_map.
        setoid_rewrite length_rev.
        setoid_rewrite length_map.
        setoid_rewrite length_seq.
        rewrite (_ : list_sum _ = length ls * bpc)%nat; last first.
        { clear. induction ls; [done|rewrite /= IHls; lia]. }
        rewrite ?(min_spec, add_spec, (Z.mod_small _ wB), of_Z_spec); [|try lia..].
        rewrite Z.min_r; [|lia].
        rewrite ?(Z2Nat.inj_div, Z2Nat.inj_add, Z2Nat.inj_mul, Z2Nat.id, Z2Nat.inj_div, Nat2Z.id, Nat2Z.inj_mul); [|try lia..].
        - apply Z.add_le_mono; [lia|].
          apply Z.mod_pos. lia.
        - apply Z_div_nonneg_nonneg; lia.
      }
      rewrite PrimStringAxioms.cat_spec.
      rewrite /num_bytes_int.
      rewrite PString.length_spec_int.
      rewrite !PrimStringAxioms.cat_spec.
      rewrite !of_N_spec; [|lia].
      rewrite of_list_N_spec; [|lia].

      rewrite !(length_take, length_app,length_rev,length_map,length_seq,length_concat).
      rewrite map_map.
      (* setoid_rewrite length_rev. *)
      (* setoid_rewrite length_map. *)
      (* setoid_rewrite length_seq. *)
      rewrite (_ : list_sum _ = length ls * bpc)%nat; last first.
      { clear. induction ls; [done|rewrite /= IHls length_rev length_map length_seq; lia]. }
      rewrite !take_ge; last first.
      { rewrite !(length_app,length_rev,length_map,length_seq,length_concat).
        rewrite map_map.
        setoid_rewrite length_rev.
        setoid_rewrite length_map.
        setoid_rewrite length_seq.
        rewrite (_ : list_sum _ = length ls * bpc)%nat; last first.
        { clear. induction ls; [done|rewrite /= IHls; lia]. }
        lia.
      }
      rewrite drop_0.
      rewrite (_ : to_nat (of_nat _ / of_nat _) = S (length ls)); last first.
      { rewrite div_spec !of_Z_spec !Z.mod_small; [|lia..].
        rewrite Z2Nat.inj_div; [|lia..].
        rewrite min_r; [|lia].
        rewrite !Nat2Z.id.
        rewrite Nat.div_add; [|lia].
        rewrite Nat.div_same; lia.
      }
      cbn [repeat].
      erewrite (reshape_app _ _ _ [_]); cycle 1.
      { reflexivity. }
      { rewrite length_rev length_map length_seq. done. }
      simpl.
      rewrite -of_list_N_spec; [|lia].
      rewrite -(drop_0 (PrimStringAxioms.to_list _)).
      rewrite [in x in drop x _](_ : 0%nat = to_nat 0); [|lia].
      erewrite <-(to_list_N'_spec _ (of_nat bpc)); cycle 1.
      { rewrite of_Z_spec Z.mod_small; lia. }
      { rewrite of_list_N_length; lia. }
      unfold to_list_N in IH.
      have ->: (length ls = to_nat (num_bytes_int (of_list_N bpc ls) / of_nat bpc))%nat.
      { rewrite /num_bytes_int. rewrite div_spec.
        rewrite of_list_N_length; [|lia].
        rewrite of_Z_spec Z.mod_small; [|lia].
        rewrite Z.div_mul; lia. }
      rewrite {}IH; [|lia..].
      f_equal.
      rewrite -of_N_spec; [|lia].
      rewrite -(drop_0 (PrimStringAxioms.to_list _)).
      rewrite [in x in drop x _](_ : 0%nat = to_nat 0); [|lia].
      rewrite -to_N_spec; last first.
      { rewrite PString.length_spec_Z of_N_length; lia. }
      rewrite to_of_N; [|lia].
      lia.
  Qed.
End Encoded.

#[global] Bind Scope pstring_scope with Encoded.t.

(** String literals supporting multi-byte characters.

    A [literal_string.t] represents a string of multi-byte characters.
    Effectively it should be thought of as a compact encoding of values of type
    [list N].

    Users of [literal_string.t] should use [literal_string.to_list_N] and
    [literal_string.of_list_N] to construct and destruct these values.

    We choose the encoding captured by [to_list_N] and [of_list_N] which encodes
    using the encoding specified by the [Encoded] module above (i.e., big-endian).
 *)
Module literal_string.

  Record t : Set :=
  { bytes : PrimString.string
  ; bytes_per_char : N }.

  Definition compare : t → t → comparison :=
    fun x y =>
      match N.compare x.(bytes_per_char) y.(bytes_per_char) with
      | Eq => Encoded.compare x.(bytes) y.(bytes)
      | _ as c => c
      end.

  #[global,program]
  Instance eqdec_literal_string : EqDecision t :=
    fun x y =>
      match compare x y as c return compare x y = c -> _ with
      | Eq => fun H => left _
      | _ => fun H => right _
      end eq_refl.
  Next Obligation.
    move => [??] [??].
    rewrite /compare /Encoded.compare /=.
    case H: (N.compare _ _); try discriminate; [].
    apply N.compare_eq in H. rewrite {}H.
    by move/PString.compare_eq => ->.
  Qed.
  Next Obligation.
    move => [??] [??].
    rewrite /compare /Encoded.compare /=.
    case H: (N.compare _ _); try discriminate; [|].
    - apply N.compare_eq in H. rewrite {}H.
      move => H1 [] /PString.compare_eq. by rewrite H1.
    - move => _ [_] /N.compare_eq_iff. by rewrite H.
  Qed.
  Next Obligation.
    move => [??] [??].
    rewrite /compare /Encoded.compare /=.
    case H: (N.compare _ _); try discriminate; [|].
    - apply N.compare_eq in H. rewrite {}H.
      move => H1 [] /PString.compare_eq. by rewrite H1.
    - move => _ [_] /N.compare_eq_iff. by rewrite H.
  Qed.

  Definition bpc_of_list_N : list N → N :=
    fun bs =>
      let max := foldl N.max 1%N bs in
      ((N.log2_up (N.succ max) + 7) / 8)%N.

  Lemma foldl_max_leb a ls : (a ≤ foldl N.max a ls)%N.
  Proof.
    elim: ls a => [|b ls IH] /= a; [lia|].
    case (N.max_spec a b) => [[? ->]|[? ->]].
    - etrans; [|apply IH]. lia.
    - apply IH.
  Qed.

  Lemma bpc_of_list_N_nonneg bytes : (0 < bpc_of_list_N bytes)%N.
  Proof.
    unfold bpc_of_list_N.
    apply N.div_str_pos_iff; [lia|].
    suff: (0 < N.log2_up (N.succ $ foldl N.max 1%N bytes))%N by lia.
    have ? := foldl_max_leb 1 bytes.
    apply N.log2_up_lt_pow2; lia.
  Qed.

  Lemma bpc_of_list_N_spec bytes:
    List.Forall (fun b => b < 256^(bpc_of_list_N bytes))%N bytes.
  Proof.
    have -> : (256^(bpc_of_list_N bytes) = 2^(8 * bpc_of_list_N bytes))%N.
    { by rewrite N.pow_mul_r. }
    unfold bpc_of_list_N.
    have H1: forall a, List.Forall (fun b => b <= foldl N.max a bytes)%N bytes.
    { elim: bytes => [|b bytes IH] //= a.
      constructor; [|done].
      have := foldl_max_leb (a `max` b) bytes. lia.
    }
    apply: Forall_impl; [exact (H1 1%N)|].
    clear H1.
    have Hf := (foldl_max_leb 1%N bytes).
    have H1: (1 < foldl N.max 1 bytes + 1)%N by lia.
    move => /= b Hb.
    apply: N.le_lt_trans; [done|].
    set f := foldl N.max _ bytes.
    move: Hf. rewrite -/f. move: f => f Hf {H1 Hb}.

    case: (N.lt_trichotomy f 1) Hf => [?|[?|?]] Hf; [lia|subst; done|].

    rewrite N.log2_up_eqn; [|lia].
    rewrite (_ : N.pred (N.succ ?[x]) = ?x); [|lia].

    case: (N.log2_spec_alt f ltac:(lia)) => d [Hf1 Hf2].
    rewrite {1}Hf1.
    apply: (N.lt_le_trans _ ((2^(1 + N.log2 f)))).
    { rewrite N.pow_add_r. lia. }
    apply: N.pow_le_mono_r; [lia|].
    have ->: (N.succ ?[x] + 7 = 8 + ?x)%N by lia.
    have {2}->: (8 = 1 * 8)%N by lia.
    rewrite N.div_add_l; [|lia].
    rewrite N.mul_add_distr_l.
    rewrite {1}(N.div_mod (N.log2 f) 8); [|lia].
    have := (N.mod_bound_pos (N.log2 f) 8) ltac:(lia) ltac:(lia).
    lia.
  Qed.

  Definition of_list_N : list N → t :=
    fun bs =>
      let bpc := bpc_of_list_N bs in
      {| bytes := Encoded.of_list_N (N.to_nat bpc) bs;
         bytes_per_char := bpc |}.

  Definition to_list_N : t → list N :=
    fun v => Encoded.to_list_N (N.to_nat v.(bytes_per_char)) v.(bytes).

  (* [lengthN s] returns the length, i.e. the number of characters, of the
     literal string [s]. It accounts for strings whose length is not a multiple
     of [bytes_per_char]. *)
  Definition lengthN (s : t) : N :=
    let bpc := of_Z $ Z.of_N $ s.(bytes_per_char) in
    Z.to_N $ to_Z $
      ((PrimString.length s.(bytes) + bpc - 1) / bpc)%uint63.

  Lemma to_of_list_N bytes :
    (length bytes * Z.of_N (bpc_of_list_N bytes) ≤ Uint63.to_Z PrimString.max_length)%Z
    → to_list_N (of_list_N bytes) = bytes.
  Proof.
    intros.
    have ? := bpc_of_list_N_nonneg bytes.
    rewrite /to_list_N/of_list_N /=.
    rewrite Encoded.to_of_list_N; [|lia..].
    rewrite N2Nat.id.
    clear.
    have := bpc_of_list_N_spec bytes.
    move: (bpc_of_list_N bytes) => a H.
    induction H as [|b bytes Hb _ IH] => //=.
    rewrite {}IH.
    by rewrite N.mod_small.
  Qed.

End literal_string.
