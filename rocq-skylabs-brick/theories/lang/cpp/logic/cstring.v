(*
 * Copyright (C) 2019-2024 BlueRock Security, Inc.

 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import Stdlib.ZArith.BinInt.
Require Import Stdlib.Lists.List.
Require Export Stdlib.Strings.Ascii.

Require Import bluerock.iris.extra.proofmode.proofmode.

Require Import bluerock.prelude.stdpp_ssreflect.
Require Import bluerock.prelude.bytestring.
Require Import bluerock.prelude.base.
Require Import bluerock.iris.extra.bi.prelude.
Require Import bluerock.iris.extra.bi.observe.
Require Import bluerock.lang.cpp.semantics.values.
Require Import bluerock.lang.cpp.logic.arr.
Require Import bluerock.lang.cpp.logic.heap_pred.
Require Import bluerock.lang.cpp.logic.mpred.
Require Import bluerock.lang.cpp.logic.zstring.

Import ChargeNotation.
#[local] Open Scope Z_scope.

#[local] Set Printing Coercions.

(**
TODO: Why does <<ascii>> come up, as opposed to <<Byte.byte>> or
<<N>>? We no longer need <<ascii>> to relate byte strings to <<list
N>>.
*)

Section Cruft.
  (** TODO: Use <<Inj>> *)
  Lemma N_of_ascii_inj:
    forall a a',
      N_of_ascii a = N_of_ascii a' <->
      a = a'.
  Proof.
    move=> a a'; split; move=> Heq;
      by [ rewrite -(ascii_N_embedding a) Heq ascii_N_embedding
         | subst].
  Qed.

  (** TODO: Use <<fmap_take>> *)
  Lemma map_take :
    forall {A B} (f : A -> B) (l : list A) (n : nat),
      map f (take n l) = take n (map f l).
  Proof.
    intros *; generalize dependent n;
      induction l as [| a l' IHl];
      intros [| n]; try reflexivity.
    simpl; f_equal; by apply IHl.
  Qed.

  (** TODO: Can we eliminate reliance on <<nth_error>>? *)
  Lemma lookup_nth_error :
    forall {A} (l : list A) (n : nat),
      l !! n = nth_error l n.
  Proof.
    intros *; generalize dependent n; induction l as [| a l' IHl]; intro n.
    - destruct n; by simpl in *.
    - destruct n; simpl in *; [done |].
      by apply IHl.
  Qed.
End Cruft.

(** * [cstring]s

    [cstring]s reflect the "string literal" which backs null-terminated strings
    in C++. These Coq-strings DO NOT include the null-terminator.
 *)
Module cstring.
  Import zstring.

  Definition t := BS.t.
  Bind Scope bs_scope with t.

  (* TODO: Prove equivalent to
  [BS.bytes_to_string (take (List.length zs - 1) zs)]

  TODO: <<ascii> here seems to be a detour.
  *)
  Definition _from_zstring (zs : zstring.t) : cstring.t :=
    BS.parse (map (byte_of_ascii ∘ ascii_of_N)
                  (take (List.length zs - 1) zs)).
  #[global] Arguments ascii_of_pos _%_positive_scope /.
  #[global] Arguments _from_zstring !zs /.
  Notation from_zstring zs := (_from_zstring zs%Z).

  (* We provide weak sealing of [to_zstring] while leaving [from_zstring] open to
     simplification to ensure that we end up with strings in our context rather
     than lists of [Z]s.
   *)
  Definition _to_zstring' (cstr : cstring.t) (l : list Byte.byte) : zstring.t :=
    map (N_of_ascii ∘ ascii_of_byte) (BS.print cstr ++ l).
  #[global] Arguments BS.print !b%_bs /.

  #[global] Arguments _to_zstring' !cstr !l /.
  Notation to_zstring' cstr l := (_to_zstring' cstr l%byte).

  Definition to_zstring (cstr : cstring.t) : zstring.t := to_zstring' cstr ["000"].
  #[global] Arguments to_zstring cstr : simpl never.

  (* TODO: upstream these instances somewhere? *)
  #[global] Instance N_of_ascii_inj: Inj eq eq N_of_ascii.
  Proof. intros ??. apply N_of_ascii_inj. Qed.
  #[global] Instance byte_of_ascii_of_byte :
    Cancel eq byte_of_ascii ascii_of_byte.
  Proof. intros ?. apply byte_of_ascii_of_byte. Qed.
  #[global] Instance ascii_of_byte_of_ascii :
    Cancel eq ascii_of_byte byte_of_ascii.
  Proof. intros ?. apply ascii_of_byte_of_ascii. Qed.
  #[global] Instance ascii_of_byte_inj : Inj eq eq ascii_of_byte :=
    cancel_inj.
  #[global] Instance byte_of_ascii_inj : Inj eq eq byte_of_ascii :=
    cancel_inj.

  #[global] Instance to_zstring_inj : Inj eq eq cstring.to_zstring.
  Proof.
    rewrite /to_zstring/_to_zstring' =>x y /(inj (map _)) => /(inj (.++ _)).
    exact: inj.
  Qed.

  (* Use [rewrite to_zstring_unfold/=] to reduce away a [to_zstring] application to a
     concrete string.
   *)
  Lemma to_zstring_unfold (cstr : cstring.t) :
    to_zstring cstr = Unfold _to_zstring' (Unfold to_zstring (to_zstring cstr)).
  Proof. by rewrite /to_zstring. Qed.

  Remark to_zstring_unfold_EmptyString :
      to_zstring "" = [0%N].
  Proof. by intros *; rewrite !to_zstring_unfold/=. Qed.

  Lemma to_zstring_unfold_String :
    forall (b : Byte.byte) (cstr : cstring.t),
      to_zstring (BS.String b cstr) =
      (N_of_ascii ∘ ascii_of_byte $ b) :: to_zstring cstr.
  Proof. by intros *; rewrite !to_zstring_unfold/=. Qed.

  Section from_zstring_to_zstring_Theory.
    Lemma from_to_zstring (cstr : t) : from_zstring (to_zstring cstr) = cstr.
    Proof.
      unfold from_zstring, to_zstring;
        rewrite map_take map_map
                length_map length_app
                Nat.add_sub/=.
      set f := fun x => byte_of_ascii _.
      have ->: forall l, map f l = l.
      { by induction l => //=; rewrite /f /= IHl ascii_N_embedding byte_of_ascii_of_byte. }
        by rewrite take_app_length BS.print_parse_inv.
    Qed.

    Lemma to_from_zstring {σ : genv}
          (zs : zstring.t)
          (H : zstring.WF char_type.Cchar zs) :
      to_zstring (from_zstring zs) = zs.
    Proof.
      have X : List.Forall (fun c => has_type_prop (Vchar c) Tchar) zs by
        rewrite /_WF in H; naive_solver.
      induction zs. 1: exfalso; by eapply not_WF_nil.
      unfold from_zstring, to_zstring, to_zstring' in *; simpl in *.
      rewrite -> BS.parse_print_inv in *.
      replace ["000"%byte] with (map (byte_of_ascii ∘ ascii_of_N) [0%N])
        in IHzs by reflexivity; rewrite -map_app in IHzs.
      destruct zs; simpl in *.
      - apply WF_singleton_inj in H; by subst.
      - rewrite -len0_take in IHzs; [| by (simpl; lia) |]; simpl in *.
        + inversion X; apply WF_cons in H; subst. 2: {
            apply WFs_equiv in H; inversion H as [? [H' [? ?]]].
            specialize (H1 0%nat
                           ltac:(rewrite !strlen_cons;
                                 pose proof (strlen_lowerbound zs);
                                 by lia))
              as [a'' [H'' ?]]; simpl in *.
            inversion H''; by subst.
          }
          rewrite -{2}IHzs; auto; f_equal.
          * apply has_type_prop_char in H2.
            rewrite ascii_of_byte_of_ascii N_ascii_embedding; eauto.
            simpl in H2. destruct H2 as [?[Hchar?]].
            inversion Hchar; subst. lia.
          * rewrite map_app; rewrite -> map_map in *; simpl in *.
(*            set f := fun x => Z.of_N _. *)
            assert (length zs = 0 \/ length zs <> 0)%nat
              as [Hlen | Hlen] by lia.
            -- apply nil_length_inv in Hlen; subst; simpl in *.
               apply WF_singleton_inj in H; by subst.
            -- rewrite map_map IHzs; auto.
               destruct (length zs) eqn:Hlen'=> //=.
               f_equal.
               ++ inversion H3; apply has_type_prop_char in H4;
                    rewrite /bitsize.bound/= in H4; subst.
                  destruct H4 as [?[Hchar?]].
                  inversion Hchar; subst.
                    rewrite ascii_of_byte_of_ascii N_ascii_embedding;
                    by lia.
               ++ rewrite map_take -take_S_r.
                  ** rewrite -map_take -Hlen' firstn_all.
                     rewrite /=.
                     under map_ext_in => x HIn. 1: {
                       inversion H3.
                       rewrite -> (@List.Forall_forall _ _ zs) in H5.
                       specialize (H5 x HIn).
                       apply has_type_prop_char in H5; rewrite /bitsize.bound/= in H5.
                       inversion H5 as [?[Hchar?]]; inversion Hchar;
                       rewrite -> ascii_of_byte_of_ascii, N_ascii_embedding by lia.
                       over.
                     }
                     by rewrite map_id.
                  ** apply WFs_equiv in H; inversion H as [Hhead [Hty [Hnonzero Hnull]]].
                     assert (Z.of_nat (S n0) = strlen (n :: zs)) as Hn
                       by (unfold strlen, size; rewrite length_cons Hlen'; lia).
                     specialize (Hnull (S n0) Hn); simpl in Hnull.
                     rewrite -Hnull.
                     under map_ext_in => x HIn. 1: {
                       inversion H3.
                       rewrite -> (@List.Forall_forall _ _ zs) in H5.
                       specialize (H5 x HIn).
                       apply has_type_prop_char in H5; rewrite /bitsize.bound/= in H5.
                       destruct H5 as [?[Hchar?]]; inversion Hchar; subst.
                       rewrite /=.
                       rewrite -> ascii_of_byte_of_ascii, N_ascii_embedding by lia.
                       over.
                     }
                     rewrite map_id.
                     by apply lookup_nth_error.
          * assumption.
        + apply WFs_equiv in H; inversion H as [Hhead [Hty [Hbody Hnull]]].
          intros i Hi.
          assert (Z.of_nat (S i) = strlen (a :: n :: zs)) as Hi'
            by (unfold strlen, size in *; simpl in *; lia).
          specialize (Hnull (S i) Hi').
          by simpl in Hnull.
    Qed.

    Lemma to_zstring_singleton_contra :
      forall (b : Byte.byte) (cstr : cstring.t),
        to_zstring (BS.String b cstr) = [0%N] ->
        False.
    Proof.
      intros * H; rewrite to_zstring_unfold/= in H.
      inversion H.
      rewrite map_app/= in H2.
      eapply app_cons_not_nil; eauto.
    Qed.

    Lemma to_zstring_append :
      forall (cstr cstr' : t),
        to_zstring (cstr ++ cstr') =
        to_zstring' cstr [] ++ to_zstring cstr'.
    Proof.
      intros. rewrite /to_zstring/_to_zstring'.
      by rewrite BS.print_append !map_app right_id_L !assoc_L.
    Qed.

    Lemma from_zstring_to_zstring_swap {σ : genv} :
      forall (zs : zstring.t) (cstr : t),
        zstring.WF char_type.Cchar zs ->
        zs = to_zstring cstr <-> cstr = from_zstring zs.
    Proof.
      intros * HWF; split; intro; subst.
      - by rewrite from_to_zstring.
      - by rewrite to_from_zstring.
    Qed.
  End from_zstring_to_zstring_Theory.

  (* [size] reflects the in-memory footprint of the null-terminated string (i.e. the
     length is one greater than that of the [cstring.t]).
   *)
  Definition size (cstr : t) := zstring.size (to_zstring cstr).
  #[global] Arguments size cstr : simpl never.

  (* [strlen] mirrors the behavior of the standard-library function of the same name
     (i.e. the length DOES NOT include the null-terminator).
   *)
  Definition strlen (cstr : t) := zstring.strlen (to_zstring cstr).
  #[global] Arguments size cstr : simpl never.

  Definition WF {σ : genv} (cstr : t) : Prop := zstring.WF char_type.Cchar (to_zstring cstr).
  #[global] Arguments WF {σ} cstr : simpl never.

  Definition WF' {σ : genv} (cstr : t) : Prop := zstring.WF' char_type.Cchar (to_zstring cstr).
  #[global] Arguments WF' {σ} cstr : simpl never.

  Section WF_Theory.
    Context {σ : genv}.
    Remark WF_nil : WF "".
    Proof.
      rewrite /WF to_zstring_unfold/=; unfold zstring.WF.
      exists []; split.
      - by rewrite app_nil_l.
      - split; [intro CONTRA; by inversion CONTRA |].
        repeat constructor. apply has_type_prop_char_0.
    Qed.

    Lemma WF_string_inj :
      forall (b : Byte.byte) (s : t),
        WF (BS.String b s) ->
        b <> "000"%byte.
    Proof.
      intros * HWF; destruct (byte_eq_dec b "000"%byte);
        try subst; last by done.
      intros _; destruct s; intros *; move: HWF.
      - rewrite /WF to_zstring_unfold/=; unfold zstring.WF.
        intros [zs [Hzs [Hin Hty]]].
        destruct zs; simpl in *; inversion Hzs.
        apply Hin; subst; simpl in *; by left.
      - rewrite /WF to_zstring_unfold/=; unfold zstring.WF.
        intros [zs [Hzs [Hin Hty]]].
        destruct zs; simpl in *; inversion Hzs.
        apply Hin; subst; simpl in *; by left.
    Qed.

    Lemma to_zstring_WF :
      forall (cstr : t),
        WF cstr <-> zstring.WF char_type.Cchar (to_zstring cstr).
    Proof. done. Qed.

    Lemma to_zstring_WF_cons_shrink :
      forall (b : Byte.byte) (cstr : t),
        b <> "000"%byte ->
        zstring.WF char_type.Cchar (to_zstring (BS.String b cstr)) ->
        zstring.WF char_type.Cchar (to_zstring cstr).
    Proof.
      move=> b cstr Hb Hzstring; generalize dependent b;
        induction cstr as [| b' cstr' IHcstr']; intros.
      - unfold zstring.WF, to_zstring, to_zstring'.
        exists []; simpl; intuition.
        repeat constructor. apply has_type_prop_char_0.
      - unfold zstring.WF, to_zstring in Hzstring; simpl in Hzstring;
          unfold zstring.WF, to_zstring, _to_zstring';
          destruct Hzstring as [zs [Hzstring [Hnonzero Hforall]]];
          fold (to_zstring cstr') in *.
        do 2 (destruct zs; inversion Hzstring); rewrite -> H4 in *.
        + exists []; split; rewrite /BS.print; fold (BS.print cstr').
          * by rewrite -app_comm_cons/= H4.
          * rewrite map_app/= in H4; exfalso; eapply app_cons_not_nil; eauto.
        + rewrite /BS.print; fold (BS.print cstr'); rewrite -app_comm_cons/=.
          rewrite H3; exists (n0 :: zs); subst; split; [rewrite -> H4 in *; by reflexivity | ].
          split.
          * intro CONTRA; apply Hnonzero; simpl in *; intuition.
          * rewrite {}H4.
            inversion Hforall; subst.
            inversion H4; subst.
            constructor; auto.
    Qed.

    Lemma to_zstring_WF_cons_grow :
      forall (b : Byte.byte) (cstr : t),
        b <> Byte.x00 ->
        zstring.WF char_type.Cchar (to_zstring cstr) ->
        zstring.WF char_type.Cchar (to_zstring (BS.String b cstr)).
    Proof.
      move=> b cstr Hb Hzstring;
        unfold zstring.WF in Hzstring;
        unfold zstring.WF, to_zstring, to_zstring';
        fold (to_zstring' cstr ["000"]) in *;
        fold (to_zstring cstr) in *;
        destruct Hzstring as [zs [Hzstring [Hnonzero Hforall]]].
      rewrite /BS.print; fold (BS.print cstr); rewrite -app_comm_cons/= map_app/=.
      match goal with
      | |- context[_ :: ?zs ++ _] =>
        exists (N_of_ascii (ascii_of_byte b) :: zs); split;
          [by rewrite app_comm_cons | ]
      end.
      split. 2: {
        constructor.
        - apply has_type_prop_char. simpl.
          generalize (N_ascii_bounded (ascii_of_byte b)).
          intros. eexists; split; eauto.
        - unfold to_zstring, to_zstring' in Hforall.
          by rewrite map_app/= in Hforall.
      }
      intro CONTRA; inversion CONTRA. 1: {
        rewrite /ascii_of_byte/N_of_ascii/N_of_digits in H;
          repeat (case_match=> //=).
        subst; exfalso; apply Hb.
        match goal with
        | H: Byte.to_bits ?b = ?cstr |- _ =>
          assert (Byte.of_bits (Byte.to_bits b) = Byte.of_bits cstr)
            as Hb'
            by (f_equal; assumption)
        end.
        rewrite Byte.of_bits_to_bits in Hb'; subst.
        revert select (Ascii _ _ _ _ _ _ _ _ = _) => H000.
        by inversion H000.
      }
      replace (BS.print cstr) with (BS.print (from_zstring (to_zstring cstr)))
        in H by (rewrite from_to_zstring//).
      rewrite Hzstring in H.
      unfold from_zstring in H.
      rewrite length_app/= Nat.add_sub take_app_length in H.
      rewrite BS.parse_print_inv in H.
      rewrite map_map in H.
      match goal with
      | H : In 0%N (map ?f ?zs) |- _ =>
        replace (map f zs) with zs in H
      end. 2: {
        under map_ext_in=> x Hin. 1: {
          assert (0 <= x <= 255) as Hx. 1: {
            clear b Hb Hnonzero CONTRA H.
            generalize dependent x; generalize dependent zs;
              induction cstr as [| b' cstr' IHcstr'];
              intros **; simpl in *.
            - assert (zs = []); subst. 1: {
                unfold to_zstring, to_zstring' in Hzstring.
                rewrite /BS.print app_nil_l/= in Hzstring.
                destruct zs=> //; inversion Hzstring.
                exfalso; eapply app_cons_not_nil; eauto.
              }
              by inversion Hin.
            - unfold to_zstring, to_zstring' in Hzstring.
              rewrite /BS.print in Hzstring; fold (BS.print cstr') in Hzstring.
              rewrite -app_comm_cons/= map_app/= app_comm_cons in Hzstring.
              apply app_inv_tail in Hzstring; subst.
              inversion Hin.
              + subst.
                pose proof N_ascii_bounded (ascii_of_byte b').
                by lia.
              + eapply IHcstr'; eauto. 2: {
                  unfold to_zstring, to_zstring'.
                  by rewrite map_app/=.
                }
                unfold to_zstring, to_zstring' in *.
                rewrite /BS.print in Hforall; fold (BS.print cstr') in Hforall.
                rewrite -app_comm_cons/= in Hforall.
                inversion Hforall; by subst.
          }

          simpl; rewrite ascii_of_byte_of_ascii N_ascii_embedding. over; lia. lia.
        }
        by rewrite map_id.
      }
      by congruence.
    Qed.

    Lemma to_zstring_WF_zero :
      forall (cstr : t),
        zstring.WF char_type.Cchar (to_zstring (BS.String Byte.x00 cstr)) ->
        cstr = ""%bs.
    Proof.
      move=> cstr Hzstring; induction cstr=> //; exfalso.
      unfold zstring.WF, to_zstring, to_zstring' in Hzstring.
      simpl in Hzstring.
      destruct Hzstring as [zs [Hzstring CONTRA]].
      destruct zs; inversion Hzstring; subst;
        apply CONTRA; by constructor.
    Qed.

    Lemma to_zstring_WF_cons :
      forall (b : Byte.byte) (cstr : t),
        b <> "000"%byte ->
        zstring.WF char_type.Cchar (to_zstring (BS.String b cstr)) <->
        zstring.WF char_type.Cchar (to_zstring cstr).
    Proof.
      split; move=> Hzstring;
        [ eapply to_zstring_WF_cons_shrink in Hzstring
        | eapply to_zstring_WF_cons_grow in Hzstring];
        by eauto.
    Qed.

    Lemma WF_to_zstring_inj :
      forall (cstr : t),
        WF cstr ->
        exists z zs,
          to_zstring cstr = z :: zs.
    Proof. move=>>; now eapply zstring.WF_nonempty_inj. Qed.

    Lemma WF_cons :
      forall (b : Byte.byte) (cstr : t),
        (b <> "000")%byte ->
        WF (BS.String b cstr) <->
        WF cstr.
    Proof. intros * Hb; rewrite /WF; by apply to_zstring_WF_cons. Qed.
  End WF_Theory.

  Section strlen_Theory.
    Remark strlen_EmptyString : (strlen "" = 0)%Z.
    Proof. rewrite /strlen/to_zstring=> //=. Qed.

    Lemma strlen_size (cstr : t) :
      strlen cstr = size cstr - 1.
    Proof. unfold strlen, size; by apply zstring.strlen_size. Qed.

    Lemma strlen_String (cstr : t) :
      forall (b : Byte.byte),
        (strlen (BS.String b cstr) = 1 + strlen cstr)%Z.
    Proof.
      induction cstr; intros; [done | ].
      rewrite IHcstr /strlen/to_zstring /=.
      by rewrite !zstring.strlen_cons.
    Qed.

    Lemma strlen_EmptyString_String_contra :
      forall (b : Byte.byte) (cstr : t),
        not (strlen (BS.String b cstr) = strlen "").
    Proof.
      intros b cstr; destruct cstr as [| b' cstr'];
        unfold strlen, zstring.strlen, zstring.size, to_zstring;
        simpl; [| destruct cstr']; by lia.
    Qed.

    Lemma strlen_String':
      forall (b : Byte.byte) (cstr : t),
        Z.to_nat (strlen (BS.String b cstr)) = S (Z.to_nat (strlen cstr)).
    Proof.
      move=> b cstr; destruct cstr as [| b' cstr'];
        unfold strlen, zstring.strlen, zstring.size, to_zstring.
      1: simpl; by lia.
      rewrite !length_map !length_app/=.
      replace ((length (BS.print cstr') + 1)%nat - 1)%Z
        with (Z.of_nat (length (BS.print cstr')))
        by lia.
      generalize (length (BS.print cstr')).
      induction n; simpl; try lia.
    Qed.

    Lemma size_app cstr cstr' : size (cstr ++ cstr') = size cstr + size cstr' - 1.
    Proof.
      have aux : ∀ cstr, zstring.size (to_zstring cstr) = zstring.size (to_zstring' cstr []) + 1.
      { clear=>cstr. rewrite /to_zstring/_to_zstring'. rewrite !map_app map_cons.
        rewrite !size_app size_cons. lia. }
      rewrite /size. rewrite to_zstring_append zstring.size_app.
      rewrite (aux cstr). lia.
    Qed.

    Lemma strlen_app :
      forall (cstr cstr' : t),
        strlen (cstr ++ cstr') = (strlen cstr + strlen cstr').
    Proof.
      intros. rewrite !strlen_size size_app. lia.
    Qed.

    Lemma strlen_nonneg : forall (cstr : t), 0 <= strlen cstr.
    Proof.
      intros cstr; destruct cstr;
        unfold strlen, zstring.strlen, zstring.size, to_zstring;
        simpl; by lia.
    Qed.

    Lemma strlen_neg_inj : forall (cstr : t), 0 = strlen cstr -> cstr = ""%bs.
    Proof.
      move=> [ | b cstr] Hlen=> //; exfalso.
      pose proof (strlen_EmptyString_String_contra b cstr) as H.
      apply H; by rewrite strlen_EmptyString.
    Qed.

    Section decisions.
      Lemma strlen_mismatch_inj : forall (cstr cstr' : t), strlen cstr <> strlen cstr' -> cstr <> cstr'.
      Proof.
        intros cstr cstr'; generalize dependent cstr';
          induction cstr; intros; simpl in *.
        - destruct cstr'; [| by (intro; discriminate)].
          rewrite strlen_EmptyString in H; by lia.
        - destruct cstr'; [by (intro; discriminate) |].
          intro; inversion H0; subst.
          by apply H.
      Qed.
    End decisions.
  End strlen_Theory.

  Section size_Theory.
    Lemma size_strlen (cstr : t) :
      size cstr = strlen cstr + 1.
    Proof. unfold strlen, size; by apply zstring.size_strlen. Qed.

    Remark size_EmptyString : (size "" = 1)%Z.
    Proof. rewrite /size/to_zstring zstring.size_unfold//=. Qed.

    Lemma size_String (cstr : t) :
      forall (b : Byte.byte),
        (size (BS.String b cstr) = 1 + size cstr)%Z.
    Proof.
      induction cstr; intros; [done | ].
      rewrite IHcstr /size/to_zstring /=.
      by rewrite !zstring.size_cons.
    Qed.

    Lemma size_EmptyString_String_contra :
      forall (b : Byte.byte) (cstr : t),
        not (size (BS.String b cstr) = size "").
    Proof.
      intros b cstr; destruct cstr as [| b' cstr'];
        unfold size, zstring.size, to_zstring;
        simpl; [| destruct cstr']; by lia.
    Qed.

    Lemma size_String':
      forall (b : Byte.byte) (cstr : t),
        Z.to_nat (size (BS.String b cstr)) = S (Z.to_nat (size cstr)).
    Proof.
      move=> b cstr; destruct cstr as [| b' cstr'];
        unfold size, zstring.size, to_zstring.
      1: simpl; by lia.
      rewrite !length_map !length_app/=.
      replace ((length (BS.print cstr') + 1)%nat - 1)%Z
        with (Z.of_nat (length (BS.print cstr')))
        by lia.
      generalize (length (BS.print cstr')).
      induction n; simpl; try lia.
    Qed.

    Lemma size_nonneg : forall (cstr : t), 0 <= size cstr.
    Proof.
      intros cstr; destruct cstr;
        unfold size, zstring.size, to_zstring;
        simpl; by lia.
    Qed.

    Lemma size_lowerbound : forall (cstr : t), 1 <= size cstr.
    Proof.
      intros cstr; destruct cstr;
        unfold size, zstring.size, to_zstring;
        simpl; by lia.
    Qed.

    Lemma size_neg_inj : forall (cstr : t), 1 = size cstr -> cstr = ""%bs.
    Proof.
      move=> [ | b cstr] Hlen=> //; exfalso.
      pose proof (size_EmptyString_String_contra b cstr) as H.
      apply H; by rewrite size_EmptyString.
    Qed.

    Section decisions.
      Lemma size_mismatch_inj : forall (cstr cstr' : t), size cstr <> size cstr' -> cstr <> cstr'.
      Proof.
        intros cstr cstr'; generalize dependent cstr';
          induction cstr; intros; simpl in *.
        - destruct cstr'; [| by (intro; discriminate)].
          rewrite size_EmptyString in H; by lia.
        - destruct cstr'; [by (intro; discriminate) |].
          intro; inversion H0; subst.
          by apply H.
      Qed.
    End decisions.
  End size_Theory.

  Section WFs_equiv_Theory.
    Context {σ : genv}.
    Lemma WFs_equiv : forall (cstr : t), WF' cstr <-> WF cstr.
    Proof. intros *; rewrite /WF/WF'; by apply zstring.WFs_equiv. Qed.

    #[local] Ltac lift_WF2WF' H :=
      intros **; rewrite -> !WFs_equiv in *; by apply H.

    Remark WF'_nil : WF' "".
    Proof. lift_WF2WF' WF_nil. Qed.

    Lemma WF'_string_inj :
      forall (b : Byte.byte) (s : t),
        WF' (BS.String b s) ->
        b <> "000"%byte.
    Proof. intros; rewrite -> !WFs_equiv in *; by eapply WF_string_inj. Qed.

    Lemma to_zstring_WF' :
      forall (cstr : t),
        WF' cstr <-> zstring.WF' char_type.Cchar (to_zstring cstr).
    Proof. done. Qed.

    Lemma to_zstring_WF'_cons_shrink :
      forall (b : Byte.byte) (cstr : t),
        b <> "000"%byte ->
        zstring._WF' char_type.Cchar (to_zstring (BS.String b cstr)) ->
        zstring._WF' char_type.Cchar (to_zstring cstr).
    Proof.
      intros **; rewrite -> zstring.WFs_equiv in *;
        by eapply to_zstring_WF_cons_shrink.
    Qed.

    Lemma to_zstring_WF'_cons_grow :
      forall (b : Byte.byte) (cstr : t),
        b <> Byte.x00 ->
        zstring.WF' char_type.Cchar (to_zstring cstr) ->
        zstring.WF' char_type.Cchar (to_zstring (BS.String b cstr)).
    Proof.
      intros **; rewrite -> zstring.WFs_equiv in *;
        by eapply to_zstring_WF_cons_grow.
    Qed.

    Lemma to_zstring_WF'_zero :
      forall (cstr : t),
        zstring.WF' char_type.Cchar (to_zstring (BS.String Byte.x00 cstr)) ->
        cstr = ""%bs.
    Proof.
      intros **; rewrite -> zstring.WFs_equiv in H;
        by eapply to_zstring_WF_zero.
    Qed.

    Lemma to_zstring_WF'_cons :
      forall (b : Byte.byte) (cstr : t),
        b <> "000"%byte ->
        zstring.WF' char_type.Cchar (to_zstring (BS.String b cstr)) <->
        zstring.WF' char_type.Cchar (to_zstring cstr).
    Proof.
      split; move=> Hzstring;
        [ eapply to_zstring_WF'_cons_shrink in Hzstring
        | eapply to_zstring_WF'_cons_grow in Hzstring];
        by eauto.
    Qed.

    Lemma WF'_to_zstring_inj :
      forall (cstr : t),
        WF' cstr ->
        exists z zs,
          to_zstring cstr = z :: zs.
    Proof. lift_WF2WF' WF_to_zstring_inj. Qed.

    Lemma WF'_cons :
      forall (b : Byte.byte) (cstr : t),
        (b <> "000")%byte ->
        WF' (BS.String b cstr) <->
        WF' cstr.
    Proof. lift_WF2WF' WF_cons. Qed.
  End WFs_equiv_Theory.

  Section with_Σ.
    Context `{Σ : cpp_logic} `{σ : genv}.

    (* The toplevel definition of [cstring.bufR]: *)
    Definition bufR (q : cQp.t) (sz : Z) (cstr : t) : Rep :=
    (* The toplevel definition of [cstring.bufR']: *)
      zstring.bufR char_type.Cchar q sz (to_zstring cstr).
    Definition bufR' (q : cQp.t) (sz : Z) (cstr : t) : Rep :=
      zstring.bufR' char_type.Cchar q sz (to_zstring cstr).

    #[global] Instance bufR_WF_observe :
      forall q (sz : Z) (zs : t),
        Observe [| WF zs |] (bufR q sz zs).
    Proof. refine _. Qed.

    #[global] Instance bufR'_WF_observe :
      forall q (sz : Z) (zs : t),
        Observe [| WF' zs |] (bufR' q sz zs).
    Proof. refine _. Qed.

    Lemma bufRs_equiv (q : cQp.t) (sz : Z) (zs : t) :
      bufR q sz zs -|- bufR' q sz zs.
    Proof. intros *; rewrite /bufR/bufR'; by apply zstring.bufRs_equiv. Qed.

    (* The toplevel definition of [cstring.R]: *)
    Definition R (q : cQp.t) (cstr : t) : Rep :=
      zstring.R char_type.Cchar q (to_zstring cstr).
    (* The toplevel definition of [cstring.R']: *)
    Definition R' (q : cQp.t) (cstr : t) : Rep :=
      zstring.R' char_type.Cchar q (to_zstring cstr).

    #[global] Instance R_WF_observe :
      forall q (zs : t),
        Observe [| WF zs |] (R q zs).
    Proof. refine _. Qed.

    #[global] Instance R'_WF'_observe :
      forall q (zs : t),
        Observe [| WF' zs |] (R' q zs).
    Proof. refine _. Qed.

    Lemma Rs_equiv :
      forall (q : cQp.t) (zs : t),
        R q zs -|- R' q zs.
    Proof. intros *; rewrite /R/R'; by apply zstring.Rs_equiv. Qed.

    Section Theory.
      #[local] Open Scope string_scope.

      Section bufR.
        #[local]
        Ltac lift_zstring_bufR2bufR H :=
          intros **; rewrite !/bufR/=; eapply H; eauto.

        Lemma bufR_nil :
          forall (q : cQp.t) (sz : Z),
            (1 <= sz)%Z ->
                arrayR Tchar (fun _ => primR Tchar q (Vchar 0)) (repeat () (Z.to_nat sz))
            |-- bufR q sz "".
        Proof.
          intros **; iIntros "rest"; rewrite /bufR/zstring.bufR.
          assert (zstring.size (to_zstring "") <= sz). 1: {
            rewrite to_zstring_unfold_EmptyString.
            rewrite zstring.size_unfold/=.
            by lia.
          }
          pose proof (iffLR (to_zstring_WF "") ltac:(apply WF_nil));
            iFrame "%"; iStopProof.
          rewrite -> to_zstring_unfold_EmptyString, zstring.size_unfold in *;
            simpl in *; clear H0.
          assert (0 < sz) as Hsz by lia.
          apply Z.lt_succ_pred in Hsz; rewrite -{}Hsz.
          rewrite -> !Z2Nat.inj_succ by lia; simpl.
          rewrite arrayR_cons arrayR_singleton; eauto.
          replace (Z.succ (Z.pred sz) - 1%nat) with (Z.pred sz) by lia.
          iIntros "[#? [head tail]]"; iFrame "#∗"; iPureIntro.
        Qed.

        (* TODO (AUTO): Investigate whether or not this hint actually fires. *)
        #[global] Instance bufR_sz_contra :
          forall (q : cQp.t) (sz : Z) (cstr : t),
            Observe2 False [| sz < size cstr |] (bufR q sz cstr).
        Proof. by lift_zstring_bufR2bufR zstring.bufR_sz_contra. Qed.

        #[global] Instance bufR_singleton :
          forall (q : cQp.t) (sz : Z) (b : Byte.byte),
            1 <= sz ->
            Observe [| b <> "000" |]%byte (bufR q sz (BS.String b ""%bs)).
        Proof.
          intros **; rewrite /bufR/Observe to_zstring_unfold_String/=; iIntros "buf".
          iDestruct (observe [| N_of_ascii (ascii_of_byte b) <> 0%N |] with "buf")
            as "%Hb". 1: {
            rewrite ascii_of_byte_via_N; rewrite -> N_ascii_embedding by (destruct b=> //).
            pose proof (zstring.bufR_singleton char_type.Cchar q sz (Byte.to_N b)).
            rewrite zstring.bufR_cons. 2: {
              rewrite ascii_of_byte_via_N N_ascii_embedding in Hb; auto.
              by (destruct b=> //).
            }
            iModIntro; iPureIntro; intro CONTRA; apply Hb; by rewrite CONTRA.
          }
        Qed.

        Lemma bufR_cons :
          forall (q : cQp.t) (sz : Z) (b : Byte.byte) (cstr : t),
            b <> "000"%byte ->
                bufR q sz (BS.String b cstr)
            -|- primR Tchar q (Vchar (N_of_ascii (ascii_of_byte b))) **
                .[Tchar ! 1] |-> bufR q (sz - 1) cstr.
        Proof.
          lift_zstring_bufR2bufR zstring.bufR_cons.
          rewrite ascii_of_byte_via_N N_ascii_embedding;
            auto; by destruct b=> //.
        Qed.

        #[global] Instance bufR_cons_cons_head_nonzero :
          forall (q : cQp.t) (sz : Z) (b b' : Byte.byte) (cstr : t),
            Observe [| b <> "000" |]%byte (bufR q sz (BS.String b (BS.String b' cstr))).
        Proof.
          intros **; rewrite /bufR/Observe !to_zstring_unfold_String/=.
          rewrite zstring.bufR_cons_cons_head_nonzero.
          iIntros "#%"; iModIntro; iPureIntro.
          intro CONTRA; apply H; by subst.
        Qed.

        (* TODO (AUTO): Fix this once we add the correct observations for arrayR *)
        #[global] Instance bufR_type_ptrR_observe :
          forall q (sz : Z) (cstr : t),
            Observe (type_ptrR Tchar) (bufR q sz cstr).
        Proof.
          intros **; rewrite /bufR/Observe/=; iIntros "zstr".
          iDestruct (observe (type_ptrR Tchar) with "zstr") as "#?".
          by iModIntro.
        Qed.

        #[global] Instance bufR_validR_end_observe :
          forall q (sz : Z) (cstr : t),
            Observe (.[Tchar ! sz] |-> validR) (bufR q sz cstr).
        Proof.
          intros **; rewrite /bufR/Observe/=; iIntros "zstr".
          iDestruct (observe (.[Tchar ! sz] |-> validR) with "zstr") as "#?".
          by iModIntro.
        Qed.

        #[global] Instance bufR_validR_inbounds_observe :
          forall q (sz : Z) (z : Z) (cstr : t),
            (0 <= z <= sz)%Z ->
            Observe (.[Tchar ! z] |-> validR) (bufR q sz cstr).
        Proof.
          intros **; rewrite /bufR/Observe/=; iIntros "zstr".
          iDestruct (observe (.[Tchar ! z] |-> validR) with "zstr") as "#?";
            last by iModIntro.
          by pose proof (zstring.bufR_validR_inbounds_observe char_type.Cchar q sz z (to_zstring cstr) H).
        Qed.
      End bufR.

      Section bufR'.
        #[local] Ltac lift_WF2WF' H :=
          intros **; rewrite -!bufRs_equiv; by apply H.

        Lemma bufR'_nil :
          forall (q : cQp.t) (sz : Z),
            (1 <= sz)%Z ->
                arrayR Tchar (fun _ => primR Tchar q (Vchar 0)) (repeat () (Z.to_nat sz))
            |-- bufR' q sz "".
        Proof. by lift_WF2WF' bufR_nil. Qed.

        (* TODO (AUTO): Investigate whether or not this hint actually fires. *)
        #[global] Instance bufR'_sz_contra :
          forall (q : cQp.t) (sz : Z) (cstr : t),
            Observe2 False [| sz < size cstr |] (bufR' q sz cstr).
        Proof. by lift_WF2WF' bufR_sz_contra. Qed.

        #[global] Instance bufR'_singleton :
          forall (q : cQp.t) (sz : Z) (b : Byte.byte),
            1 <= sz ->
            Observe [| b <> "000" |]%byte (bufR' q sz (BS.String b ""%bs)).
        Proof. by lift_WF2WF' bufR_singleton. Qed.

        Lemma bufR'_cons :
          forall (q : cQp.t) (sz : Z) (b : Byte.byte) (cstr : t),
            b <> "000"%byte ->
                bufR' q sz (BS.String b cstr)
            -|- primR Tchar q (Vchar (N_of_ascii (ascii_of_byte b))) **
                .[Tchar ! 1] |-> bufR' q (sz - 1) cstr.
        Proof. by lift_WF2WF' bufR_cons. Qed.

        #[global] Instance bufR'_cons_cons_head_nonzero :
          forall (q : cQp.t) (sz : Z) (b b' : Byte.byte) (cstr : t),
            Observe [| b <> "000" |]%byte (bufR' q sz (BS.String b (BS.String b' cstr))).
        Proof. by lift_WF2WF' bufR_cons_cons_head_nonzero. Qed.

        (* TODO (AUTO): Fix this once we add the correct observations for arrayR *)
        #[global] Instance bufR'_type_ptrR_observe :
          forall q (sz : Z) (zs : t),
            Observe (type_ptrR Tchar) (bufR' q sz zs).
        Proof. by lift_WF2WF' bufR_type_ptrR_observe. Qed.

        #[global] Instance bufR'_validR_end_observe :
          forall q (sz : Z) (zs : t),
            Observe (.[Tchar ! sz] |-> validR) (bufR' q sz zs).
        Proof. by lift_WF2WF' bufR_validR_end_observe. Qed.

        #[global] Instance bufR'_validR_inbounds_observe :
          forall q (sz : Z) (z : Z) (cstr : t),
            (0 <= z <= sz)%Z ->
            Observe (.[Tchar ! z] |-> validR) (bufR' q sz cstr).
        Proof. by lift_WF2WF' bufR_validR_inbounds_observe. Qed.
      End bufR'.

      Lemma bufR_unfold :
        forall (q : cQp.t) (sz : Z) (cstr : t),
          bufR q sz cstr -|-
          [| size cstr <= sz |] ** R q cstr **
          .[ Tchar ! size cstr] |-> arrayR Tchar (fun _ => primR Tchar q (Vchar 0))
                                           (repeat () (Z.to_nat (sz - size cstr))).
      Proof.
        intros **; split'.
        - rewrite /bufR/R; iIntros "(%&?&%&?)"; by iFrame "∗%".
        - rewrite /bufR/R; iIntros "[% [[? %] ?]]"; by iFrame "∗%".
      Qed.

      Lemma bufR'_unfold :
        forall (q : cQp.t) (sz : Z) (cstr : t),
          bufR' q sz cstr -|-
          [| size cstr <= sz |] ** R' q cstr **
          .[ Tchar ! size cstr] |-> arrayR Tchar (fun _ => primR Tchar q (Vchar 0))
                                           (repeat () (Z.to_nat (sz - size cstr))).
      Proof. intros **; rewrite -!bufRs_equiv -!Rs_equiv; by apply bufR_unfold. Qed.

      Section R.
        Lemma R_bufR_equiv :
          forall q (cstr : t),
            R q cstr ≡ bufR q (size cstr) cstr.
        Proof. intros **; rewrite /R/bufR; by apply zstring.R_bufR_equiv. Qed.

        #[local] Ltac try_lift_bufR H :=
          intros **; rewrite !R_bufR_equiv; eapply H; eauto.

        Remark R_nil :
          forall (q : cQp.t),
                arrayR Tchar (fun c => primR Tchar q (Vchar c)) [0%N]
            |-- R q "".
        Proof.
          intros *; rewrite /R !/zstring.R arrayR_singleton
                            to_zstring_unfold_EmptyString.
          iIntros "?"; iFrame "∗"; iPureIntro.
          auto with pure.
        Qed.

        #[global] Instance R_singleton :
          forall (q : cQp.t) (b : Byte.byte),
            Observe [| b <> "000" |]%byte
                    (R q (BS.String b ""%bs)).
        Proof.
          try_lift_bufR bufR_singleton.
          rewrite size_String; pose proof (size_nonneg ""); by lia.
        Qed.

        Lemma R_cons :
          forall (q : cQp.t) (b : Byte.byte) (cstr : t),
            b <> "000"%byte ->
                R q (BS.String b cstr)
            -|- primR Tchar q (Vchar (N_of_ascii (ascii_of_byte b))) **
                .[Tchar ! 1] |-> R q cstr.
        Proof.
          intros **; rewrite !R_bufR_equiv.
          replace (size cstr) with ((size (BS.String b cstr)) - 1)
            by (rewrite size_String; lia).
          by apply bufR_cons.
        Qed.

        #[global] Instance R_cons_cons_head_nonzero :
          forall (q : cQp.t) (b b' : Byte.byte) (cstr : t),
            Observe [| b <> "000" |]%byte (R q (BS.String b (BS.String b' cstr))).
        Proof. try_lift_bufR bufR_cons_cons_head_nonzero. Qed.

        (* TODO (AUTO): Fix this once we add the correct observations for arrayR *)
        #[global] Instance R_type_ptrR_observe :
          forall q (cstr : t),
            Observe (type_ptrR Tchar) (R q cstr).
        Proof. refine _. Qed.

        #[global] Instance R_validR_end_observe :
          forall q (cstr : t),
            Observe (.[Tchar ! size cstr] |-> validR) (R q cstr).
        Proof. refine _. Qed.

        #[global] Instance R_validR_end_observe' :
          forall q (cstr : t),
            Observe (.[Tchar ! strlen cstr] |-> .[Tchar ! 1] |-> validR) (R q cstr).
        Proof.
          intros *; pose proof (R_validR_end_observe q cstr).
          rewrite _offsetR_sub_sub; unfold size, strlen, zstring.size, zstring.strlen in *.
          unfold zstring.size in *.
          by replace (length (to_zstring cstr) - 1 + 1)%Z
            with (Z.of_nat (length (to_zstring cstr)))
            by lia.
        Qed.

        #[global] Instance R_validR_inbounds_observe :
          forall q (z : Z) (cstr : t),
            (0 <= z <= size cstr)%Z ->
            Observe (.[Tchar ! z] |-> validR) (R q cstr).
        Proof. refine _. Qed.

        #[local] Lemma observe_2_aux q1 q2 a1 a2 :
          (length (to_zstring a1) <= length (to_zstring a2))%nat
          -> Observe2 [| a1 = a2 |] (R q1 a1) (R q2 a2).
        Proof.
          rewrite /R/zstring.R.
          iIntros (Hlen) "[L %] [K %]".
          iDestruct (arrayR_agree_prefix _ (fun q c => primR Tchar q (Vchar c)) with "L K") as %Heq;
            first done;
            iIntros "!>"; iPureIntro.
          by apply: to_zstring_inj; apply: zstring.WF_eq_prefix_eq.
        Qed.

        #[global] Instance observe_2 q1 q2 a1 a2 :
          Observe2 [| a1 = a2 |] (R q1 a1) (R q2 a2).
        Proof.
          case: (bool_decide_reflect
                   (length (cstring.to_zstring a1) <= length (cstring.to_zstring a2))%nat).
          - exact: observe_2_aux.
          - rewrite -Nat.lt_nge eq_comm=>/Nat.lt_le_incl ?.
            symmetry. exact: observe_2_aux.
        Qed.

      End R.

      Section R'.
        #[local] Ltac lift_WF2WF' H :=
          intros **; rewrite -!Rs_equiv; by apply H.

        Lemma R'_bufR_equiv :
          forall q (cstr : t),
            R' q cstr ≡ bufR' q (size cstr) cstr.
        Proof. intros **; rewrite /R'/bufR'; by apply zstring.R'_bufR'_equiv. Qed.

        #[local] Ltac try_lift_bufR H :=
          intros **; rewrite !R_bufR_equiv; eapply H; eauto.

        Remark R'_nil :
          forall (q : cQp.t),
                arrayR Tchar (fun c => primR Tchar q (Vchar c)) [0%N]
            |-- R' q "".
        Proof. lift_WF2WF' R_nil. Qed.

        #[global] Instance R'_singleton :
          forall (q : cQp.t) (b : Byte.byte),
            Observe [| b <> "000" |]%byte
                    (R' q (BS.String b ""%bs)).
        Proof. lift_WF2WF' R_singleton. Qed.

        Lemma R'_cons :
          forall (q : cQp.t) (b : Byte.byte) (cstr : t),
            b <> "000"%byte ->
                R' q (BS.String b cstr)
            -|- primR Tchar q (Vchar (N_of_ascii (ascii_of_byte b))) **
                .[Tchar ! 1] |-> R' q cstr.
        Proof. lift_WF2WF' R_cons. Qed.

        #[global] Instance R'_cons_cons_head_nonzero :
          forall (q : cQp.t) (b b' : Byte.byte) (cstr : t),
            Observe [| b <> "000" |]%byte (R' q (BS.String b (BS.String b' cstr))).
        Proof. lift_WF2WF' R_cons_cons_head_nonzero. Qed.

        (* TODO (AUTO): Fix this once we add the correct observations for arrayR *)
        #[global] Instance R'_type_ptrR_observe :
          forall q (cstr : t),
            Observe (type_ptrR Tchar) (R' q cstr).
        Proof. lift_WF2WF' R_type_ptrR_observe. Qed.

        #[global] Instance R'_validR_end_observe :
          forall q (zs : t),
            Observe (.[Tchar ! size zs] |-> validR) (R' q zs).
        Proof. lift_WF2WF' R_validR_end_observe. Qed.

        #[global] Instance R'_validR_end_observe' :
          forall q (zs : t),
            Observe (.[Tchar ! strlen zs] |-> .[Tchar ! 1] |-> validR) (R' q zs).
        Proof. lift_WF2WF' R_validR_end_observe'. Qed.

        #[global] Instance R'_validR_inbounds_observe :
          forall q (z : Z) (cstr : t),
            (0 <= z <= size cstr)%Z ->
            Observe (.[Tchar ! z] |-> validR) (R' q cstr).
        Proof. lift_WF2WF' R_validR_inbounds_observe. Qed.
      End R'.

      Lemma R_unfold :
        forall (q : cQp.t) (cstr : t),
              R q cstr
          -|- arrayR Tchar (fun c => primR Tchar q (Vchar c)) (to_zstring cstr) ** [| WF cstr |].
      Proof. intros **; split'; by rewrite /R. Qed.

      Lemma R'_unfold :
        forall (q : cQp.t) (cstr : t),
              R' q cstr
          -|- arrayR Tchar (fun c => primR Tchar q (Vchar c)) (to_zstring cstr) ** [| WF' cstr |].
      Proof. intros **; split'; by rewrite /R'. Qed.

      Section Extra.
        Lemma R_to_zstringR (q : cQp.t) (cstr : t) : R q cstr |-- zstring.R char_type.Cchar q (to_zstring cstr).
        Proof. by []. Qed.

        Lemma R_from_zstringR (q : cQp.t) (zs : zstring.t) :
          zstring.R char_type.Cchar q zs |-- R q (from_zstring zs).
        Proof.
          iIntros "R";
            iDestruct (observe [| zstring.WF char_type.Cchar zs |] with "R") as "%WF";
            iStopProof.
          rewrite zstring.R_has_type_prop; iIntros "[? %]".
          rewrite /R to_from_zstring //.
        Qed.
      End Extra.
    End Theory.
  End with_Σ.
End cstring.

Require Import bluerock.lang.cpp.logic.core_string.

Section core_string.
  Context `{Σ : cpp_logic} {σ : genv}.

  Lemma string_bytesR_zstringR str q :
    zstring.WF char_type.Cchar (literal_string.to_list_N str ++ [0%N]) ->
    string_bytesR char_type.Cchar q str -|- zstring.R char_type.Cchar q (literal_string.to_list_N str ++ [0]%N).
  Proof.
    intros HWF.
    apply Rep_equiv_at => p.
    rewrite /zstring.R string_bytesR.unlock /= _at_sep _at_only_provable.
    rewrite only_provable_True // right_id; f_equiv.
    move: (literal_string.to_list_N _) HWF => bytes HWF.
    elim: bytes HWF => [|b bs IH] /= HWF.
    by rewrite !(arrayR_cons, arrayR_nil) !N_to_char_Cchar_eq.
    move: HWF => /zstring.WF_cons' [_ [/has_type_prop_char' /= Hbt Hbs]].
    rewrite !(arrayR_cons, arrayR_nil) -IH ?N_to_char_Cchar_eq //; lia.
  Qed.

  Lemma string_bytesR_cstringR str q :
    zstring.WF char_type.Cchar (literal_string.to_list_N str ++ [0%N]) ->
    string_bytesR char_type.Cchar q str -|- cstring.R q (cstring._from_zstring (literal_string.to_list_N str ++ [0%N])).
  Proof.
    intros HWF.
    by rewrite string_bytesR_zstringR // /cstring.R cstring.to_from_zstring.
  Qed.
End core_string.
