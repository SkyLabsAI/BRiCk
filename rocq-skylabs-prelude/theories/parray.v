(*
 * Copyright (c) 2025 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bluerock.prelude.base.
Require Import bluerock.prelude.uint63.
Require Import Stdlib.Numbers.Cyclic.Int63.Uint63.
Require Import Stdlib.Array.PArray.
Require Stdlib.Lists.List.

Import Uint63.
#[local] Close Scope nat_scope.
#[local] Open Scope Z_scope.

#[global] Instance Op_max_length : ZifyClasses.CstOp max_length :=
  { TCst := 4194303%Z ; TCstInj := eq_refl }.
Add Zify CstOp Op_max_length.

#[global] Arguments leb_length [A].

Module PArray.
  Export Array.PArray.

  Section Lists.
    Context {A : Type}.
    Implicit Type a : array A.

    #[local] Definition to_list_aux a : nat -> int -> list A -> list A :=
      fix go n i acc {struct n} :=
        match n with
        | O => acc
        | S n => go n (i - 1)%uint63 (PArray.get a i :: acc)
        end.

    #[local]
    Lemma to_list_aux_P a : forall n i acc,
      to_list_aux a n i acc = List.map (fun i => PArray.get a i) (seq_int (i + 1 - of_nat n) n) ++ acc.
    Proof.
      elim => [//|n IHn] i acc.
      cbn. rewrite {}IHn.
      rewrite app_comm_cons.
      rewrite cons_middle.
      rewrite app_assoc.
      f_equal.
      have ->: (i + 1 - of_nat (S n) = i - of_nat n)%uint63 by lia.
      have ->: (i - 1 + 1 - of_nat n = i - of_nat n)%uint63 by lia.
      clear -n. revert i.
      induction n => i.
      - subst. cbn. repeat f_equal. lia.
      - cbn. f_equal.
        move: IHn => /(_ i).
        have ->: (i - of_nat (S n) + 1 = i - of_nat n)%uint63 by lia.
        done.
    Qed.

    (** *** Array -> List *)

    (** Converts the array to a list dropping the default element. *)
    Definition to_list (a : array A) : list A  :=
      let len := PArray.length a in
      to_list_aux a (Z.to_nat (Uint63.to_Z len)) (len - 1)%uint63 [].

    (** Convert an array to a list including the default element of
        the array as the first element of the list.
     *)
    Definition to_list_with_def (a : array A) : list A  :=
      PArray.default a :: to_list a.

    Lemma to_list_P a :
      to_list a = (List.map (fun i => PArray.get a i) (seq_int 0 (Z.to_nat (to_Z (PArray.length a))))).
    Proof.
      unfold to_list.
      rewrite to_list_aux_P app_nil_r.
      repeat f_equal. lia.
    Qed.

    Lemma to_list_with_def_P a :
      to_list_with_def a = PArray.default a :: (List.map (fun i => PArray.get a i) (seq_int 0 (Z.to_nat (to_Z (PArray.length a))))).
    Proof.
      unfold to_list_with_def.
      repeat f_equal. apply to_list_P.
    Qed.

    (** *** List -> Array *)

    Fixpoint of_list_aux l i a {struct l} :=
      match l with
      | x :: l =>
          let a := PArray.set a i x in
          let i := (i + 1)%uint63 in
          of_list_aux l i a
      | [] => a
      end.

    Lemma length_of_list_aux : forall l i a,
          length (of_list_aux l i a) = length a.
    Proof.
      elim => [|x l IHl] i a.
      - done.
      - by rewrite IHl length_set.
    Qed.

    Lemma default_of_list_aux : forall l i a,
          default (of_list_aux l i a) = default a.
    Proof.
      elim => [|x l IHl] i a.
      - done.
      - by rewrite IHl default_set.
    Qed.

    Lemma nth_cons {X:Type} (n : nat) (x : X) xs d :
      n > 0 ->
      nth n (x :: xs) d = nth (Nat.pred n) xs d.
    Proof. elim: n x xs => [|n IHn] x xs //=. Qed.

    Lemma get_of_list_aux {j} : forall l a i,
      (Z.of_nat (List.length l) <= to_Z (PArray.length a)) ->
      (to_Z i + Z.of_nat (List.length l) <= to_Z $ PArray.length a)%Z ->
      (of_list_aux l i a).[j] =
        if (i <=? j)%uint63 && (j <? i + of_nat (List.length l))%uint63 then
          List.nth (to_nat j - to_nat i) l a.[j]
        else
          a.[j].
    Proof.
      elim => [|x l IHl] a i; cbn -[nth] => Hl Hi.
      - by cbn; repeat first [case_decide|case_match].
      - opose proof * (IHl a.[i<-x] (i + 1)%uint63) as IHl; [rewrite length_set; lia..|].
        rewrite {}IHl.
        repeat first [case_decide|case_match];
        repeat lazymatch goal with
          | H : _ && _ = true |- _ => apply andb_true_iff in H; destruct H
          | H : _ && _ = false |- _ => apply andb_false_iff in H; destruct H
          end.
        all: try (rewrite !get_set_other; [try first [done|lia]|lia]).
        + have ->: (to_nat j - to_nat i = S (to_nat j - to_nat (i + 1)))%nat by lia.
          by rewrite nth_cons.
        + have ?: i = j by lia. subst.
          rewrite get_set_same; [|lia].
          have ->: (to_nat j - to_nat j = 0)%nat by lia.
          done.
    Qed.

    Definition of_list (default : A) (l : list A) : array A :=
      let len := of_nat (List.length l) in
      let a := PArray.make len default in
      of_list_aux l 0 a.

    Lemma length_of_list default l :
      (List.length l <= to_Z max_length)%Z ->
      length (of_list default l) = of_nat (List.length l).
    Proof.
      intros ?.
      rewrite length_of_list_aux length_make.
      case_match; lia.
    Qed.

    Lemma default_of_list def l :
      default (of_list def l) = def.
    Proof.
      by rewrite /of_list default_of_list_aux default_make.
    Qed.

    Lemma get_of_list def l i:
      (List.length l <= to_Z max_length)%Z ->
      get (of_list def l) i = nth (to_nat i) l def.
    Proof.
      intros ?.
      rewrite /of_list get_of_list_aux; last 2 first.
      { rewrite length_make. case_match; lia. }
      { rewrite length_make. case_match; lia. }
      rewrite get_make.
      case_match;
        repeat lazymatch goal with
          | H : _ && _ = true |- _ => apply andb_true_iff in H; destruct H
          | H : _ && _ = false |- _ => apply andb_false_iff in H; destruct H
          end.
      - f_equal; lia.
      - lia.
      - rewrite nth_overflow; [done|lia].
    Qed.

    Definition of_list_with_def (l : list A) : option (array A) :=
      match l with
      | default :: l => Some (of_list default l)
      | _ => None
      end.

    Lemma length_of_list_with_def l a:
      (List.length l <= to_Z max_length)%Z ->
      of_list_with_def l = Some a ->
      length a = (of_nat (List.length l) - 1)%uint63.
    Proof.
      intros Hl.
      destruct l; cbn in *; [done|] => [[<-]].
      rewrite length_of_list; lia.
    Qed.

    Lemma default_of_list_with_def l a:
      of_list_with_def l = Some a ->
      default a = nth 0 l (default a).
    Proof.
      destruct l; cbn in *; [done|] => [[<-]].
      by rewrite default_of_list.
    Qed.

    Lemma get_of_list_with_def l a i:
      of_list_with_def l = Some a ->
      (List.length l <= to_Z max_length)%Z ->
      get a i = nth (S (to_nat i)) l (default a).
    Proof.
      destruct l; cbn -[nth] in *; [done|] => [[<-]] ?.
      rewrite get_of_list; [|lia].
      by rewrite default_of_list.
    Qed.


    (* Round trip *)
    Lemma to_of_list def l :
      (List.length l <= to_Z max_length)%Z ->
      to_list (of_list def l) = l.
    Proof.
      intros.
      have Hl: List.length (to_list (of_list def l)) = List.length l.
      { rewrite to_list_P length_map seq_int_length length_of_list; lia. }
      apply: (nth_ext _ _ def def); [done|].
      rewrite Hl.
      move Hn: (List.length l) Hl H => n Hl H.
      intros i Hi.
      rewrite to_list_P.
      pose p := get (of_list def l).
      rewrite -/p.
      have {2}->: def = p (of_nat n).
      { rewrite /p get_out_of_bounds ?default_of_list // length_of_list; lia. }
      rewrite map_nth.
      rewrite length_of_list; [|lia]. rewrite Hn.
      rewrite seq_int_nth /p.
      rewrite get_of_list; [|lia].
      case_decide.
      { repeat f_equal. lia. }
      { by rewrite !nth_overflow; [|lia..]. }
    Qed.

  End Lists.


  Definition foldl_i {A B} (f : int -> A -> B -> B) (a : array A) (b : B) : B :=
    let l := length a in
    let g k '(b,i) :=
      let a := get a i in
      (f i a b, (i+1)%uint63)
    in
    let '(res,_) :=
      nat_rect
        (fun _ => B * int)%type
        (b, 0%uint63)
        g
        (Z.to_nat (Uint63.to_Z (l)))
    in
    res.

  Definition foldr_i {A B} (f : int -> A -> B -> B) (a : array A) (b : B) : B :=
    let l := length a in
    let g k '(b,i) :=
      let a := get a (l - i - 1)%uint63 in
      (f i a b, (i+1)%uint63)
    in
    let '(res,_) :=
      nat_rect
        (fun _ => B * int)%type
        (b, 0%uint63)
        g
        (Z.to_nat (Uint63.to_Z (l)))
    in
    res.

  Lemma default_get {A} (a : array A) : default a = a.[length a].
  Proof. rewrite get_out_of_bounds //. lia. Qed.

  (* [eq_dec] implementation.
    It checks [length], then [default], then the contents.
    This is optimal for (in)equality checks. *)
  Section EqDec.
    Context `{EqDecision A}.
    Implicit Type a : array A.

    #[local] Unset Program Cases.
    #[program]
    Fixpoint eq_dec_partial a1 a2 (n : nat) {struct n} :
      {(forall m : int, (0 <= to_Z m < n)%Z -> get a1 m = get a2 m)} + {a1 <> a2} :=
      match n with
      | O => left _
      | S n =>
          match decide (get a1 (of_Z (Z.of_nat n)) = get a2 (of_Z (Z.of_nat n))) with
          | right Hm => right _
          | left Hm =>
              match eq_dec_partial a1 a2 n with
              | left Hr => left _
              | right Hr => right _
              end
          end
      end.
    Next Obligation. lia. Qed.
    Next Obligation.
      intros.
      case: (decide (to_Z m < n)%Z) => ?.
      - apply: Hr; lia.
      - clear Hr. by have <- : of_nat n = m by lia.
    Qed.
    Next Obligation.
      intros ** ?; subst. now auto.
    Qed.
    Next Obligation.
      intros ** ?; subst. now auto.
    Qed.

    #[program]
    Definition eq_dec a1 a2 : {a1 = a2} + {a1 <> a2} :=
      let s1 := PArray.length a1 in
      let s2 := PArray.length a2 in
      match eqs s1 s2 with
      | right H => right _
      | left H =>
        let d1 := PArray.default a1 in
        let d2 := PArray.default a2 in
        match decide (d1 = d2) with
        | right H => right _
        | left H =>
          let n := s1 in
          match eq_dec_partial a1 a2 (Z.to_nat (to_Z n)) with
          | right _ => right _
          | left H => left _
          end
        end
      end.
    Next Obligation.
      intros.
      apply PArray.array_ext.
      + auto.
      + intros i.
        clear -H.
        intros Hi%ltb_spec.
        assert (E : i = of_Z (Z.of_nat (Z.to_nat (to_Z i)))).
        { rewrite Znat.Z2Nat.id.
          - rewrite of_to_Z. now auto.
          - rewrite <-to_Z_0.
            pose proof (to_Z_bounded i).
            now auto.
        }
        specialize (H i).
        apply H.
        lia.
      + now auto.
    Qed.
    Next Obligation.
      intros **; subst; now auto.
    Qed.
    Next Obligation.
      intros ** ?; subst; now auto.
    Qed.
    Next Obligation.
      intros ** ?; subst; now auto.
    Qed.

    #[global] Instance array_eqdec : EqDecision (@array A) := eq_dec.
  End EqDec.

End PArray.
