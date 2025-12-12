(*
 * Copyright (c) 2020-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import Stdlib.Lists.List.
Require Import Stdlib.NArith.NArith.
Require Import Stdlib.Structures.OrderedType.
Require Import Stdlib.micromega.Lia.
Require Stdlib.Strings.Byte.
Require Import bluerock.prelude.base.
Import ListNotations.

(** Bytestring core definitions. Depends only on the stdlib, and could in
principle be upstreamed.

TODO: Some stdpp dependencies have crept in. Move them out, making
this file compile without <<bluerock.prelude.base>>.
*)
#[local] Set Default Proof Using "Type".

Definition byte_parse (b : Byte.byte) : Byte.byte := b.
Definition byte_print (b : Byte.byte) : Byte.byte := b.

(** comparison *)
Definition byte_cmp (a b : Byte.byte) : comparison :=
  N.compare (Byte.to_N a) (Byte.to_N b).
#[global] Instance byte_compare : Compare Byte.byte := byte_cmp.

Delimit Scope byte_scope with byte.
String Notation Byte.byte byte_parse byte_print : byte_scope.

Bind Scope byte_scope with Byte.byte.

Lemma byte_cmp_refl a : byte_cmp a a = Eq.
Proof. intros. apply N.compare_refl. Qed.

Lemma byte_to_N_inj x y : Byte.to_N x = Byte.to_N y <-> x = y.
Proof.
  split. 2: now intros ->.
  intros Heq.
  enough (Some x = Some y) as [= ->] by easy.
  do 2 rewrite <- Byte.of_to_N.
  now rewrite Heq.
Qed.

Module OT_byte <: OrderedType.OrderedType with Definition t := Byte.byte.
  Definition t := Byte.byte.
  Definition eq := fun l r => byte_cmp l r = Eq.
  Definition lt := fun l r => byte_cmp l r = Lt.
  Theorem eq_refl (x : t) : eq x x.
  Proof.
    intros; apply N.compare_refl.
  Qed.
  Theorem eq_sym (x y : t) : eq x y -> eq y x.
  Proof.
    intros Hxy. eapply N.compare_eq in Hxy. unfold eq, byte_cmp.
    rewrite Hxy. apply eq_refl.
  Qed.
  Theorem eq_trans (x y z : t) : eq x y -> eq y z -> eq x z.
  Proof.
    intros Hxy Hyz. eapply N.compare_eq in Hxy. eapply N.compare_eq in Hyz.
    unfold eq, byte_cmp. rewrite -> Hxy, Hyz.
    apply eq_refl.
  Qed.
  Theorem lt_trans (x y z : t) : lt x y -> lt y z -> lt x z.
  Proof.
    unfold lt, byte_cmp. rewrite ->!N.compare_lt_iff.
    lia.
  Qed.
  Theorem lt_not_eq (x y : t) : lt x y -> ~ eq x y.
  Proof.
    unfold lt, eq, byte_cmp. rewrite ->N.compare_lt_iff, N.compare_eq_iff.
    lia.
  Qed.
  Definition compare (x y : t) : OrderedType.Compare lt eq x y.
  Proof.
    refine (match byte_cmp x y as X return byte_cmp x y = X -> OrderedType.Compare lt eq x y with
      | Eq => fun pf => OrderedType.EQ pf
      | Lt => fun pf => OrderedType.LT pf
      | Gt => fun pf => OrderedType.GT _
      end Logic.eq_refl).
    unfold lt, byte_cmp.
    abstract (rewrite N.compare_antisym; apply CompOpp_iff, pf).
  Defined.

  Definition eq_dec (x y : t) : {eq x y} + {~ eq x y}.
  Proof.
    refine (match byte_cmp x y as Z return byte_cmp x y = Z -> _ with
        | Eq => fun pf => left pf
        | _ => fun _ => right _
        end Logic.eq_refl);
    abstract congruence.
  Defined.
End OT_byte.

Theorem byte_cmp_spec x y : CompareSpec (x = y) (OT_byte.lt x y) (OT_byte.lt y x) (byte_cmp x y).
Proof.
  unfold byte_cmp, OT_byte.lt, byte_cmp.
  destruct (N.compare_spec (Byte.to_N x) (Byte.to_N y)); constructor; auto.
  apply byte_to_N_inj. assumption.
Qed.

(** bytestrings *)
(** Many functions on byte strings are meant to be always used
qualified, as they conflict with similar functions from [List] or [String].

All such functions are collected in a module [BS], which serves as a namespace:
that is, it is not meant to be imported by clients.
*)

Module Import BS.
  Inductive t : Set :=
  | EmptyString
  | String (_ : Byte.byte) (_ : t).

  Definition eq_dec (x y : t) : {x = y} + {x <> y}.
  Proof. decide equality. apply Byte.byte_eq_dec. Defined.

  Fixpoint print (b : t) : list Byte.byte :=
    match b with
    | EmptyString => nil
    | String b bs => b :: print bs
    end.

  Fixpoint parse (b : list Byte.byte) : t :=
    match b with
    | nil => EmptyString
    | b :: bs => String b (parse bs)
    end.

  Lemma print_parse_inv (x : t) :
    parse (print x) = x.
  Proof.
    induction x; simpl; intros; auto.
    f_equal; auto.
  Qed.

  Lemma parse_print_inv (x : list Byte.byte) :
    print (parse x) = x.
  Proof.
    induction x; simpl; intros; auto.
    f_equal; auto.
  Qed.

  Lemma print_empty : print EmptyString = [].
  Proof. done. Qed.
  Lemma parse_nil : parse [] = EmptyString.
  Proof. done. Qed.

  Lemma print_string b s : print (String b s) = b :: print s.
  Proof. done. Qed.
  Lemma parse_cons b l : parse (b :: l) = String b (parse l).
  Proof. done. Qed.

  Lemma print_nil_inv s : print s = [] -> s = EmptyString.
  Proof. by destruct s. Qed.
  Lemma parse_nil_inv l : parse l = EmptyString -> l = [].
  Proof. by destruct l. Qed.

  Lemma print_cons_inv s b l :
    print s = b :: l -> exists t, s = String b t /\ l = print t.
  Proof.
    destruct s as [|b' t]; [done|]. cbn. move=>[]<- ?. by eexists.
  Qed.
  Lemma parse_string_inv l b s :
    parse l = String b s -> exists k, l = b :: k /\ s = parse k.
  Proof.
    destruct l as [|b' k]; [done|]. cbn. move=>[]<- ?. by eexists.
  Qed.

  #[global] Instance print_inj : Inj (=) (=) print.
  Proof.
    move=>s t. elim: t s=>[|b t IH] s /=.
    { apply print_nil_inv. }
    { intros (u & -> & ?)%print_cons_inv. by rewrite (IH u). }
  Qed.
  #[global] Instance parse_inj : Inj (=) (=) parse.
  Proof.
    move=>l k. elim: k l=>[|b k IH] l /=.
    { apply parse_nil_inv. }
    { intros (k' & -> & ?)%parse_string_inv. by rewrite (IH k'). }
  Qed.

  Fixpoint rev_append (s t : BS.t) {struct s} : BS.t :=
    match s with
    | EmptyString => t
    | String b s => rev_append s (String b t)
    end.
  Definition rev (s : BS.t) : BS.t := rev_append s EmptyString.
  Definition append_tailrec (s t : BS.t) : BS.t := rev_append (rev s) t.
  Fixpoint append (s t : BS.t) {struct s} : BS.t :=
    match s with
    | EmptyString => t
    | String b s => String b (append s t)
    end.

  (** Module [Bytestring_notations] is exported below, and contains
  notations that can be safely exported. *)
  Module Import Bytestring_notations.
    Notation bs := BS.t.

    Declare Scope bs_scope.
    Delimit Scope bs_scope with bs.
    Bind Scope bs_scope with bs.

    Notation "x ++ y" := (append x y) : bs_scope.

    String Notation bs BS.parse BS.print : bs_scope.

  End Bytestring_notations.
  #[local] Notation Byte b := (String b EmptyString) (only parsing).

  Lemma print_rev_append s t :
    print (rev_append s t) = List.rev_append (print s) (print t).
  Proof. by elim: s t; cbn. Qed.

  Lemma print_rev s : print (rev s) = reverse (print s).
  Proof. by rewrite /rev print_rev_append. Qed.

  Lemma print_append_tailrec s t : print (append_tailrec s t) = print s ++ print t.
  Proof.
    rewrite /append_tailrec print_rev_append print_rev.
    rewrite rev_append_rev rev_alt.
    by rewrite -/(reverse (reverse (print s))) reverse_involutive.
  Qed.

  Lemma print_append s t : print (s ++ t) = print s ++ print t.
  Proof. elim: s t=>//= b s IH t. by f_equiv. Qed.

  Lemma append_alt s t : (s ++ t)%bs = append_tailrec s t.
  Proof. apply (inj print). by rewrite print_append print_append_tailrec. Qed.

  #[global] Instance append_left_id : LeftId (=) EmptyString append.
  Proof. done. Qed.
  #[global] Instance append_right_id : RightId (=) EmptyString append.
  Proof.
    intros s. apply (inj print).
    by rewrite print_append print_empty right_id_L.
  Qed.

  Lemma rev_empty : rev "" = ""%bs.
  Proof. done. Qed.

  Lemma rev_string b s : rev (String b s) = (rev s ++ Byte b)%bs.
  Proof.
    apply (inj print). rewrite !(print_rev, print_append, print_string).
    by rewrite reverse_cons print_empty.
  Qed.

  Lemma rev_involutive s : rev (rev s) = s.
  Proof. apply (inj print). by rewrite !print_rev reverse_involutive. Qed.

  Lemma rev_app s t : rev (s ++ t) = (rev t ++ rev s)%bs.
  Proof.
    apply (inj print). by rewrite !(print_rev, print_append, reverse_app).
  Qed.

  Definition concat_aux (rsep : bs) :=
    fix concat_aux (rl : list bs) (acc : bs) {struct rl} : bs :=
    match rl with
    | nil => acc
    | s :: nil => append s acc
    | s :: (_ :: _) as rl =>
      let acc := append_tailrec s acc in
      let acc := rev_append rsep acc in
      concat_aux rl acc
    end.
  Definition concat (sep : bs) (l : list bs) : bs :=
    concat_aux (rev sep) (reverse l) EmptyString.

  (** Building strings in linear time  *)
  Module Buf.
    Inductive t : Set :=
    | Empty
    | Byte (_ : Byte.byte)
    | String (_ : bs)
    | Append (_ _ : t)
    | Concat (_ : t) (_ : list t).

    Definition concat_aux (contents_aux : t -> bs -> bs) (sep : t) :=
      fix concat_aux (l : list t) (acc : bs) : bs :=
      match l with
      | nil => acc
      | b :: nil => contents_aux b acc
      | b :: (_ :: _) as l =>
        let acc := concat_aux l acc in
        let acc := contents_aux sep acc in
        contents_aux b acc
      end.
    Fixpoint contents_aux (b : t) (acc : bs) {struct b} : bs :=
      match b with
      | Empty => acc
      | Byte b => BS.String b acc
      | String s => BS.append_tailrec s acc
      | Append b1 b2 =>
        let acc := contents_aux b2 acc in
        contents_aux b1 acc
      | Concat sep bufs => concat_aux contents_aux sep bufs acc
      end.
    Definition contents (b : t) : bs := contents_aux b BS.EmptyString.

    #[global] Instance empty : base.Empty t := Empty.
    #[global] Instance monoid : monoid.Monoid t := {
      monoid.monoid_unit := Empty;
      monoid.monoid_op := Append;
    }.
  End Buf.

  Fixpoint prefix (s1 s2 : bs) {struct s1} : bool :=
    match s1 with
    | EmptyString => true
    | String x xs =>
      match s2 with
      | EmptyString => false
      | String y ys =>
        if Byte.byte_eq_dec x y then prefix xs ys
        else false
      end
    end.

  (** [substring n m s] returns the substring of [s] that starts
      at position [n] and of length [m];
      if this does not make sense it returns [""] *)
  Fixpoint substring (n m : nat) (s : bs) : bs :=
    match n, m, s with
    | O,    O,    _              => BS.EmptyString
    | O,    S m', BS.EmptyString => s
    | O,    S m', BS.String c s' => BS.String c (substring 0 m' s')
    | S n', _,    BS.EmptyString => s
    | S n', _,    BS.String c s' => substring n' m s'
    end.

  Fixpoint index (n : nat) (s1 s2 : bs) {struct s2} : option nat :=
    match s2 with
    | EmptyString =>
        match n with
        | 0 => match s1 with
              | "" => Some 0
              | String _ _ => None
              end
        | S _ => None
        end
    | String _ s2' =>
        match n with
        | 0 =>
            if prefix s1 s2
            then Some 0
            else match index 0 s1 s2' with
                | Some n0 => Some (S n0)
                | None => None
                end
        | S n' => match index n' s1 s2' with
                  | Some n0 => Some (S n0)
                  | None => None
                  end
        end
    end%bs.

  Fixpoint length (l : bs) : nat :=
    match l with
    | EmptyString => 0
    | String _ l => S (length l)
    end.

  Lemma print_length (s : bs) :
    List.length (print s) = length s.
  Proof.
    induction s; simpl.
    - easy.
    - now rewrite IHs.
  Qed.

  Fixpoint contains (start : nat) (keys : list bs) (fullname : bs) :bool :=
    match keys with
    | kh::ktl =>
      match index start kh fullname with
      | Some n => contains (n + length kh) ktl fullname
      | None => false
      end
    | [] => true
    end.

  Definition eqb (a b : bs) : bool :=
    if eq_dec a b then true else false.

  #[deprecated(since="2021-09-21", note="Use [byte_to_N_inj].")]
  Notation to_N_inj := byte_to_N_inj.
End BS.
Export Bytestring_notations.

Fixpoint bs_cmp (xs ys : bs) : comparison :=
  match xs , ys with
  | BS.EmptyString , BS.EmptyString => Eq
  | BS.EmptyString , _ => Lt
  | _ , BS.EmptyString => Gt
  | BS.String x xs , BS.String y ys =>
    match byte_cmp x y with
    | Eq => bs_cmp xs ys
    | x => x
    end
  end%bs.
#[global] Instance bs_compare : Compare bs := bs_cmp.

Module OT_bs <: OrderedType.OrderedType with Definition t := bs.
  Definition t := bs.
  Definition eq := @eq bs.
  Definition lt := fun l r => bs_cmp l r = Lt.

  Theorem lm x y : CompareSpec (x = y) (lt x y) (lt y x) (bs_cmp x y).
  Proof.
    revert y; induction x; destruct y; simpl.
    - constructor; reflexivity.
    - constructor. reflexivity.
    - constructor. reflexivity.
    - unfold lt; simpl.
      destruct (byte_cmp_spec b b0); simpl.
      + subst. destruct (IHx y); constructor; eauto.
        congruence.
        destruct (byte_cmp_spec b0 b0); try congruence.
        red in H0. rewrite OT_byte.eq_refl in H0. congruence.
      + constructor; auto.
      + red in H. rewrite H. constructor; auto.
  Qed.

  Definition compare (x y : t) : OrderedType.Compare lt eq x y.
  Proof.
    refine (
      match bs_cmp x y as X return bs_cmp x y = X -> OrderedType.Compare lt eq x y with
      | Eq => fun pf => OrderedType.EQ _
      | Lt => fun pf => OrderedType.LT pf
      | Gt => fun pf => OrderedType.GT _
      end (Logic.eq_refl));
    abstract (generalize (lm x y); rewrite pf; inversion 1; auto).
  Defined.

  Theorem eq_refl (x : t) : eq x x.
  Proof. reflexivity. Qed.
  Theorem eq_sym (x y : t) : eq x y -> eq y x.
  Proof. eapply eq_sym. Qed.
  Theorem eq_trans (x y z : t) : eq x y -> eq y z -> eq x z.
  Proof. eapply eq_trans. Qed.
  Theorem lt_trans (x y z : t) : lt x y -> lt y z -> lt x z.
  Proof.
    unfold lt.
    revert y z.
    induction x; destruct y; simpl; try congruence.
    - destruct z; congruence.
    - destruct (byte_cmp_spec b b0); subst.
      + destruct z; auto.
        destruct (byte_cmp b0 b); auto.
        eauto.
      + destruct z; auto.
        red in H.
        destruct (byte_cmp b0 b1) eqn:?.
        * generalize (byte_cmp_spec b0 b1).
          rewrite Heqc. inversion 1.
          subst. rewrite H. auto.
        * generalize (OT_byte.lt_trans _ _ _ H Heqc). unfold OT_byte.lt.
          intro X; rewrite X. auto.
        * congruence.
      + congruence.
  Qed.
  Theorem lt_not_eq (x y : t) : lt x y -> ~ eq x y.
  Proof.
    unfold lt, eq.
    intros Heq ->.
    induction y; simpl in *; try congruence.
    rewrite ->byte_cmp_refl in Heq. auto.
  Qed.

  Definition eq_dec := BS.eq_dec.
End OT_bs.

(* The [Arguments] line for [Byte.to_bits] speeds up [simpl] quite considerably,
   especially when [simpl] makes no progress. *)
#[global] Arguments Byte.to_bits !_ / : simpl nomatch.
