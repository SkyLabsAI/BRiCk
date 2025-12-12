(*
 * Copyright (c) 2020-2025 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 * Attribution: Work done by Eashan Hatti <eashan.hatti@yale.edu>
 *)

(**
A mostly-complete consistency proof for [PTRS] base upon [inductive_ptrs.v]. The main
difference is that this file defines offset normalization as a string-rewrite system
instead of using a Coq function.
*)

Require Import Equations.Prop.Equations.

Require Import stdpp.relations.
Require Import stdpp.gmap.
Require Import bluerock.prelude.base.
Require Import bluerock.prelude.addr.
Require Import bluerock.prelude.avl.
Require Import bluerock.prelude.bytestring.
Require Import bluerock.prelude.numbers.

Require Import bluerock.lang.cpp.syntax.
Require Import bluerock.lang.cpp.semantics.sub_module.
Require Import bluerock.lang.cpp.semantics.values.
Require Import bluerock.lang.cpp.model.simple_pointers_utils.
Require Import bluerock.lang.cpp.model.inductive_pointers_utils.
Require Import bluerock.lang.cpp.semantics.ptrs.

Axiom irr : ∀ (P : Prop) (p q : P), p = q.

Implicit Types (σ : genv) (z : Z).
#[local] Close Scope nat_scope.
#[local] Open Scope Z_scope.

Module PTRS_IMPL <: PTRS_INTF.
  Import canonical_tu address_sums merge_elems.

  Inductive raw_offset_seg : Set :=
  | o_field_ (* type-name: *) (f : field)
  | o_sub_ (ty : type) (z : Z)
  | o_base_ (derived base : globname)
  | o_derived_ (base derived : globname).
  #[local] Instance raw_offset_seg_eq_dec : EqDecision raw_offset_seg.
  Proof. solve_decision. Defined.
  #[global] Declare Instance raw_offset_seg_countable : Countable raw_offset_seg.

  Definition raw_offset := list raw_offset_seg.
  #[local] Instance raw_offset_eq_dec : EqDecision raw_offset := _.
  #[local] Instance raw_offset_countable : Countable raw_offset := _.

  Variant roff_rw_local : raw_offset -> raw_offset -> Prop :=
  | CanonDerBase der base :
    roff_rw_local
      [o_derived_ base der; o_base_ der base]
      []
  | CanonBaseDer der base :
    roff_rw_local
      [o_base_ der base; o_derived_ base der]
      []
  | CanonSubZero ty :
    roff_rw_local
      [o_sub_ ty 0]
      []
  | CanonSubMerge ty n1 n2 :
      roff_rw_local
        [o_sub_ ty n1; o_sub_ ty n2]
        [o_sub_ ty (n1 + n2)].

  Definition roff_rw_global (os1 os2 : raw_offset) :=
    ∃ l r s t,
      os1 = l ++ s ++ r /\
      os2 = l ++ t ++ r /\
      roff_rw_local s t.

  Definition roff_rw := rtc roff_rw_global.

  #[global] Instance: RewriteRelation roff_rw := {}.
  #[global] Instance: subrelation roff_rw_global roff_rw.
  Proof. exact: rtc_once. Qed.
  (* #[global] Instance: Reflexive roff_rw.
  Proof. apply _. Abort.
  #[global] Instance: Transitive roff_rw.
  Proof. apply _. Abort. *)
  Definition roff_canon := nf roff_rw_global.

  #[global] Instance roff_rw_reflexive : Reflexive roff_rw.
  Proof.
    move=> x. done.
  Qed.
  #[global] Instance roff_rw_transitive : Transitive roff_rw.
  Proof.
    move=> x y z. apply rtc_transitive.
  Qed.

  Lemma singleton_offset_canon :
    ∀ o,
      (¬∃ ty, o = o_sub_ ty 0) ->
      roff_canon [o].
  Proof.
    assert (Hn : ∀ A (x y z : A) (l r : list A), [x] ≠ l ++ [y; z] ++ r).
    {
      move=> A x y z l r H.
      destruct l. done.
      inversion H. subst.
      destruct l; done.
    }
    move=> o H.
    rewrite /roff_canon /nf /roff_rw_global /red.
    move=> [_ [l [r [s [t [H1 [_ H2]]]]]]].
    destruct H2.
    { apply: Hn. exact: H1. }
    { apply: Hn. exact: H1. }
    {
      destruct l; simpl in H1;
      inversion H1; subst.
      { apply: H. by exists ty. }
      destruct l; done.
    }
    { apply: Hn. exact: H1. }
  Qed.

  Lemma nil_canon :
    roff_canon [].
  Proof.
    rewrite /roff_canon /roff_rw_global /nf /not /red.
    move=> [o [l [r [s [t [H1 [H2 H3]]]]]]].
    subst.
    assert (l = []).
    { by destruct l. }
    subst.
    assert (s = []).
    { by destruct s. }
    subst.
    clear - H3. remember [].
    by destruct H3.
  Qed.

  Inductive roff_canon_syn : raw_offset -> Prop :=
  | NilCanon :
      roff_canon_syn []
  | SingCanon o :
      ¬(∃ ty, o = o_sub_ ty 0) ->
      roff_canon_syn [o]
  | SubCanon ty i o os :
      roff_canon_syn (o :: os) ->
      ¬(∃ i' ty', o = o_sub_ ty' i') ->
      i ≠ 0 ->
      roff_canon_syn (o_sub_ ty i :: o :: os)
  | FieldCanon f os :
      roff_canon_syn os ->
      roff_canon_syn (o_field_ f :: os)
  | BaseCanon der base o os :
      roff_canon_syn (o :: os) ->
      o ≠ o_derived_ base der ->
      roff_canon_syn (o_base_ der base :: o :: os)
  | DerCanon base der o os :
      roff_canon_syn (o :: os) ->
      o ≠ o_base_ der base ->
      roff_canon_syn (o_derived_ base der :: o :: os).

  Lemma canon_syn_sem_eqv :
    ∀ os,
      roff_canon os <-> roff_canon_syn os.
  Proof.
    rewrite /roff_canon /nf /red.
    move=> os. split; move=> Hc.
    {
      admit.
    }
    {
      induction Hc;
      try (
        remember (o :: os) as eos;
        destruct Hc; subst
      ); try done;
      try inversion Heqeos;
      subst.
      { apply: nil_canon. }
      { by apply: singleton_offset_canon. }
      all:
        move=> [y [l [r [s [t [Ho [Hl Hstep]]]]]]];
        subst; destruct l; simpl in *; destruct Hstep;
        simpl in *; inversion Ho; subst; try done;
        try (
          match goal with
          | H : ¬∃ i ty, o_sub_ _ _ = o_sub_ ty i |- False =>
            apply H
          end;
          try repeat eexists
        );
        try (
          match goal with
          | H : [?o] = ?l ++ ?r |- False =>
            destruct l; simpl in *;
            inversion H; subst;
            destruct l; simpl in *;
            inversion H
          end
        );
        try (
          match goal with
          | H : [?o] = ?l ++ ?r |- False =>
            destruct l; simpl in *;
            inversion H; subst
          end
        );
        try (
          match goal with
          | H : ¬∃ ty, o_sub_ _ 0 = o_sub_ ty 0 |- False =>
              apply H; repeat eexists
          end
        );
        try (
          match goal with
          | H : [] = ?l ++ ?r |- False =>
              destruct l; simpl in *;
              inversion H
          end
        ).
        all: admit.
    }
  Admitted.

  (** *** Offsets *)
  Definition offset := {o : raw_offset | roff_canon o}.
  #[global] Instance offset_eq_dec : EqDecision offset.
  Proof.
    move=> [o1 H1] [o2 H2].
    destruct (decide (o1 = o2)).
    {
      subst. left.
      f_equal.
      apply: irr.
    }
    {
      right.
      rewrite /not => H.
      apply n.
      now apply proj1_sig_eq in H.
    }
  Qed.
  #[global] Declare Instance offset_countable : Countable offset.

  Section norm_def.

    Equations find_redex (os : raw_offset)
      : option (raw_offset * raw_offset * raw_offset * raw_offset)
      by wf (length os) :=
    | [] :=
        None
    | o_sub_ ty 0 :: os :=
        Some ([], os, [o_sub_ ty 0], [])
    | o_sub_ ty1 i1 :: o_sub_ ty2 i2 :: os :=
        if decide (ty1 = ty2) then
          Some ([], os, [o_sub_ ty1 i1; o_sub_ ty2 i2], [o_sub_ ty1 (i1 + i2)])
        else
          '(l, r, s, t) ← find_redex (o_sub_ ty2 i2 :: os);
          Some (o_sub_ ty1 i1 :: l, r, s, t)
    | o_base_ der1 base1 :: o_derived_ base2 der2 :: os =>
        if decide (der1 = der2 /\ base1 = base2) then
          Some ([], os, [o_base_ der1 base1; o_derived_ base2 der2], [])
        else
          '(l, r, s, t) ← find_redex (o_derived_ base2 der2 :: os);
          Some (o_base_ der1 base1 :: l, r, s, t)
    | o_derived_ base1 der1 :: o_base_ der2 base2 :: os =>
        if decide (der1 = der2 /\ base1 = base2) then
          Some ([], os, [o_derived_ base1 der1; o_base_ der2 base2], [])
        else
          '(l, r, s, t) ← find_redex (o_base_ der2 base2 :: os);
          Some (o_derived_ base1 der1 :: l, r, s, t)
    | o :: os =>
        '(l, r, s, t) ← find_redex os;
        Some (o :: l, r, s, t).
    Admit Obligations.

    Ltac dex :=
      let H0 := fresh in
      move=> H0;
      repeat match goal with
      | H : ∃ x, ?P |- _ => destruct H
      | H : ?x = ?y |- _ => inversion H; subst; done
      end.

    Lemma find_redex_ind :
      ∀ P :
        raw_offset ->
        option (raw_offset * raw_offset * raw_offset * raw_offset) ->
        Prop,
      (P [] None) ->
      (∀ ty os,
        P
          (o_sub_ ty 0 :: os)
          (Some ([], os, [o_sub_ ty 0], []))) ->
      (∀ ty i1 i2 os,
        i1 ≠ 0 ->
        P
          (o_sub_ ty i1 :: o_sub_ ty i2 :: os)
          (Some ([], os, [o_sub_ ty i1; o_sub_ ty i2], [o_sub_ ty (i1 + i2)]))) ->
      (∀ der base os,
        P
          (o_base_ der base :: o_derived_ base der :: os)
          (Some ([], os, [o_base_ der base; o_derived_ base der], []))) ->
      (∀ base der os,
        P
          (o_derived_ base der :: o_base_ der base :: os)
          (Some ([], os, [o_derived_ base der; o_base_ der base], []))) ->
      (∀ o os l r s t,
        P os (Some (l, r, s, t)) ->
        P (o :: os) (Some (o :: l, r, s, t))) ->
      (∀ o os,
        ¬(∃ ty, o = o_sub_ ty 0) ->
        ¬(∃ ty i1 i2 r, o :: os = o_sub_ ty i1 :: o_sub_ ty i2 :: r) ->
        ¬(∃ der base r, o :: os = o_base_ der base :: o_derived_ base der :: r) ->
        ¬(∃ base der r, o :: os = o_derived_ base der :: o_base_ der base :: r) ->
        P os None ->
        P (o :: os) None) ->
      ∀ os, P os (find_redex os).
    Proof.
      move=> P Pnil Ps0 Pss Pbd Pdb Pks Pkn os.
      funelim (find_redex os); simp find_redex in *;
      try case_match; subst; clear Heqcall; simpl in *.
      all:
        repeat match type of H with
        | ∀ x : ?A, _ =>
          match goal with
          | H2 : ?A |- _ => specialize (H H2)
          end
        end.
      all: try (
        destruct (find_redex _); simpl in *;
        (
          repeat match goal with
          | H : _ * _ |- _ => destruct H
          end; by apply Pks, H
        ||
        apply Pkn; (dex || done)
        )
      ).
      all: try (apply Pkn; (dex || done)).
      { by apply Pss. }
      { by apply Pss. }
      { destruct a. subst. apply Pbd. }
      {
        destruct (find_redex _); simpl in *.
        {
          repeat match goal with
          | H : _ * _ |- _ => destruct H
          end; by apply Pks, H.
        }
        {
          apply Pkn; (dex || done).
          inversion H1. subst. by apply n.
        }
      }
      { destruct a. subst. apply Pdb. }
      {
        destruct (find_redex _); simpl in *.
        {
          repeat match goal with
          | H : _ * _ |- _ => destruct H
          end; by apply Pks, H.
        }
        {
          apply Pkn; (dex || done).
          inversion H1. subst. by apply n.
        }
      }
    Qed.

    Lemma find_redex_pass :
      ∀ os l s r t,
        find_redex os = Some (l, r, s, t) ->
        os = l ++ s ++ r /\
        roff_rw_local s t.
    Proof.
      move=> os.
      apply find_redex_ind; clear.
      { done. }
      {
        move=> ty os l r s t H.
        inversion H; subst.
        repeat constructor.
      }
      {
        move=> ty i1 i2 os H1 l r s t H2.
        inversion H2. subst.
        repeat constructor.
      }
      {
        move=> der base os l r s t H.
        inversion H. subst.
        repeat constructor.
      }
      {
        move=> base der os l r s t H.
        inversion H. subst.
        repeat constructor.
      }
      {
        move=> o os l r s t H1 l' s' r' t' H2.
        inversion H2. subst. simpl in *.
        specialize (H1 _ _ _ _ eq_refl).
        move: H1 => [Hos Hrw]. by subst.
      }
      { done. }
    Qed.

    Lemma find_redex_fail :
      ∀ os,
        find_redex os = None ->
        ¬∃ l r s t,
            os = l ++ s ++ r /\
            roff_rw_local s t.
    Proof.
      move=> os.
      apply find_redex_ind;
      clear; try done.
      {
        move=> _ [l [r [s [t [Heq Hrw]]]]].
        destruct l; simpl in *; try done.
        destruct s; simpl in *; try done.
        subst. inversion Hrw.
      }
      {
        move=> o os Hns0 Hnss Hnbd Hndb IH.
        move=> _ [l [r [s [t [Heq Hrw]]]]].
        destruct l; simpl in *.
        {
          destruct Hrw; simpl in *;
          inversion Heq; subst.
          { apply Hndb. repeat eexists. }
          { apply Hnbd. repeat eexists. }
          { apply Hns0. repeat eexists. }
          { apply Hnss. repeat eexists. }
        }
        {
          inversion Heq. subst.
          apply IH.
          { done. }
          { by exists l, r, s, t. }
        }
      }
    Qed.

    Lemma length_app {A} :
      ∀ xs ys : list A,
        length (xs ++ ys) = (length xs + length ys)%nat.
    Proof.
      move=> xs ys.
      induction xs; simpl; auto.
    Qed.

    Equations normalize (os : raw_offset) : raw_offset by wf (length os) lt :=
    normalize os with (existT (find_redex os) eq_refl) => {
      normalize os (existT (Some (l, r, s, t)) H) => normalize (l ++ t ++ r);
      normalize os (existT None H) => os
    }.
    Next Obligation.
      intros.
      apply find_redex_pass in H.
      move: H => [Heq Hrw]. subst.
      repeat rewrite length_app.
      destruct Hrw; simpl; lia.
    Qed.

    Lemma norm_eager :
      ∀ s t r,
        roff_rw_local s t ->
        normalize (s ++ r) = normalize (t ++ r).
    Proof.
      move=> s t r H.
      funelim (normalize (s ++ r)).
      {
        clear H0 H1 Heqcall.
        destruct H2; simpl in *;
        simp find_redex in *;
        try case_match;
        try match goal with
        | H : ¬(?x = ?x /\ ?y = ?y) |- _ =>
          exfalso; by apply H
        end;
        inversion H;
        subst; simpl;
        try done.
        {
          destruct n1; simpl in *;
          simp find_redex in *;
          try case_match; try done;
          inversion H1; subst;
          simpl; done.
        }
      }
      {
        clear - H H1.
        apply find_redex_fail in H.
        exfalso. apply: H.
        by exists [], r, s, t.
      }
    Qed.

    Lemma norm_sound :
      ∀ os ,
        roff_rw os (normalize os).
    Proof.
      move=> os.
      funelim (normalize os).
      {
        clear H1.
        apply find_redex_pass in H.
        move: H => [Heq Hrw]. subst.
        apply: rtc_l. 2: apply H0.
        by exists l, r, s, t.
      }
      { done. }
    Qed.

    Lemma norm_canon :
      ∀ os, roff_canon (normalize os).
    Proof.
      move=> os.
      funelim (normalize os).
      {
        clear H1.
        apply find_redex_pass in H.
        move: H => [Heq Hrw]. subst.
        done.
      }
      {
        clear - H.
        apply find_redex_fail in H.
        move=> [y [l [r [s [t [Hos [Hy Hrw]]]]]]].
        apply H. by exists l, r, s, t.
      }
    Qed.

    Lemma canon_uncons :
      ∀ o os,
        roff_canon (o :: os) ->
        roff_canon os.
    Proof.
      move=> o os H1 H2. apply: H1.
      move: H2 => [y [l [r [s [t [H1 [H2 H3]]]]]]].
      subst. by exists (o :: l ++ t ++ r), (o :: l), r, s, t.
    Qed.

    Lemma norm_invol :
      ∀ os,
        roff_canon os <-> normalize os = os.
    Proof.
      move=> os.
      split; move=> H.
      {
        funelim (normalize os).
        clear Heqcall H1. 2: done.
        exfalso. apply: H2.
        apply find_redex_pass in H.
        move: H => [Heq Hrw]. subst.
        by exists (l ++ t ++ r), l, r, s, t.
      }
      {
        move: H.
        funelim (normalize os);
        intros; subst.
        {
          clear H1 Heqcall.
          apply find_redex_pass in H.
          move: H => [Heq Hrw]. clear H0.
          assert (roff_canon (l ++ s ++ r)).
          {
            rewrite -Heq.
            apply norm_canon.
          }
          exfalso. apply H.
          by exists (l ++ t ++ r), l, r, s, t.
        }
        {
          clear - H.
          apply find_redex_fail in H.
          move=> [y [l [r [s [t [H1 [H2 H3]]]]]]].
          apply: H. subst. repeat eexists; done.
        }
      }
    Qed.

    Lemma norm_complete_aux :
      ∀ l r s t,
        roff_rw_local s t ->
        normalize (l ++ s ++ r) = normalize (l ++ t ++ r).
    Proof.
    Admitted.

    Lemma norm_complete :
      ∀ os1 os2,
        roff_rw os1 os2 ->
        roff_canon os2 ->
        normalize os1 = os2.
    Proof.
      move=> os1 os2 Hrw Hc.
      induction Hrw.
      { by apply norm_invol. }
      {
        rewrite -IHHrw.
        2: done. clear IHHrw Hc Hrw.
        move: H => [l [r [s [t [Hx [Hy Hrw]]]]]].
        subst. clear z. by apply norm_complete_aux.
      }
    Qed.

  End norm_def.

  Section norm_lemmas.

    Lemma norm_rel :
      ∀ os1 os2,
        normalize os1 = os2 <-> roff_rw os1 os2 /\ roff_canon os2.
    Proof.
      move=> os1 os2.
      split; move=> H.
      {
        subst. split.
        { apply norm_sound. }
        { apply norm_canon. }
      }
      {
        apply norm_complete;
        by destruct H.
      }
    Qed.

    Lemma norm_rw_derive :
      ∀ os1 os2,
        roff_rw os1 os2 ->
        normalize os1 = normalize os2.
    Proof.
      move=> os1 os2 H.
      apply norm_complete.
      {
        remember (normalize os2).
        symmetry in Heqr.
        rewrite norm_rel in Heqr.
        etrans. exact: H. by destruct Heqr.
      }
      { apply norm_canon. }
    Qed.

  End norm_lemmas.

  Section rw_lemmas.

    Lemma roff_rw_cong :
      ∀ ol1 ol2 or1 or2,
        roff_rw ol1 or1 ->
        roff_rw ol2 or2 ->
        roff_rw (ol1 ++ ol2) (or1 ++ or2).
    Proof.
      move=> ol1 ol2 or1 or2 Hrw0 Hrw1.
      induction Hrw0.
      {
        induction Hrw1.
        { done. }
        {
          rewrite -{}IHHrw1.
          apply rtc_once.
          move: H => [l [r [s [t [H1 [H2 H3]]]]]].
          subst. exists (x ++ l), r, s, t.
          split. by rewrite app_assoc.
          split. by rewrite app_assoc.
          done.
        }
      }
      {
        rewrite -{}IHHrw0.
        apply rtc_once.
        move: H => [l [r [s [t [H1 [H2 H3]]]]]].
        subst. exists l, (r ++ ol2), s, t.
        split. by repeat rewrite -app_assoc.
        split. by repeat rewrite -app_assoc.
        done.
      }
    Qed.

    #[global] Instance roff_rw_app_mono :
      Proper (roff_rw ==> roff_rw ==> roff_rw) (++).
    Proof.
      rewrite /Proper /respectful.
      move=> ol1 or1 H1 ol2 or2 H2.
      by apply roff_rw_cong.
    Qed.
    #[global] Instance roff_rw_app_flip_mono :
      Proper (flip roff_rw ==> flip roff_rw ==> flip roff_rw) (++).
    Proof. solve_proper. Qed.

    #[global] Instance roff_rw_cons_mono ro :
      Proper (roff_rw ==> roff_rw) (ro ::.).
    Proof.
      intros x y H.
      by apply roff_rw_cong with (ol1:=[ro]) (or1:=[ro]).
    Qed.

    #[global] Instance roff_rw_cons_flip_mono ro :
      Proper (flip roff_rw ==> flip roff_rw) (ro ::.).
    Proof. solve_proper. Qed.

    #[local] Hint Constructors roff_rw_local : core.

    Lemma norm_absorb_l :
      ∀ o1 o2,
        normalize (o1 ++ normalize o2) = normalize (o1 ++ o2).
    Proof.
      move=> o1 o2.
      symmetry.
      apply norm_rw_derive.
      apply roff_rw_cong.
      { done. }
      { apply norm_sound. }
    Qed.

    Lemma norm_absorb_r :
      ∀ o1 o2,
        normalize (normalize o1 ++ o2) = normalize (o1 ++ o2).
    Proof.
      move=> o1 o2.
      symmetry.
      apply norm_rw_derive.
      apply roff_rw_cong.
      { apply norm_sound. }
      { done. }
    Qed.

  End rw_lemmas.

  Variant root_ptr : Set :=
  | nullptr_
  | global_ptr_ (tu : translation_unit_canon) (o : obj_name)
  | fun_ptr_ (tu : translation_unit_canon) (o : obj_name)
  | alloc_ptr_ (a : alloc_id) (va : vaddr).
  Variant ptr_ : Set :=
  | invalid_ptr_
  | offset_ptr (p : root_ptr) (o : offset).
  Definition ptr := ptr_.
  #[global] Instance ptr_eq_dec : EqDecision ptr.
  Admitted.
  #[global] Instance ptr_countable : Countable ptr.
  Admitted.

  #[program] Definition __offset_ptr (p : ptr) (o : offset) : ptr :=
    match p with
    | invalid_ptr_ => invalid_ptr_
    | offset_ptr rp ro => offset_ptr rp (normalize (ro ++ o))
    end.
  Next Obligation.
    intros. simpl.
    apply: norm_canon.
  Qed.

  Program Definition __o_dot (o1 o2 : offset) : offset :=
    normalize (o1 ++ o2).
  Next Obligation.
    intros. simpl.
    apply: norm_canon.
  Qed.

  Include PTRS_SYNTAX_MIXIN.

  Lemma sig_eq {A} {P : A -> Prop} :
  ∀ (x y : A) (p : P x) (q : P y),
    x = y ->
    x ↾ p = y ↾ q.
  Proof.
    move=> x y p q H.
    subst. f_equal.
    apply: irr.
  Qed.

  Program Definition o_id : offset :=
    [].
  Next Obligation.
    by apply: nil_canon.
  Qed.

  #[local] Ltac UNFOLD_dot := rewrite _dot.unlock/DOT_dot/=.

  Lemma id_dot : LeftId (=) o_id o_dot.
  Proof.
    UNFOLD_dot.
    move=> [o H].
    rewrite /o_id /__o_dot.
    simpl. apply: sig_eq.
    by apply norm_invol.
  Qed.

  Lemma dot_id : RightId (=) o_id o_dot.
  Proof.
    UNFOLD_dot.
    move=> [o H].
    rewrite /o_id /__o_dot.
    simpl. apply: sig_eq.
    rewrite app_nil_r.
    by apply norm_invol.
  Qed.

  Lemma dot_assoc : Assoc (=) o_dot.
  Proof.
    UNFOLD_dot.
    move=> [o1 H1] [o2 H2] [o3 H3].
    rewrite /o_id /__o_dot.
    simpl. apply: sig_eq.
    by rewrite norm_absorb_l norm_absorb_r app_assoc.
  Qed.

  Lemma offset_ptr_id :
    ∀ p : ptr,
      p ,, o_id = p.
  Proof.
    move=> [| r [o H]]; UNFOLD_dot.
    { easy. }
    {
      f_equal. apply: sig_eq.
      rewrite app_nil_r.
      by apply norm_invol.
    }
  Qed.

  Lemma offset_ptr_dot :
    ∀ (p : ptr) o1 o2,
      p ,, (o1 ,, o2) = p ,, o1 ,, o2.
  Proof.
    move=> [| r o]; UNFOLD_dot.
    { easy. }
    {
      move=> [o1 H1] [o2 H2].
      simpl. f_equal. apply: sig_eq.
      by rewrite norm_absorb_l norm_absorb_r app_assoc.
    }
  Qed.

  Program Definition nullptr : ptr :=
    offset_ptr nullptr_ [].
  Next Obligation.
  Proof.
    by apply: nil_canon.
  Qed.

  Definition invalid_ptr : ptr :=
    invalid_ptr_.

  Program Definition global_ptr (tu : translation_unit) (n : name) : ptr :=
    offset_ptr (global_ptr_ (tu_to_canon tu) n) [].
  Next Obligation.
    intros. simpl.
    by apply: nil_canon.
  Qed.

  Lemma global_ptr_nonnull :
    ∀ tu o,
      global_ptr tu o ≠ nullptr.
  Proof.
    by done.
  Qed.

  (* Definition eval_raw_offset_seg σ (ro : raw_offset_seg) : option Z :=
    match ro with
    | o_field_ f => o_field_off σ f
    | o_sub_ ty z => o_sub_off σ ty z
    | o_base_ derived base => o_base_off σ derived base
    | o_derived_ base derived => o_derived_off σ base derived
    | o_invalid_ => None
    end.

  Definition mk_offset_seg σ (ro : raw_offset_seg) : offset_seg :=
    match eval_raw_offset_seg σ ro with
    | None => (o_invalid_, 0%Z)
    | Some off => (ro, off)
    end. *)

  Program Definition o_field (σ : genv) (f : field) : offset :=
    [o_field_ f].
  Next Obligation.
    intros. simpl.
    apply: singleton_offset_canon.
    by move=> [ty H].
  Qed.

  Program Definition o_base (σ : genv) derived base : offset :=
    [o_base_ derived base].
  Next Obligation.
    intros. simpl.
    apply: singleton_offset_canon.
    by move=> [ty H].
  Qed.

  Program Definition o_derived (σ : genv) base derived : offset :=
    [o_derived_ base derived].
  Next Obligation.
    intros. simpl.
    apply: singleton_offset_canon.
    by move=> [ty H].
  Qed.

  Program Definition o_sub (σ : genv) ty z : offset :=
    if decide (z = 0)%Z then
      o_id
    else
      [o_sub_ ty z].
  Next Obligation.
    intros. simpl.
    apply: singleton_offset_canon.
    move=> [ty' H]. congruence.
  Qed.

  #[global] Notation "p ., o" := (_dot p (o_field _ o))
    (at level 11, left associativity, only parsing) : stdpp_scope.
    #[global] Notation "p .[ t ! n ]" := (_dot p (o_sub _ t n))
      (at level 11, left associativity, format "p  .[  t  '!'  n  ]") : stdpp_scope.
    #[global] Notation ".[ t ! n ]" := (o_sub _ t n) (at level 11, no associativity, format ".[  t  !  n  ]") : stdpp_scope.

  Lemma o_sub_0 :
    ∀ σ ty,
      is_Some (size_of σ ty) ->
      o_sub σ ty 0 = o_id.
  Proof.
    move=> σ ty _.
    rewrite /o_sub.
    by case_match.
  Qed.

  Lemma o_base_derived :
    ∀ σ (p : ptr) base derived,
      directly_derives σ derived base ->
      p ,, o_base σ derived base ,, o_derived σ base derived = p.
  Proof.
    UNFOLD_dot.
    rewrite /__offset_ptr.
    move=> σ [| rp [o H]] base der _.
    { done. }
    {
      f_equal. simpl. apply: sig_eq.
      rewrite norm_absorb_r -app_assoc norm_rel.
      split.
      {
        simpl. apply: rtc_l. 2: done.
        exists o, [], [o_base_ der base; o_derived_ base der], [].
        split. done.
        split. by repeat rewrite app_nil_r.
        constructor.
      }
      { done. }
    }
  Qed.

  Lemma o_derived_base :
    ∀ σ (p : ptr) base derived,
      directly_derives σ derived base ->
      p ,, o_derived σ base derived ,, o_base σ derived base = p.
  Proof.
    UNFOLD_dot.
    rewrite /__offset_ptr.
    move=> σ [| rp [o H]] base der _.
    { done. }
    {
      f_equal. simpl. apply: sig_eq.
      rewrite norm_absorb_r -app_assoc norm_rel.
      split.
      {
        simpl. apply: rtc_l. 2: done.
        exists o, [], [o_derived_ base der; o_base_ der base], [].
        split. done.
        split. by repeat rewrite app_nil_r.
        constructor.
      }
      { done. }
    }
  Qed.

  Lemma o_dot_sub :
    ∀ σ i j ty,
      o_sub σ ty i ,, o_sub σ ty j = o_sub σ ty (i + j).
  Proof.
    UNFOLD_dot.
    move=> σ i j ty.
    rewrite /__o_dot /o_sub /o_id.
    repeat case_match; subst;
    try lia; apply sig_eq; simpl.
    { by simp normalize. }
    { simp normalize. by destruct j. }
    { simp normalize. by destruct i. }
    {
      change [o_sub_ ty i; o_sub_ ty j]
      with  ([o_sub_ ty i; o_sub_ ty j] ++ []).
      rewrite (norm_eager _ [o_sub_ ty (i + j)]).
      2: constructor.
      rewrite e (norm_eager _ []).
      2: constructor.
      simpl. by simp normalize.
    }
    {
      change [o_sub_ ty i; o_sub_ ty j]
      with  ([o_sub_ ty i; o_sub_ ty j] ++ []).
      rewrite (norm_eager _ [o_sub_ ty (i + j)]).
      2: constructor. simpl.
      destruct (i + j); done.
    }
  Qed.

  Definition ptr_alloc_id (p : ptr) : option alloc_id :=
    match p with
    | offset_ptr (alloc_ptr_ a _) _ => Some a
    | _ => None
    end.

  Definition null_alloc_id : alloc_id := null_alloc_id.
  Lemma ptr_alloc_id_nullptr :
    ptr_alloc_id nullptr = Some null_alloc_id.
  Admitted.

  Lemma ptr_alloc_id_offset :
    ∀ p o,
      is_Some (ptr_alloc_id (p ,, o)) ->
      ptr_alloc_id (p ,, o) = ptr_alloc_id p.
  Proof.
    UNFOLD_dot.
    rewrite /ptr_alloc_id.
    move=> [| r o1] o2; simpl.
    { done. }
    { by destruct r. }
  Qed.

  Definition eval_offset_seg (σ : genv) (o : raw_offset_seg) : option Z :=
    match o with
    | o_field_ f => o_field_off σ f
    | o_sub_ ty i => o_sub_off σ ty i
    | o_base_ der base => o_base_off σ der base
    | o_derived_ base der => o_derived_off σ base der
    end.

  Fixpoint eval_offset_aux (σ : genv) (os : list raw_offset_seg) : option Z :=
    match os with
    | [] => Some 0
    | o :: os =>
      eval_offset_seg σ o ≫= λ o,
      eval_offset_aux σ os ≫= λ os,
      Some (o + os)
    end.

  Definition eval_offset (σ : genv) (os : offset) : option Z :=
    eval_offset_aux σ (`os).

  Lemma eval_o_sub' :
    ∀ σ (ty : type) (i : Z) (sz : N),
      size_of σ ty = Some sz ->
      eval_offset σ (o_sub σ ty i) = Some (sz * i).
  Proof.
    rewrite /eval_offset /o_sub.
    move=> σ ty i n Hsome.
    case_match; subst; simpl.
    { f_equal. lia. }
    {
      rewrite /o_sub_off Hsome /=.
      f_equal. lia.
    }
  Qed.

  Lemma eval_o_field :
  ∀ σ (f : name) (n : atomic_name) (cls : name) (st : Struct),
    f = Field cls n ->
    glob_def σ cls = Some (Gstruct st) ->
    s_layout st = POD \/ s_layout st = Standard ->
    eval_offset σ (o_field σ f) = offset_of σ cls n.
  Proof.
  Admitted.

  Lemma eval_offset_resp_norm :
    ∀ σ os,
      roff_canon os ->
      eval_offset_aux σ (normalize os) = eval_offset_aux σ os.
  Proof.
    move=> σ os Hc.
    have H : normalize os = os
      by apply norm_invol.
    by rewrite H.
  Qed.

  Lemma bind_assoc {A} :
    ∀ (m : option A) (k1 k2 : A -> option A),
      (m >>= k1) >>= k2 = m >>= λ x, k1 x >>= k2.
  Proof.
    move=> m k1 k2.
    by destruct m.
  Qed.

  Lemma norm_resp_eval_offset :
    ∀ σ os,
      eval_offset_aux σ os ≠ None ->
      eval_offset_aux σ (normalize os) = eval_offset_aux σ os.
  Proof.
    move=> σ os s.
    funelim (normalize os).
    2: done. clear H1.
    apply find_redex_pass in H.
    move: H => [Heq Hrw]. subst.
    clear - Hrw s0 H0.
    rewrite H0; clear H0.
    2:{
      induction l;
      simpl in *.
      {
        destruct Hrw;
        simpl in *.
        {
          unfold o_derived_off, o_base_off in *.
          destruct (parent_offset _ _ _);
          simpl in *; try done.
          destruct (eval_offset_aux σ r);
          simpl in *; done.
        }
        {
          unfold o_derived_off, o_base_off in *.
          destruct (parent_offset _ _ _);
          simpl in *; try done.
          destruct (eval_offset_aux σ r);
          simpl in *; done.
        }
        {
          unfold o_sub_off in *.
          destruct (size_of _ _);
          simpl in *; try done.
          destruct (eval_offset_aux _ _);
          simpl in *; done.
        }
        {
          unfold o_sub_off in *.
          destruct (size_of _ _);
          simpl in *; try done.
          destruct (eval_offset_aux _ _);
          simpl in *; done.
        }
      }
      {
        destruct (eval_offset_seg σ a);
        simpl in *; try done.
        destruct (eval_offset_aux σ (l ++ s ++ r));
        simpl in *; try done.
        assert (Some z0 ≠ None) by done.
        apply IHl in H.
        destruct (eval_offset_aux _ _);
        simpl in *; done.
      }
    }
    induction l;
    simpl in *.
    {
      destruct Hrw;
      simpl in *.
      {
        unfold o_derived_off, o_base_off in *.
        destruct (parent_offset _ _ _);
        simpl in *; try done.
        destruct (eval_offset_aux σ r);
        simpl in *; try done.
        f_equal. lia.
      }
      {
        unfold o_derived_off, o_base_off in *.
        destruct (parent_offset _ _ _);
        simpl in *; try done.
        destruct (eval_offset_aux σ r);
        simpl in *; try done.
        f_equal. lia.
      }
      {
        unfold o_sub_off in *.
        destruct (size_of _ _);
        simpl in *; try done.
        destruct (eval_offset_aux _ _);
        simpl in *; done.
      }
      {
        unfold o_sub_off in *.
        destruct (size_of _ _);
        simpl in *; try done.
        destruct (eval_offset_aux _ _);
        simpl in *; try done.
        f_equal. lia.
      }
    }
    {
      destruct (eval_offset_seg σ a);
      simpl in *; try done.
      destruct (eval_offset_aux σ (l ++ s ++ r));
      simpl in *; try done.
      by rewrite IHl.
    }
  Qed.

  Lemma eval_offset_dot :
    ∀ σ (o1 o2 : offset) s1 s2,
    eval_offset σ o1 = Some s1 ->
    eval_offset σ o2 = Some s2 ->
    eval_offset σ (o1 ,, o2) = Some (s1 + s2).
  Proof.
    UNFOLD_dot. rewrite /eval_offset.
    move=> σ [o1 H1] [o2 H2] s1 s2 H3 H4.
    simpl in *. clear - H3 H4.
    rewrite norm_resp_eval_offset.
    2:{
      generalize dependent s1.
      induction o1; simpl in *.
      { by rewrite H4. }
      {
        destruct (eval_offset_seg σ a);
        simpl in *; try done.
        destruct (eval_offset_aux σ (o1 ++ o2)).
        { done. }
        {
          intros. exfalso.
          eapply IHo1 with (s1:= s1 - z).
          {
            destruct (eval_offset_aux σ o1);
            simpl in *; try done.
            inversion H3. subst.
            f_equal. lia.
          }
          { done. }
        }
      }
    }
    generalize dependent s1.
    induction o1; simpl in *;
    intros.
    {
      rewrite H4.
      inversion H3.
      subst. f_equal.
    }
    {
      destruct (eval_offset_seg σ a);
      simpl in *; try done.
      rewrite (IHo1 (s1 - z)).
      2:{
        destruct (eval_offset_aux σ o1);
        simpl in *; try done.
        inversion H3. subst.
        f_equal. lia.
      }
      simpl. f_equal. lia.
    }
  Qed.

  Definition ptr_vaddr σ (p : ptr) : option vaddr :=
    match p with
    | invalid_ptr_ => None
    | offset_ptr p o =>
      match eval_offset σ o with
      | None => None
      | Some o =>
        let c : N := match p with
        | nullptr_ => 0%N
        | fun_ptr_ tu o => global_ptr_encode_vaddr o
        | global_ptr_ tu o => global_ptr_encode_vaddr o
        | alloc_ptr_ aid va => va
        end in
        match o with
        | Z0 => Some c
        | Z.pos o => Some (c + Npos o)%N
        | _ => None
        end
      end
    end.

  Lemma ptr_vaddr_resp_leq :
    ∀ σ1 σ2,
      genv_leq σ1 σ2 ->
      @ptr_vaddr σ1 = @ptr_vaddr σ2.
  Proof.
    move=> σ1 σ2 H.
    rewrite /ptr_vaddr.
    extensionality p.
    destruct p. easy.
  Admitted.

  Lemma ptr_vaddr_nullptr :
    ∀ σ, @ptr_vaddr σ nullptr = Some 0%N.
  Proof.
  Admitted.

  Lemma ptr_vaddr_o_sub_eq :
    ∀ σ p ty n1 n2 sz,
      size_of σ ty = Some sz -> (sz > 0)%N ->
      same_property (@ptr_vaddr σ) (p ,, o_sub σ ty n1) (p ,, o_sub σ ty n2) ->
      n1 = n2.
  Admitted.

  Lemma global_ptr_nonnull_addr :
    ∀ σ tu o, @ptr_vaddr σ (global_ptr tu o) <> Some 0%N.
  Admitted.

  Lemma global_ptr_nonnull_aid :
    ∀ tu o,
      ptr_alloc_id (global_ptr tu o) <> Some null_alloc_id.
  Admitted.

  Lemma global_ptr_inj :
    ∀ tu, Inj (=) (=) (global_ptr tu).
  Admitted.

  Lemma global_ptr_addr_inj :
    ∀ σ tu, Inj (=) (=) (λ o, @ptr_vaddr σ (global_ptr tu o)).
  Admitted.

  Lemma global_ptr_aid_inj :
    ∀ tu, Inj (=) (=) (λ o, ptr_alloc_id (global_ptr tu o)).
  Admitted.
  #[global] Existing Instances global_ptr_inj global_ptr_addr_inj global_ptr_aid_inj.

  Include PTRS_DERIVED.
  Include PTRS_MIXIN.
End PTRS_IMPL.
