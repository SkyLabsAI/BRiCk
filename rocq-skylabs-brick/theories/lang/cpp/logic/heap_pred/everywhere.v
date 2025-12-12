(*
 * Copyright (c) 2023-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bluerock.lang.cpp.logic.heap_pred.prelude.
Require Import bluerock.lang.cpp.logic.rep_proofmode.
Require Import bluerock.lang.cpp.logic.arr.
Require Import bluerock.lang.cpp.logic.heap_pred.valid.
Require Import bluerock.lang.cpp.logic.heap_pred.null.
Require Import bluerock.lang.cpp.logic.heap_pred.simple.
Require Import bluerock.lang.cpp.logic.heap_pred.aggregate.
Require Import bluerock.lang.cpp.logic.heap_pred.tptsto.
Require Import bluerock.lang.cpp.logic.heap_pred.uninit.
Require Import bluerock.lang.cpp.logic.heap_pred.prim.

Section with_cpp.
  Context `{Σ : cpp_logic} {σ : genv}.

  (* UPSTREAM *)
  #[global] Instance has_type_has_type_prop_observe v t :
    Observe [| has_type_prop v t |] (has_type v t).
  Proof. rewrite has_type_has_type_prop. refine _. Qed.

  (** [mut_type m q] is the ownership [cQp.t] and the type used for a [Member] *)
  Definition mut_type (m : Member) (q : cQp.t) : cQp.t * Rtype :=
    let '(cv, ty) := decompose_type m.(mem_type) in
    let q := if q_const cv && negb m.(mem_mutable) then cQp.c q else q in
    (q, to_heap_type ty).

  Lemma mut_type_plus f q1 q2 :
    (mut_type f (q1 + q2)).1 = ((mut_type f q1).1 + (mut_type f q2).1)%cQp.
  Proof. rewrite /mut_type. case_match; case_match; simpl; auto. Qed.
  Lemma mut_type_plus_2 f a b :
    (mut_type f a).2 = (mut_type f b).2.
  Proof. rewrite /mut_type. case_match; case_match; simpl; auto. Qed.

  (** [qualify cv q] applies the <<const>> qualifier from [cv] to [q]. *)
  Definition qualify (tq : type_qualifiers) (q : cQp.t) : cQp.t :=
    if q_const tq then cQp.const q else q.

  Lemma qualify_plus t q1 q2
    : qualify t (q1 + q2)%cQp = (qualify t q1 + qualify t q2)%cQp.
  Proof.
    clear. rewrite /qualify/cQp.add/=. by case_match; eauto.
  Qed.

  Lemma qualify_frac q t : cQp.frac (qualify t q) = cQp.frac q.
  Proof. rewrite /qualify. case_match; done. Qed.

  Lemma qualify_mut q : qualify QM q = q.
  Proof. destruct q; reflexivity. Qed.

  Lemma qualify_merge_tq cv1 cv2 t
    : qualify cv1 (qualify cv2 t) = qualify (merge_tq cv1 cv2) t.
  Proof. rewrite /qualify. destruct cv1, cv2 => /=; eauto. Qed.

  Lemma join_lists {PROP : bi} {T U} (L : T -> PROP) (R' : U -> PROP)
                    ls rs :
    ([∗list] l ∈ ls, L l) ** ([∗list] r ∈ rs, R' r)
  -|- [∗list] lr ∈ (inl <$> ls) ++ (inr <$> rs),
      match lr with
      | inl l => L l
      | inr r => R' r
      end.
  Proof.
    clear.
    by rewrite big_opL_app !big_opL_fmap.
  Qed.
  (* END UPSTREAM *)

  (** [struct_def R cls st q] is the ownership of the class where [R ty q] is
      owned for each field and base class

      TODO: the use of [nil] in [derivationR] is justified only because it can
            be weakened, but this should probably be changed so that it tracks
            the actual initialized state.
   *)
  Definition struct_defR (R : Rtype -> cQp.t -> Rep) (cls : globname) (st : Struct) (q : cQp.t) : Rep :=
    ([** list] base ∈ st.(s_bases),
       _base cls base.1 |-> R (Tnamed base.1) q) **
    ([** list] fld ∈ st.(s_fields),
      let f := Field cls fld.(mem_name) in
      let qt := mut_type fld q in
      _field f |-> R qt.2 qt.1) **
    (if has_vtable st then derivationR cls nil q else emp) **
    structR cls q.

  (** [union_def R cls st q] is the ownership of the union where [R ty q] is
      owned for each field and base class *)
  Definition union_defR (R : Rtype -> cQp.t -> Rep) (cls : globname) (st : decl.Union) (q : cQp.t) : Rep :=
    Exists o,
      unionR cls q o **
      match o with
      | None => emp
      | Some idx =>
          Exists m, [| st.(u_fields) !! idx = Some m |] **
          let f := _field $ Field cls m.(mem_name) in
          let qt := mut_type m q in
          f |-> R qt.2 qt.1
      end.

  Section typeR.
    Variable tu : translation_unit.
    Variable R : cQp.t -> Rtype -> Rep.
    Variable rec : cQp.t -> Rtype -> Rep.

    (** [typeR] visits all of the primitive objects of a given object

        This currently discards <<volatile>> qualifiers.

        NOTE: The implementation could/should use [qual_norm].
      *)
    Fixpoint typeR (q : cQp.t) (t : Rtype) : Rep :=
      match t with
      | Tnum _ _
      | Tbool
      | Tvoid
      | Tchar_ _
      | Tfloat_ _
      | Tnullptr
      | Tptr _
      | Tref _
      | Trv_ref _
      | Tenum _
      | Tmember_pointer _ _
      | Tarch _ _ => R q t
      | Tnamed nm =>
          match tu.(types) !! nm with
          | Some (Gstruct s) =>
              struct_defR (fun ty q => rec q ty) nm s q
          | Some (Gunion u) =>
              union_defR (fun ty q => rec q ty) nm u q
          | _ => False
          end
      | Tarray ty n =>
          arrayR ty (fun _ => typeR q ty) (replicateN n tt)
      | Tincomplete_array _ => False
      | Tvariable_array _ _ => False

      | Tqualified tq ty => typeR (qualify tq q) ty
      | Tfunction _ => False
      | Tunsupported _ => False
      | Tresult_global _
      | Tparam _ | Tresult_param _
      | Tresult_unop _ _ | Tresult_binop _ _ _
      | Tresult_call _ _ | Tresult_member_call _ _ _
      | Tresult_member _ _
      | Tdecltype _
      | Texprtype _
      | Tauto
      | Tresult_parenlist _ _ => False
      end%I.

    #[local] Instance typeR_timeless
      (Trec : forall q ty, Timeless (rec q ty))
      (TprimR : forall q ty, Timeless (R q ty)) : forall q ty, Timeless (typeR q ty).
    Proof.
      move=> q ty; revert q; induction ty; simpl; intros; refine _.
      rewrite /struct_defR/union_defR.
      repeat (case_match; refine _).
    Qed.

    #[local] Instance typeR_valid
      (TprimR : forall q ty, Observe validR (R q ty)) : forall q ty, Observe validR (typeR q ty).
    Proof.
      move=> q ty; revert q; induction ty; simpl; intros; refine _.
      rewrite /struct_defR/union_defR.
      repeat (case_match; refine _).
    Qed.

    #[local] Instance typeR_nonnull
      (TR : forall q ty, Observe nonnullR (R q ty)) :
      forall ty, ~zero_sized_array ty -> forall q, Observe nonnullR (typeR q ty).
    Proof.
      induction ty; try solve [ simpl; intros; refine _ ].
      { simpl; intros; revert H. rewrite /qual_norm/=. case_bool_decide => //.
        intros.
        have->: n = ((n - 1) + 1)%N by lia.
        rewrite replicateN_succ.
        rewrite arrayR_cons. refine _. }
      { simpl; intros.
        case_match; refine _.
        case_match; refine _. }
      { intros. eapply IHty.
        by rewrite -zero_sized_array_qual in H. }
    Qed.

    #[local] Instance typeR_cfractional
      (Trec : forall ty, CFractional (fun q => rec q ty))
      (TprimR : forall ty, CFractional (fun q => R q ty)) : forall ty, CFractional (fun q => typeR q ty).
    Proof.
      induction ty; simpl; refine _.
      { case_match; refine _.
        case_match; refine _.
        { rewrite /union_defR.
        red; intros.
        iSplit.
        { iIntros "A".
          iDestruct "A" as ([|]) "[[L R] A]".
          iDestruct "A" as (?) "[% A]".
          rewrite mut_type_plus Trec _offsetR_sep.
          iDestruct "A" as "[La Ra]".
          iSplitL "L La".
          { iExists _; iFrame.
            iExists _; iFrame "%".
            erewrite mut_type_plus_2. eauto. }
          { iExists _; iFrame.
            iExists _; iFrame "%".
            erewrite mut_type_plus_2. eauto. }
          { iSplitL "L". iExists _; iFrame.
            iExists _; iFrame. } }
        { iIntros "[L R]".
          iDestruct "L" as (?) "[Lu L]".
          iDestruct "R" as (?) "[Ru R]".
          iDestruct (unionR_agree with "Lu Ru") as "%"; subst.
          iExists _.
          iCombine "Lu Ru" as "$".
          case_match; eauto.
          iDestruct "L" as (?) "[% L]".
          iDestruct "R" as (?) "[% R]".
          iExists _; iFrame "%".
          rewrite mut_type_plus.
          rewrite (mut_type_plus_2 _ q1 q2).
          rewrite (mut_type_plus_2 _ (q1 + q2) q2).
          rewrite Trec.
          have->: m = m0 by congruence.
          iFrame. } }
      { rewrite /struct_defR.
        repeat eapply cfractional_sep; refine _.
        { eapply cfractional_big_sepL; intros.
          eapply _offsetR_cfractional.
          red. intros. rewrite mut_type_plus. rewrite Trec.
          erewrite (mut_type_plus_2 _ q1 _).
          erewrite (mut_type_plus_2 _ q2 _). reflexivity. }
        { case_match; refine _. eapply derivationR_cfractional. } } }
      { intro. intros.
        rewrite qualify_plus. apply IHty. }
    Qed.

  End typeR.

  Lemma typeR_mono' R R' rec rec' tu tu' :
    sub_module tu tu' ->
    forall ty (o : offset) q,
        □ (Forall (o : offset) a b, o |-> R a b -* o |-> R' a b)
    |-- □ (Forall (o : offset) a b, o |-> rec a b -* o |-> rec' a b) -*
        o |-> typeR tu R rec q ty -* o |-> typeR tu' R' rec' q ty.
  Proof.
    induction ty; simpl; intros; iIntros "#A #B";
      try solve [ iApply "A" | iIntros "[]" ].
    - iStopProof.
      revert o.
      induction (replicateN n ()); simpl; intros.
      { rewrite !arrayR_nil. iIntros "#? $". }
      { rewrite !arrayR_cons !_offsetR_sep !_offsetR_offsetR.
        iIntros "#[H1 H2] [$ [L R]]".
        iSplitL "L".
        { iApply IHty; eauto. }
        iApply IHl; eauto. }
    - case_match; try iIntros "[]".
      case_match; try iIntros "[]".
      + have->: (types tu' !! gn = Some (Gunion u)) by apply (sub_module_preserves_gunion _ _ _ _ H H0).
        rewrite /union_defR !_offsetR_exists.
        iIntros "C".
        iDestruct "C" as (which) "C".
        iExists _.
        rewrite !_offsetR_sep.
        iDestruct "C" as "[$ C]".
        case_match; eauto.
        rewrite !_offsetR_exists.
        iDestruct "C" as (c) "C".
        iExists c.
        rewrite !_offsetR_sep !_offsetR_offsetR.
        iDestruct "C" as "[$ C]".
        iApply "B"; iFrame.
      + have->: (types tu' !! gn = Some (Gstruct s)) by apply (sub_module_preserves_gstruct _ _ _ _ H H0).
        rewrite /struct_defR !_offsetR_sep.
        iIntros "[X [Y [$ $]]]".
        iSplitL "X".
        { iStopProof. induction (s_bases s); simpl; eauto.
          iIntros "[#[X Y] [B C]]".
          rewrite !_offsetR_sep !_offsetR_offsetR.
          iSplitL "B".
          { iApply "Y"; eauto. }
          iApply IHl.
          iFrame "#∗". }
        { iStopProof. induction (s_fields s); simpl; eauto.
          iIntros "[#[X Y] [B C]]".
          rewrite !_offsetR_sep !_offsetR_offsetR.
          iSplitL "B".
          { iApply "Y"; eauto. }
          iApply IHl.
          iFrame "#∗". }
    - iApply IHty; eauto.
  Qed.

  Lemma typeR_mono R R' rec rec' tu tu' :
    sub_module tu tu' ->
    forall ty q,
        □ (Forall (o : offset) a b, o |-> R a b -* o |-> R' a b)
    |-- □ (Forall (o : offset) a b, o |-> rec a b -* o |-> rec' a b) -*
        typeR tu R rec q ty -* typeR tu' R' rec' q ty.
  Proof.
    intros.
    iIntros "#? #?".
    rewrite -(_offsetR_id (typeR _ _ rec _ _)) -(_offsetR_id (typeR _ _ rec' _ _)).
    iApply typeR_mono'; eauto.
  Qed.

  Section everywhereR.
    Variable tu : translation_unit.
    Variable R : cQp.t -> Rtype -> Rep.

    Fixpoint everywhereR_f (f : nat) {struct f} : cQp.t -> Rtype -> Rep :=
      match f with
      | 0 => fun _ _ => False%I
      | S f => typeR tu R (fun ty q => everywhereR_f f ty q)
      end%I.

    #[local] Instance everywhereR_f_timeless
      (TprimR : forall ty q, Timeless (R q ty)) : forall f ty q, Timeless (everywhereR_f f q ty).
    Proof.
      induction f; simpl; refine _.
      intros. apply typeR_timeless; eauto.
    Qed.

    #[local] Instance everywhereR_f_valid
      (TprimR : forall ty q, Observe validR (R q ty)) : forall f ty q, Observe validR (everywhereR_f f q ty).
    Proof.
      induction f; simpl; refine _.
      intros. apply typeR_valid; eauto.
    Qed.

    #[local] Instance everywhereR_f_nonnull
      (TR : forall q ty, Observe nonnullR (R q ty)) :
      forall f ty, ~zero_sized_array ty -> forall q, Observe nonnullR (everywhereR_f f q ty).
    Proof.
      induction f; simpl; refine _.
      intros. apply typeR_nonnull; eauto.
    Qed.

    #[local] Instance everywhereR_f_cfractional
      (TprimR : forall ty, CFractional (fun q => R q ty)) : forall f ty, CFractional (fun q => everywhereR_f f q ty).
    Proof.
      induction f; simpl; refine _.
      intros. apply typeR_cfractional; eauto.
    Qed.

    Lemma everywhereR_f_mono' f : forall f',
        f <= f' ->
        forall q (o : offset) ty,
      o |-> everywhereR_f f q ty |-- o |-> everywhereR_f f' q ty.
    Proof.
      induction f; simpl; intros; eauto.
      - iIntros "[]".
      - destruct f'; try lia.
        iApply typeR_mono'; eauto.
        + reflexivity.
        + iModIntro.
          iIntros (???). iApply IHf. lia.
    Qed.

    Definition everywhereR q t : Rep :=
      Exists f, everywhereR_f f q t.

    Lemma everywhereR_unfold (q : cQp.t) ty :
      everywhereR q ty -|- typeR tu R (fun q ty => everywhereR q ty) q ty.
    Proof.
      rewrite /everywhereR.
      iSplit.
      { iIntros "A"; iDestruct "A" as (f) "A".
        iStopProof.
        revert q ty. induction f; simpl; intros.
        - iIntros "[]".
        - iApply typeR_mono; eauto.
          + reflexivity.
          + iModIntro; iIntros (???) "A"; iExists _; eauto. }
      { iIntros; iStopProof.
        revert q.
        induction ty; simpl; intros;
          try solve [ iIntros "A"; iExists 1; simpl; auto ].
        { iIntros "B".
          rewrite arrayR_eq/arrayR_def arrR_eq/arrR_def /=.
          iDestruct "B" as "[V [S B]]".
          assert (forall q ls (O : _ -> offset),
              ([∗list] i↦Ri ∈ ((λ _ : (), typeR tu R (λ (q0 : cQp.t) (ty0 : type), Exists f, everywhereR_f f q0 ty0) q ty) <$> ls), O i |-> (type_ptrR ty ** Ri))
          |-- Exists f, [∗list] i↦Ri ∈ ((λ _ : (), typeR tu R (λ (q0 : cQp.t) (ty0 : type), everywhereR_f f q0 ty0) q ty) <$> ls), O i |-> (type_ptrR ty ** Ri)).
          { induction ls; simpl; intros.
            { iIntros "_"; iExists 0; eauto. }
            rewrite IHls !_offsetR_sep.
            iIntros "[[#A B] C]".
            iDestruct "C" as (f') "C".
            rewrite IHty.
            iDestruct "B" as (f) "B".
            rewrite (everywhereR_f_mono' f (S $ f `max` f')); last lia.
            simpl.
            iDestruct (IHls (fun i => O (S i)) with "[C]") as "C".
            {
              rewrite !big_sepL_fmap. iClear "A". iStopProof.
              f_equiv. red. intros. red. intros.
              rewrite !_offsetR_sep.
              iIntros "[$ A]".
              iApply typeR_mono'. reflexivity. 3: iApply "A".
              eauto.
              { iIntros "!>" (???). iIntros "A"; iExists _. eauto. } }
            { iDestruct "C" as (ff) "C".
              iExists (S $ ff `max` (f `max` f')).
              rewrite !_offsetR_sep. iFrame "#".
              iSplitL "B".
              { iClear "A"; iStopProof. iApply typeR_mono'; eauto. reflexivity.
                iIntros "!>" (???). iApply everywhereR_f_mono'. lia. }
              Opaque everywhereR_f.
              iClear "A". rewrite !big_sepL_fmap.
              iStopProof.
              f_equiv. red; intros; red; intros.
              rewrite !_offsetR_sep.
              f_equiv.
              iApply typeR_mono'. reflexivity. eauto.
              { iIntros "!>" (???). iApply everywhereR_f_mono'. lia. } }
            Transparent everywhereR_f. }
          iDestruct (H with "B") as "B".
          iDestruct "B" as (f) "B". iExists (S f).
          simpl. iFrame.
          rewrite arrayR_eq/arrayR_def arrR_eq/arrR_def.
          iFrame. rewrite !length_fmap. done. }
        { case_match; try iIntros "[]".
          case_match; try iIntros "[]".
          { rewrite /union_defR.
            iIntros "A"; iDestruct "A" as (o) "[? A]".
            case_match.
            { iDestruct "A" as (?) "(%&A)".
              iDestruct "A" as (f) "A".
              iExists (S f); simpl.
              rewrite H /union_defR.
              iExists o. subst.
              by iFrame. }
            { iExists 1. simpl.
              rewrite H /union_defR.
              iExists None. iFrame. } }
          { rewrite /struct_defR.
            transitivity (Exists f, everywhereR_f (S f) q (Tnamed gn)); last first.
            { iIntros "X"; iDestruct "X" as (?) "?"; iExists _; eauto. }
            simpl. rewrite H/struct_defR.
            iIntros "[A[B $]]".
            iStopProof.
            rewrite join_lists.
            setoid_rewrite join_lists.
            clear.
            match goal with
            | |- context [ ([∗list] _ ∈ ?L , _)%I ] => induction L
            end; simpl.
            { iIntros "_"; iExists 0%nat; done. }
            { rewrite IHl; clear IHl.
              iIntros "[A B]"; iDestruct "B" as (f') "B".
              destruct a;
                (iDestruct "A" as (f) "A";
                iExists (max f f');
                iSplitL "A";
                  [ iApply everywhereR_f_mono'; [ | eauto ]; lia
                  | iStopProof; f_equiv; do 2 intro;
                    case_match; apply everywhereR_f_mono'; lia ]). } } }
        { iIntros "A".
          iDestruct (IHty with "A") as (f) "A".
          iExists f.
          destruct f; simpl; eauto. } }
    Qed.

    Lemma everywhereR_Tqualified t tq q :
      everywhereR q (Tqualified tq t) -|- everywhereR (qualify tq q) t.
    Proof.
      by rewrite !everywhereR_unfold.
    Qed.

  End everywhereR.

End with_cpp.
