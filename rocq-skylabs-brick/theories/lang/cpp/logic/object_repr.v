(*
 * Copyright (c) 2022-2025 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(** [object_repr.v] contains bundled definitions and utilities which are useful
    when operating on (or reasoning about) the "object representation" of a C++
    object (cf. <https://eel.is/c++draft/basic.types.general#4>). In BRiCk,
    [rawR]/[rawsR] - which are wrappers around [Vraw] [val]ues and lists of them,
    respectively - are used to refer to and manipulate these "object representations".
 *)
Require Import bluerock.iris.extra.proofmode.proofmode.
Require Import bluerock.prelude.base.

Require Import bluerock.iris.extra.bi.big_op.
Require Import bluerock.lang.cpp.semantics.
Require Import bluerock.lang.cpp.logic.arr.
Require Import bluerock.lang.cpp.logic.pred.
Require Import bluerock.lang.cpp.logic.heap_pred.
Require Import bluerock.lang.cpp.logic.layout.
Require Import bluerock.lang.cpp.logic.raw.

Section Utilities.
  Context `{Σ : cpp_logic} {σ : genv}.

  #[local]
  Lemma big_sepL_shift_aux_N {PROP : bi} {p : ptr} {ty : type} (P : ptr -> PROP) (j : N) {n m : N} :
    (j <= n)%N ->
        ([∗list] i ∈ seqN n m, P (p .[ ty ! Z.of_N i ]))
    -|- ([∗list] i ∈ seqN j m, P (p .[ ty ! Z.of_N (n - j) ] .[ty ! Z.of_N i ])).
  Proof.
    setoid_rewrite o_sub_sub.
    intros Hsz.
    rewrite {Hsz} (big_sepL_seqN_shift _ _ Hsz).
    f_equiv => _ i.
    by rewrite N2Z.inj_add.
  Qed.

  #[local]
  Lemma big_sepL_shift_aux_nat {PROP : bi} {p : ptr} {ty : type} (P : ptr -> PROP) (j : nat) {n m : nat}  :
    (j <= n)%nat ->
        ([∗list] i ∈ seq n m, P (p .[ ty ! Z.of_nat i ]))
    -|- ([∗list] i ∈ seq j m, P (p .[ ty ! Z.of_nat (n - j) ] .[ty ! Z.of_nat i ])).
  Proof.
    intros Hsz.
    setoid_rewrite o_sub_sub.
    rewrite {Hsz} (big_sepL_seq_shift _ _ Hsz).
    f_equiv => _ i.
    by rewrite Nat2Z.inj_add.
  Qed.

  Lemma big_sepL_shift_N {PROP : bi} (P : ptr -> PROP) (n m : N) :
    forall (p : ptr) (ty : type),
          ([∗list] i ∈ seqN n m, P (p .[ ty ! Z.of_N i ]))
      -|- ([∗list] i ∈ seqN 0 m, P (p .[ ty ! Z.of_N n ] .[ty ! Z.of_N i ])).
  Proof.
    intros p ty.
    rewrite (big_sepL_shift_aux_N P 0 ltac:(lia)).
    f_equiv=> _ i; by rewrite N.sub_0_r.
  Qed.

  Lemma big_sepL_shift_nat {PROP : bi} (P : ptr -> PROP) (n m : nat) :
    forall (p : ptr) (ty : type),
          ([∗list] i ∈ seq n m, P (p .[ ty ! Z.of_nat i ]))
      -|- ([∗list] i ∈ seq 0 m, P (p .[ ty ! Z.of_nat n ] .[ty ! Z.of_nat i ])).
  Proof.
    intros p ty.
    rewrite (big_sepL_shift_aux_nat P 0 ltac:(lia)).
    f_equiv=> _ i; by rewrite Nat.sub_0_r.
  Qed.

  Lemma big_sepL_type_ptr_shift (n m : N) (p : ptr) (ty : type) :
          ([∗list] i ∈ seqN n m, type_ptr ty (p .[ ty ! Z.of_N i ]))
      -|- ([∗list] i ∈ seqN 0 m, type_ptr ty (p .[ ty ! Z.of_N n ] .[ty ! Z.of_N i ] )).
  Proof. by apply big_sepL_shift_N. Qed.

  Lemma big_sepL_type_ptr_shift' (n m : nat) (p : ptr) (ty : type) :
          ([∗list] i ∈ seq n m, type_ptr ty (p .[ ty ! Z.of_nat i ]))
      -|- ([∗list] i ∈ seq 0 m, type_ptr ty (p .[ ty ! Z.of_nat n ] .[ty ! Z.of_nat i ] )).
  Proof. by apply big_sepL_shift_nat. Qed.
End Utilities.

Section rawsR_transport.
  Context `{Σ : cpp_logic} {σ : genv}.

  Lemma _at_rawsR_ptr_congP_transport (p1 p2 : ptr) (q : cQp.t) (rs : list raw_byte) :
        ptr_congP σ p1 p2 ** ([∗list] i ∈ seqN 0 (lengthN rs), type_ptr Tbyte (p2 .[ Tbyte ! Z.of_N i ]))
    |-- p1 |-> rawsR q rs -* p2 |-> rawsR q rs.
  Proof.
    generalize dependent p2; generalize dependent p1; induction rs;
      iIntros (p1 p2) "[#congP tptrs]"; iAssert (ptr_congP σ p1 p2) as "(% & #tptr1 & #tptr2)"=> //.
    - rewrite /rawsR !arrayR_nil !_at_sep !_at_only_provable !_at_validR.
      iIntros "[_ %]"; iFrame "%"; iApply (type_ptr_valid with "tptr2").
    - rewrite /rawsR !arrayR_cons !_at_sep !_at_type_ptrR !_at_offsetR; fold (rawsR q rs).
      iIntros "[_ [raw raws]]"; iFrame "#"; iSplitL "raw".
      + iApply (rawR_ptr_congP_transport with "congP"); iFrame "∗".
      + destruct rs.
        * rewrite /rawsR !arrayR_nil !_at_sep !_at_only_provable !_at_validR.
          iDestruct "raws" as "[#valid %]"; iFrame "%".
          iApply type_ptr_valid_plus_one; iFrame "#".
        * specialize (IHrs (p1 .[ Tbyte ! 1 ]) (p2 .[ Tbyte ! 1 ])).

          iDestruct (observe (type_ptr Tbyte (p1 .[ Tbyte ! 1 ])) with "raws") as "#tptr1'". 1: {
            rewrite /rawsR arrayR_cons; apply: _.
          }

          iDestruct (observe (type_ptr Tbyte (p2 .[ Tbyte ! 1 ])) with "tptrs") as "#tptr2'". 1: {
            rewrite !lengthN_cons !N.add_1_r !seqN_S_start/=; apply: _.
          }

          rewrite lengthN_cons N.add_1_r seqN_S_start/=.
          rewrite big_sepL_type_ptr_shift; auto.
          replace (Z.of_N 1) with 1%Z by lia.
          iDestruct "tptrs" as "#[tptr' tptrs]".

          iApply (IHrs with "[tptrs]"); iFrame "#∗".
          iPureIntro. exact: ptr_cong_o_sub.
  Qed.
End rawsR_transport.

(* Definitions to ease consuming and reasoning about the collection of [type_ptr Tbyte]
   facts induced by [type_ptr_obj_repr].
 *)
Section raw_type_ptrs.
  Context `{Σ : cpp_logic} {σ : genv}.

  (* [obj_type_ptr ty p] collects all of the constituent [type_ptr Tbyte] facts
     for the "object representation" of an object of type [ty] rooted at [p].
   *)
  Definition raw_type_ptrs_def (ty : type) (p : ptr) : mpred :=
    Exists (sz : N),
      [| size_of σ ty = Some sz |] **
      [∗list] i ∈ seqN 0 sz, type_ptr Tbyte (p .[ Tbyte ! Z.of_N i ]).
  Definition raw_type_ptrs_aux : seal (@raw_type_ptrs_def). Proof. by eexists. Qed.
  Definition raw_type_ptrs := raw_type_ptrs_aux.(unseal).
  Definition raw_type_ptrs_eq : @raw_type_ptrs = _ := raw_type_ptrs_aux.(seal_eq).

  (* [obj_type_ptr ty p] collects all of the constituent [type_ptr Tbyte] facts
     for the "object representation" of an object of type [ty] rooted at [p].
   *)
  Definition raw_type_ptrsR_def (ty : type) : Rep := as_Rep (raw_type_ptrs ty).
  Definition raw_type_ptrsR_aux : seal (@raw_type_ptrsR_def). Proof. by eexists. Qed.
  Definition raw_type_ptrsR := raw_type_ptrsR_aux.(unseal).
  Definition raw_type_ptrsR_eq : @raw_type_ptrsR = _ := raw_type_ptrsR_aux.(seal_eq).

  #[global] Hint Opaque raw_type_ptrsR : br_opacity.

  Lemma type_ptr_raw_type_ptrs :
    forall (ty : type) (p : ptr),
      is_Some (size_of σ ty) ->
      type_ptr ty p |-- raw_type_ptrs ty p.
  Proof.
    intros * Hsz; rewrite raw_type_ptrs_eq/raw_type_ptrs_def.
    destruct Hsz as [sz Hsz].
    iIntros "#tptr"; iExists sz; iFrame "%".
    by iApply type_ptr_obj_repr.
  Qed.

  Section Instances.
    #[global]
    Instance raw_type_ptrs_persistent : forall p ty,
      Persistent (raw_type_ptrs ty p).
    Proof. rewrite raw_type_ptrs_eq/raw_type_ptrs_def; apply: _. Qed.
    #[global]
    Instance raw_type_ptrsR_persistent : forall ty,
      Persistent (raw_type_ptrsR ty).
    Proof. rewrite raw_type_ptrsR_eq/raw_type_ptrsR_def; apply: _. Qed.

    #[global]
    Instance raw_type_ptrs_affine : forall p ty,
      Affine (raw_type_ptrs ty p).
    Proof. rewrite raw_type_ptrs_eq/raw_type_ptrs_def; apply: _. Qed.
    #[global]
    Instance raw_type_ptrsR_affine : forall ty,
      Affine (raw_type_ptrsR ty).
    Proof. rewrite raw_type_ptrsR_eq/raw_type_ptrsR_def; apply: _. Qed.

    #[global]
    Instance raw_type_ptrs_timeless : forall p ty,
      Timeless (raw_type_ptrs ty p).
    Proof. rewrite raw_type_ptrs_eq/raw_type_ptrs_def; apply: _. Qed.
    #[global]
    Instance raw_type_ptrsR_timeless : forall ty,
      Timeless (raw_type_ptrsR ty).
    Proof. rewrite raw_type_ptrsR_eq/raw_type_ptrsR_def; apply: _. Qed.

    Section observations.
      #[global]
      Instance raw_type_ptrs_type_ptr_Tbyte_obs (ty : type) (i : N) :
        forall (p : ptr) (sz : N),
          size_of σ ty = Some sz ->
          (i < sz)%N ->
          Observe (type_ptr Tbyte (p .[ Tbyte ! i ])) (raw_type_ptrs ty p).
      Proof.
        iIntros (p sz Hsz Hi) "#raw_tptrs !>".
        rewrite raw_type_ptrs_eq/raw_type_ptrs_def.
        iDestruct "raw_tptrs" as (sz') "[%Hsz' tptrs]".
        rewrite {}Hsz' in Hsz; inversion Hsz; subst.
        iStopProof.
        induction sz as [| sz' IHsz'] using N.peano_ind; first lia.
        iIntros "#tptrs".
        assert (i = sz' \/ i < sz')%N as [Hi' | Hi'] by lia;
          rewrite seqN_S_end_app big_opL_app; cbn;
          iDestruct "tptrs" as "(#tptrs & #tptr & _)";
          by [subst | iApply IHsz'].
      Qed.

      Lemma raw_type_ptrs_Tarray_elem (i : N) :
        forall (p : ptr) ty (cnt sz : N)
          (Hcnt : (cnt <> 0)%N) (Hsz : types.size_of σ ty = Some sz) (Hi : N.lt i cnt),
          raw_type_ptrs (Tarray ty cnt) p |-- raw_type_ptrs ty (p .[Tbyte ! sz * i]).
      Proof.
        intros **; iIntros "#raw_tptrs_array".
        rewrite raw_type_ptrs_eq/raw_type_ptrs_def.
        iDestruct "raw_tptrs_array" as (sz_array) "[%Hsz_array tptrs]".
        iExists sz; iSplit; first by iPureIntro.
        rewrite -N2Z.inj_mul -(big_sepL_type_ptr_shift (sz * i) sz p Tbyte).
        iApply (big_sepL_submseteq with "tptrs").
        apply sublist_submseteq.
        apply seqN_sublist; first by done.
        erewrite size_of_array in Hsz_array; eauto; inversion Hsz_array.
        rewrite N.add_0_l -N.mul_succ_r N.mul_comm.
        apply N.mul_le_mono_r.
        lia.
      Qed.

      #[global]
      Instance raw_type_ptrs_Tarray_elem_observe (i : N) :
        forall (p : ptr) ty (cnt sz : N)
          (Hcnt : (cnt <> 0)%N) (Hsz : types.size_of σ ty = Some sz) (Hi : N.lt i cnt),
          Observe (raw_type_ptrs ty (p .[Tbyte ! sz * i])) (raw_type_ptrs (Tarray ty cnt) p).
      Proof. intros **; rewrite (raw_type_ptrs_Tarray_elem i); eauto; by apply: _. Qed.

      #[global]
      Instance raw_type_ptrs_blockR_obs (ty : type) :
        forall (p : ptr) (sz : N) q,
          size_of σ ty = Some sz ->
          Observe (raw_type_ptrs ty p) (p |-> blockR sz q).
      Proof.
        intros * Hsz.
        rewrite blockR_eq/blockR_def raw_type_ptrs_eq/raw_type_ptrs_def !_at_sep.
        apply observe_sep_r.
        iIntros "anyRs".
        rewrite bi.persistently_exist; iExists sz.
        rewrite bi.persistently_sep; iSplitR "anyRs";
          first by (iModIntro; iPureIntro).
        rewrite _at_big_sepL.

        unshelve iDestruct (big_sepL_mono with "anyRs") as "H";
          [ by exact (fun _ v =>  <pers> type_ptr Tbyte (p .[Tbyte ! v]))%I
          | by intros k v Hlookup; cbn;
            rewrite _at_offsetR anyR_type_ptr_observe // _at_pers _at_type_ptrR
          | ]; cbn.
        rewrite -big_sepL_persistently; iDestruct "H" as "#tptrs"; iModIntro.

        (* NOTE (JH): There is probably a better way to relate these *)
        iStopProof.
        clear Hsz; generalize dependent p; induction sz using N.peano_ind=> p;
          iIntros "#tptrs"; first by done.
        rewrite seqN_S_start N2Nat.inj_succ; cbn.
        iDestruct "tptrs" as "[#tptr tptrs]"; iSplitL "tptr".
        - by replace (Z.of_nat 0) with 0%Z by lia.
        - rewrite big_sepL_type_ptr_shift big_sepL_type_ptr_shift'.
          specialize (IHsz (p .[Tbyte ! 1%N])).
          by iApply IHsz.
      Qed.
    End observations.
  End Instances.

  Section equivalences.
    Lemma _at_raw_type_ptrsR_equiv : forall (p : ptr) ty,
        p |-> raw_type_ptrsR ty -|- raw_type_ptrs ty p.
    Proof. by intros p ty; rewrite raw_type_ptrsR_eq/raw_type_ptrsR_def _at_as_Rep. Qed.

    Lemma raw_type_ptrs_arrayR_Tbyte_emp `(xs : list X) :
      forall (ty : type) (p : ptr) (sz : N),
        size_of σ ty = Some sz ->
        lengthN xs = sz ->
        xs <> nil ->
            raw_type_ptrs ty p
        -|- p |-> arrayR Tbyte (const emp) xs.
    Proof.
      intros * Hsz Hlen Hnonnil.
      rewrite raw_type_ptrs_eq/raw_type_ptrs_def.
      rewrite arrayR_eq/arrayR_def arrR_eq/arrR_def.
      split'.
      - iIntros "P"; iDestruct "P" as (sz') "[%Hsz' #tptrs]".
        rewrite !_at_sep !_at_offsetR !_at_only_provable.
        assert (is_Some (size_of σ Tbyte)) by eauto; iFrame "%".
        rewrite length_fmap length_lengthN Hlen N_nat_Z.
        rewrite Hsz' in Hsz; inversion Hsz; subst.
        iSplit.
        + rewrite (big_sepL_lookup _ _ (Nat.pred (length xs))). 2: {
            rewrite list_lookup_lookupN.
            eapply lookupN_seqN.
            intuition eauto.
            destruct xs; simpl; [by exfalso; apply Hnonnil |].
            rewrite /lengthN/=; lia.
          }
          rewrite N.add_0_l Nat2N.inj_pred; fold (lengthN xs).
          replace (Z.of_N (lengthN xs))
            with (N.pred (lengthN xs) + 1)%Z
            by (destruct xs; by [contradiction | rewrite /lengthN/=; lia]).
          rewrite -o_sub_sub _at_validR.
          by iApply type_ptr_valid_plus_one.
        + rewrite _at_big_sepL.
          iApply (big_sepL_mono (fun n _ => type_ptr Tbyte (p .[ Tbyte ! n ]))).
          2: {
            iStopProof; generalize dependent p; clear -Hnonnil;
              destruct xs as [| x xs]; first by contradiction.
            generalize dependent x; induction xs as [| x' xs IHxs];
              iIntros (x Hnonnil p) "#tptrs"; first done.
            specialize (IHxs x' ltac:(auto) (p .[ Tbyte ! 1 ])).
            rewrite fmap_cons big_sepL_cons.
            replace (lengthN (x :: x' :: xs))
              with (N.succ (lengthN (x' :: xs)))
              by (rewrite !lengthN_cons; lia).
            rewrite seqN_S_start big_sepL_cons.
            iDestruct "tptrs" as "[$ tptrs]".
            iApply (big_sepL_mono (fun n _ => type_ptr Tbyte (p .[ Tbyte ! 1 ] .[Tbyte ! n ])));
              first by (intros **; rewrite o_sub_sub;
                          by replace (Z.of_nat (S k)) with (1 + k)%Z by lia).
            iApply IHxs; iModIntro.
            by iApply (big_sepL_type_ptr_shift 1%N).
          }
          intros k y Hy.
          rewrite list_lookup_fmap in Hy.
          destruct (xs !! k); last by done.
          inversion Hy; subst.
          rewrite _at_offsetR _at_sep _at_emp _at_type_ptrR.
          iIntros "$".
      - rewrite !_at_sep !_at_offsetR _at_only_provable _at_validR _at_big_sepL.
        iIntros "(_ & _ & tptrs)".
        iExists sz; iFrame "%"; rewrite -Hlen; clear -Hnonnil.
        iDestruct (big_sepL_mono _ (fun n y => type_ptr Tbyte (p .[ Tbyte ! n ])) with "tptrs") as "tptrs".
        2: {
          iStopProof; generalize dependent p;
             destruct xs as [| x xs]; first by contradiction.
          generalize dependent x; induction xs as [| x' xs IHxs];
            iIntros (x Hnonnil p) "tptrs"; first by done.
          specialize (IHxs x' ltac:(auto) (p .[ Tbyte ! 1 ])).
          rewrite fmap_cons big_sepL_cons.
          replace (lengthN (x :: x' :: xs))
            with (N.succ (lengthN (x' :: xs)))
            by (rewrite !lengthN_cons; lia).
          rewrite seqN_S_start big_sepL_cons.
          iDestruct "tptrs" as "[$ tptrs]".
          iDestruct (big_sepL_mono _ (fun n _ => type_ptr Tbyte (p .[ Tbyte ! 1 ] .[Tbyte ! n ]))
                      with "tptrs") as "tptrs";
            first by (intros **; rewrite o_sub_sub;
                        by replace (Z.of_nat (S k)) with (1 + k)%Z by lia).
          iDestruct (IHxs with "tptrs") as "tptrs".
          by iApply (big_sepL_type_ptr_shift 1%N).
        }
        intros k y Hy.
        rewrite list_lookup_fmap in Hy.
        destruct (xs !! k); last by done.
        inversion Hy; subst.
        rewrite _at_offsetR _at_sep _at_emp _at_type_ptrR.
        iIntros "[$ _]".
    Qed.

    #[local]
    Lemma raw_type_ptrs_array_aux :
      forall (ty : type) (cnt : N) (p : ptr) (i sz : N),
        size_of σ ty = Some sz ->
            ([∗list] j ∈ seqN (i * sz) (cnt * sz)%N,
               type_ptr Tbyte (p .[ Tbyte ! Z.of_N (i * sz) ] .[ Tbyte ! Z.of_N j ]))
        -|- ([∗list] j ∈ seqN i cnt,
               raw_type_ptrs ty (p .[ Tbyte ! Z.of_N ((i + j) * sz) ])).
    Proof.
      intros ty cnt; induction cnt as [| cnt' IHcnt'] using N.peano_ind=> p i sz Hsz;
        first by rewrite N.mul_0_l !seqN_0.
      rewrite Nmult_Sn_m {1}/seqN N2Nat.inj_add seq_app -N2Nat.inj_add fmap_app.
      fold (seqN (i * sz) sz) (seqN (i * sz + sz)%N (cnt' * sz)).
      replace (i * sz + sz)%N with ((i + 1) * sz)%N by lia;
        rewrite big_sepL_app.
      rewrite seqN_S_start big_sepL_cons -N.add_1_r.
      specialize (IHcnt' (p .[ Tbyte ! -sz ]) (i + 1)%N sz Hsz).
      rewrite !o_sub_sub in IHcnt'.
      split'; iIntros "[P Q]"; iSplitL "P".
      - rewrite raw_type_ptrs_eq/raw_type_ptrs_def.
        iExists sz; iFrame "%".
        iDestruct (big_sepL_type_ptr_shift with "P") as "?"; auto.
        rewrite o_sub_sub.
        by replace (Z.add (Z.of_N (i * sz)) (Z.of_N (i * sz)))
          with (Z.of_N ((i + i) * sz))
          by lia.
      - iApply big_sepL_mono; last iApply IHcnt'.
        + intros **; simpl.
          rewrite o_sub_sub.
          by replace (Z.add (-sz) (Z.of_N ((i + 1 + y) * sz)))
            with (Z.of_N ((i + y) * sz))
            by lia.
        + iApply big_sepL_mono; last by iFrame.
          intros **; simpl.
          by replace (Z.add (-sz) (Z.of_N ((i + 1) * sz)))
            with (Z.of_N (i * sz))
            by lia.
      - rewrite raw_type_ptrs_eq/raw_type_ptrs_def.
        iDestruct "P" as (sz') "[%Hsz' tptrs]".
        rewrite Hsz' in Hsz; inversion Hsz; subst.
        iApply big_sepL_type_ptr_shift; auto.
        rewrite o_sub_sub.
        by replace (Z.add (Z.of_N (i * sz)) (Z.of_N (i * sz)))
          with (Z.of_N ((i + i) * sz))
          by lia.
      - iApply big_sepL_mono; last iApply IHcnt'.
        + intros **; simpl.
          by replace (Z.add (-sz) (Z.of_N ((i + 1) * sz)))
            with (Z.of_N (i * sz))
            by lia.
        + iApply big_sepL_mono; last by iFrame.
          intros **; simpl.
          rewrite o_sub_sub.
          by replace (Z.add (-sz) (Z.of_N ((i + 1 + y) * sz)))
            with (Z.of_N ((i + y) * sz))
            by lia.
    Qed.

    Lemma raw_type_ptrs_big_array :
      forall (p : ptr) (ty : type) (cnt sz : N),
        size_of σ ty = Some sz ->
            raw_type_ptrs (Tarray ty cnt) p
        -|- [∗list] i ∈ seqN 0 cnt, raw_type_ptrs ty (p .[ Tbyte ! Z.of_N (i * sz) ]).
    Proof.
      intros p ty cnt sz Hsz.
      pose proof (raw_type_ptrs_array_aux ty cnt p 0 sz Hsz) as Haux.
      split'; iIntros "P";
        rewrite offset_ptr_sub_0 // in Haux;
        rewrite raw_type_ptrs_eq/raw_type_ptrs_def.
      - iDestruct "P" as (array_sz) "[%Harray_sz tptrs]".
        apply size_of_array_shatter in Harray_sz as [sz' [? [Hsz' Harray_sz]]]; subst.
        rewrite Hsz' in Hsz; inversion Hsz; subst.
        rewrite N.mul_0_l in Haux; rewrite Haux.
        iApply big_sepL_mono; last by iFrame.
        intros k y Hk=> /=.
        by rewrite raw_type_ptrs_eq/raw_type_ptrs_def N.add_0_l.
      - pose proof (size_of_array ty cnt sz Hsz).
        iExists (cnt * sz)%N; iFrame "%".
        iApply Haux.
        iApply big_sepL_mono; last by iFrame.
        intros k y Hk=> /=.
        by rewrite raw_type_ptrs_eq/raw_type_ptrs_def N.add_0_l.
    Qed.
  End equivalences.
End raw_type_ptrs.
#[global] Arguments raw_type_ptrs {_ _ Σ σ} _ _.
#[global] Arguments raw_type_ptrsR {_ _ Σ σ} _.
#[global] Hint Opaque raw_type_ptrs raw_type_ptrsR : typeclass_instances.

Section primR_transport.
  Context `{Σ : cpp_logic} {σ : genv}.

  Lemma _at_primR_ptr_congP_transport p p' ty q v :
    ptr_congP σ p p' ** type_ptr ty p' |-- p |-> primR ty q v -* p' |-> primR ty q v.
  Proof.
    iIntros "#[cong tptr'] prim".
    iDestruct (type_ptr_size with "tptr'") as "%Hsz"; destruct Hsz as [sz Hsz].
    iDestruct (type_ptr_raw_type_ptrs with "tptr'") as "raw_tptrs"; eauto.
    rewrite raw_type_ptrs_eq/raw_type_ptrs_def.
    iDestruct "raw_tptrs" as (sz') "[%Hsz' tptrs]".
    rewrite Hsz' in Hsz; inversion Hsz; subst.
    rewrite primR_to_rawsR !_at_exists.
    iDestruct "prim" as (rs) "H"; iExists rs.
    rewrite !_at_sep !_at_only_provable !_at_type_ptrR.
    iDestruct "H" as "(%raw_bytes & _ & raws)"; iFrame "#%".
    pose proof (raw_bytes_of_val_sizeof raw_bytes) as Hlen.
    rewrite Hlen in Hsz'; inversion Hsz'; subst.
    rewrite lengthN_fold.
    iRevert "raws".
    iApply _at_rawsR_ptr_congP_transport.
    by iFrame "#".
  Qed.
End primR_transport.

(* [Rep]s which can be encoded as [raw] bytes enjoy certain transport and cancellation properties *)
Section with_rawable.
  Context `{Σ : cpp_logic} {σ : genv}.
  Context {X : Type} (R : cQp.t -> X -> Rep).
  Context (decode : list raw_byte -> X -> Prop) (encode : X -> list raw_byte -> Prop).
  Context (enc_dec_uniq : forall (x x' : X) (raws : list raw_byte),
              encode x raws -> decode raws x' -> x = x').
  (* NOTE (JH): structs with padding are rawable, but this direction is too strict to permit
     the nondeterminism inherent in the representation of padding.
   *)
  (* Context (dec_enc_uniq : forall (x x' : X) (raws : list raw_byte), *)
  (*             decode raws x -> encode x raws' -> ). *)
  Context (ty : type) (sz : N) (Hsz : size_of σ ty = Some sz) (Hnonzero : (sz <> 0)%N).
  Context (Hdecode_sz : forall (x : X) (rs : list raw_byte), decode rs x -> lengthN rs = sz).
  Context (Hencode_sz : forall (x : X) (rs : list raw_byte), encode x rs -> lengthN rs = sz).
  Context (HR_decode : forall (rs : list raw_byte) (p : ptr) q,
                             p |-> rawsR q rs ** type_ptr ty p
                         |-- Exists (x : X),
                                [| decode rs x |] ** p |-> R q x).
  Context (HR_encode : forall (x : X) (p : ptr) q,
                             p |-> R q x
                         |-- type_ptr ty p **
                             Exists (rs : list raw_byte),
                               [| encode x rs |] ** p |-> rawsR q rs).

  #[local] Lemma _at_rawable_R_obj_repr_aux (i : N) :
    forall (p : ptr) q (rs : list raw_byte),
          p .[ Tbyte ! i ] |-> rawsR q (dropN i rs)
      |-- p .[ Tbyte ! i ] |-> arrayR Tbyte (fun tt => anyR Tbyte q)
                                        (replicateN (lengthN rs - i) ()).
  Proof.
    intros **; clear Hsz Hdecode_sz Hencode_sz Hnonzero HR_decode HR_encode.
    generalize dependent i; generalize dependent p.
    induction rs as [| r rs IHrs]; intros p i.
    - rewrite replicateN_0 dropN_nil /rawsR !arrayR_nil.
      done.
    - destruct i as [| i' _] using N.peano_ind=>//.
      + rewrite offset_ptr_sub_0; last done.
        specialize (IHrs (p .[ Tbyte ! 1 ]) 0%N).
        rewrite ->!N.sub_0_r in *.
        rewrite lengthN_cons replicateN_succ /rawsR !arrayR_cons
                !_at_sep !_at_offsetR.
        iIntros "(#tptr & raw & raws)".
        iFrame "#"; iSplitL "raw".
        * rewrite rawR.unlock. by rewrite anyR_tptsto_fuzzyR_val_2.
        * rewrite offset_ptr_sub_0 in IHrs; last done.
          iApply IHrs.
          rewrite dropN_zero /rawsR _at_type_ptrR; iFrame "#∗".
      + replace (dropN (N.succ i') (r :: rs))
          with (dropN i' rs)
          by (rewrite -N.add_1_r dropN_cons_succ//).
        rewrite lengthN_cons.
        replace (lengthN rs + 1 - N.succ i')%N
          with (lengthN rs - i')%N
          by lia.
        specialize (IHrs (p .[ Tbyte ! 1 ]) i').
        rewrite o_sub_sub in IHrs.
        replace (1 + Z.of_N i')%Z with (Z.of_N (N.succ i')) in IHrs by lia.
        by iApply IHrs.
  Qed.

  Lemma _at_rawable_R_arrayR_anyR :
    forall (p : ptr) q (x : X),
          p |-> R q x
      |-- p |-> arrayR Tbyte (fun tt => anyR Tbyte q) (replicateN sz ()).
  Proof using encode ty Hsz Hencode_sz Hnonzero HR_encode.
    intros **.
    rewrite HR_encode.
    iIntros "[#tptr H]"; iDestruct "H" as (rs) "[%Hrs raws]".
    pose proof (_at_rawable_R_obj_repr_aux 0 p q rs) as Haux.
    rewrite offset_ptr_sub_0 in Haux; last done.
    rewrite dropN_zero N.sub_0_r (Hencode_sz x) in Haux; last by assumption.
    by iApply Haux.
  Qed.

  Lemma _at_rawable_R_anyR :
    forall (p : ptr) q (x : X),
          p |-> R q x
      |-- p |-> anyR (Tarray Tbyte sz) q.
  Proof using encode ty Hsz Hencode_sz Hnonzero HR_encode.
    intros **; rewrite anyR_array repeatN_replicateN.
    by apply _at_rawable_R_arrayR_anyR.
  Qed.

  Lemma R_ptr_congP_transport_via_rawsR :
    forall (p p' : ptr) q (x : X),
      ptr_congP σ p p' ** type_ptr ty p' |-- p |-> R q x -* p' |-> R q x.
  Proof using decode encode enc_dec_uniq sz Hdecode_sz Hencode_sz Hsz HR_decode HR_encode Hnonzero.
    intros p p' q x; rewrite HR_encode.
    iIntros "#[cong tptr'] [#tptr H]"; iDestruct "H" as (rs) "[%Henc raws]".
    iDestruct (type_ptr_raw_type_ptrs with "tptr'") as "#raw_tptrs'"; auto.
    assert (rs <> []) as Hrs_nonnil
        by (intro CONTRA; subst; specialize (Hencode_sz x [] Henc);
            apply Hnonzero; rewrite -Hencode_sz; by apply lengthN_nil).
    rewrite raw_type_ptrs_eq/raw_type_ptrs_def.
    iDestruct "raw_tptrs'" as (sz') "[%Hsz' tptrs']".
    rewrite Hsz in Hsz'; inversion Hsz'; subst.
    assert (sz' = lengthN rs) as -> by (by erewrite <- Hencode_sz).
    iDestruct (_at_rawsR_ptr_congP_transport with "[$] [$]") as "raws'".
    iCombine "raws' tptr'" as "H".
    iDestruct (HR_decode with "H") as "H".
    iDestruct "H" as (x') "[%Hdec R]".
    by rewrite (enc_dec_uniq x x' rs).
  Qed.
End with_rawable.

Section blockR_transport.
  Context `{Σ : cpp_logic} {σ : genv}.

  Lemma blockR_ptr_congP_transport_raw (sz : N) :
    forall (p p' : ptr) (ty : type) q,
      size_of σ ty = Some sz ->
          ptr_congP σ p p' ** raw_type_ptrs ty p'
      |-- p |-> blockR sz q -* p' |-> blockR sz q.
  Proof.
    iIntros (p p' ty q Hty) "[#cong #raw_tptrs'] block".
    iDestruct (raw_type_ptrs_blockR_obs with "block") as "#raw_tptrs"; eauto.
    assert (sz = 0 \/ 0 < sz)%N as [Hsz | Hsz] by lia.
    - subst; rewrite blockR_eq/blockR_def !_at_sep !_at_offsetR/=.
      rewrite !offset_ptr_sub_0 // !_at_emp.
      iDestruct "block" as "[_ $]".
      rewrite _at_validR.
      iDestruct "cong" as "#(cong & tptr & tptr')".
      by iApply type_ptr_valid.
    - rewrite blockR_eq/blockR_def !_at_sep !_at_offsetR.
      iDestruct "block" as "[block_valid block]"; iSplit.
      + iDestruct (raw_type_ptrs_type_ptr_Tbyte_obs
                     ty (N.pred sz) p' sz Hty ltac:(lia)
                    with "raw_tptrs'")
          as "#tptr_end'".
        rewrite !_at_validR.
        iDestruct (type_ptr_valid_plus_one with "tptr_end'") as "valid_end'".
        rewrite o_sub_sub.
        by have ->: (N.pred sz + 1)%Z = Z.of_N sz by lia.
      + rewrite !_at_big_sepL.
        (* TODO: find a strengthened [big_sepL] lemma for monotonicity in a given context *)
        rewrite raw_type_ptrs_eq/raw_type_ptrs_def.
        iDestruct "raw_tptrs" as (sz') "[%Hty' tptrs]".
        iDestruct "raw_tptrs'" as (sz'') "[%Hty'' tptrs']".
        rewrite Hty' in Hty; inversion Hty; subst; clear Hty.
        rewrite Hty'' in Hty'; inversion Hty'; subst; clear Hty' Hty''.
        iClear "block_valid".

        iDestruct "cong" as "-#cong".
        iDestruct "tptrs" as "-#tptrs".
        iDestruct "tptrs'" as "-#tptrs'".
        iRevert "block"; iStopProof.

        generalize dependent p'; generalize dependent p;
          induction sz as [| sz' IHsz'] using N.peano_ind;
          first by lia.

        assert (sz' = 0 \/ 0 < sz')%N as [Hsz' | Hsz'] by lia. 1: {
          iIntros (p p') "#(cong & tptrs & tptrs')"; subst.
          rewrite !N2Nat.inj_succ/= !_at_offsetR !offset_ptr_sub_0 //.
          rewrite !(right_id emp).
          iApply _at_anyR_ptr_congP_transport.
          (* TODO AUTO: Missing [Typeclasses Opaque ptr_congP]. *)
          iFrame "cong #".
        }

        iIntros (p p') "#(cong & tptrs & tptrs')".
        rewrite !seqN_S_start !N2Nat.inj_succ/=.
        rewrite !_at_offsetR !offset_ptr_sub_0 //.
        iDestruct "tptrs" as "[tptr tptrs]".
        iDestruct "tptrs'" as "[tptr' tptrs']".
        iIntros "[any REST]"; iSplitL "any".
        * iRevert "any"; iApply _at_anyR_ptr_congP_transport.
          by iFrame "cong tptr'".
        * rewrite !(big_sepL_type_ptr_shift 1 sz'); eauto.
          specialize (IHsz' Hsz' (p .[ Tbyte ! 1%N ]) (p' .[ Tbyte ! 1%N ])).
          iDestruct (IHsz' with "[]") as "IH".
          -- iFrame "tptrs tptrs'"; unfold ptr_congP.
             iDestruct "cong" as "(%Hcong & _ & _)".
             iSplitR.
             ++ iPureIntro. exact: ptr_cong_o_sub.
             ++ iSplitL "tptrs"; destruct sz' using N.peano_ind; try lia;
                  rewrite seqN_S_start/= !offset_ptr_sub_0 //.
                ** by iDestruct "tptrs" as "[$ _]".
                ** by iDestruct "tptrs'" as "[$ _]".
          -- setoid_rewrite _at_offsetR.
             rewrite !(big_sepL_shift_nat (λ p, p |-> anyR Tbyte q) 1 (N.to_nat sz')).
             by iRevert "REST".
  Qed.

  (* NOTE (JH): In practice this will likely be difficult to use due to the
     [type_ptr ty p'] obligation.
   *)
  Lemma blockR_ptr_congP_transport (sz : N) :
    forall (p p' : ptr) (ty : type) q,
      size_of σ ty = Some sz ->
          ptr_congP σ p p' ** type_ptr ty p ** type_ptr ty p'
      |-- p |-> blockR sz q -* p' |-> blockR sz q.
  Proof.
    intros **; iIntros "(cong & _ & tptr')".
    rewrite type_ptr_raw_type_ptrs; eauto.
    by iApply blockR_ptr_congP_transport_raw; eauto.
  Qed.
End blockR_transport.
