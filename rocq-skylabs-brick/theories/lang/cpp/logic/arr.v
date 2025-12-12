(*
 * Copyright (c) 2020-2025 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bluerock.iris.extra.algebra.list.
Require Import bluerock.iris.extra.proofmode.proofmode.
Require Import bluerock.prelude.numbers.
Require Import bluerock.iris.extra.bi.observe.
Require Import bluerock.iris.extra.bi.fractional.
Require Import bluerock.iris.extra.bi.big_op.
Require Import bluerock.lang.cpp.bi.cfractional.
Require Import bluerock.lang.cpp.semantics.types.
Require Import bluerock.lang.cpp.semantics.genv.
Require Import bluerock.lang.cpp.logic.pred.
Require Import bluerock.lang.cpp.logic.path_pred.
Require Import bluerock.lang.cpp.logic.heap_pred.valid.
Require Import bluerock.lang.cpp.semantics.values.

#[local] Set Printing Coercions.	(** Readability *)

(** PDS: Misplaced *)
#[local] Arguments N.of_nat _ : simpl never.
#[local] Arguments N.to_nat _ : simpl never.

#[local] Ltac iCancel :=
  iIntros; repeat iDestruct select (bi_sep _ _) as "[? ?]";
  iRevert "∗"; iIntros;
  iFrame "#∗".

Lemma size_of_array_0_Some σ ty :
  is_Some (size_of σ ty) → size_of σ (Tarray ty 0) = Some 0%N.
Proof. by move=>[]sz /= ->. Qed.
#[local] Hint Resolve size_of_array_0_Some : core.
Lemma size_of_array_0_None σ ty :
  size_of σ ty = None → size_of σ (Tarray ty 0) = None.
Proof. by move=>/= ->. Qed.
#[local] Hint Resolve size_of_array_0_None : core.

Section simpl_never.
  #[local] Arguments N.mul : simpl never.
  Lemma size_of_array_1 σ ty : size_of σ (Tarray ty 1) = size_of σ ty.
  Proof. simpl. case: (size_of _ ty) => //= s. f_equiv. apply: left_id. Qed.
End simpl_never.
#[local] Hint Resolve size_of_array_1 : core.

(** PDS: Misplaced *)
Section offsetR.
  Context `{Σ : cpp_logic}.

  Lemma monPred_at_offsetR offs (R : Rep) (p : ptr) :
    (_offsetR offs R) p -|- R (p ,, offs).
  Proof. by rewrite INTERNAL._offsetR_eq. Qed.
End offsetR.

Implicit Types (p : ptr) (σ : genv).

Section validR.
  Context `{Σ : cpp_logic} {resolve : genv}.

  Lemma type_ptrR_validR_plus_one ty :
    type_ptrR ty ⊢@{RepI} .[ ty ! 1 ] |-> validR .
  Proof.
    apply Rep_entails_at => p.
    rewrite _at_type_ptrR _at_offsetR _at_validR.
    exact: type_ptr_valid_plus_one.
  Qed.

  (** [validR] and [_at] *)

  (* Lemma _at_offsetR_validR p (o : offset) :
    _at p (_offsetR o validR) -|- valid_ptr (_offset_ptr p o).
  Proof. by rewrite _at_offsetR _at_validR. Qed. *)

  #[global] Instance _offsetR_sub_inv ty i :
    Observe [| is_Some (size_of resolve ty) |] (_offsetR (_sub ty i) validR).
  Proof.
    apply /observe_intro_persistent /Rep_entails_at => p.
    rewrite _at_offsetR _at_validR _at_only_provable.
    apply valid_o_sub_size.
  Qed.
End validR.

Definition arrR_def `{Σ : cpp_logic} {σ : genv} ty (Rs : list Rep) : Rep :=
  .[ ty ! length Rs ] |-> validR ** [| is_Some (size_of σ ty) |] **
  (* ^ both of these are only relevant for empty arrays, otherwise, they are implied by the
     following conjunct *)
  [∗ list] i ↦ Ri ∈ Rs, .[ ty ! Z.of_nat i ] |-> (type_ptrR ty ** Ri).
Definition arrR_aux : seal (@arrR_def). Proof. by eexists. Qed.
Definition arrR := arrR_aux.(unseal).
Definition arrR_eq : @arrR = _ := arrR_aux.(seal_eq).
Arguments arrR {_ _ _ _} _%_cpp_type _%_list_scope : assert.
#[global] Instance: Params (@arrR) 5 := {}.	(** TODO: [genv] weakening *)

Section arrR.
  Context `{Σ : cpp_logic, σ : genv}.

  #[global] Instance arrR_ne ty : NonExpansive (arrR ty).
  Proof.
    intros n l1 l2 Hl. rewrite arrR_eq /arrR_def.
    have Hlen := Forall2_length _ _ _ Hl.
    f_equiv. f_equiv. by rewrite Hlen. f_equiv.
    apply big_sepL_gen_ne; first done.
    move=>k y1 y2 Hl1 Hl2. apply _offsetR_ne, bi.sep_ne; first done.
    move: Hl =>/dist_Forall2 Hl.
    exact: Forall2_lookup_lr.
  Qed.

  #[global] Instance arrR_proper ty : Proper ((≡) ==> (≡)) (arrR ty).
  Proof.
    intros l1 l2 Hl. rewrite arrR_eq /arrR_def.
    have Hlen : length l1 = length l2 by apply (Forall2_length (≡)), list_equiv_Forall2.
    f_equiv. f_equiv. by rewrite Hlen. f_equiv.
    apply big_sepL_gen_proper; first done.
    move=>k y1 y2 Hl1 Hl2. apply _offsetR_proper, bi.sep_proper; first done.
    apply list_equiv_Forall2 in Hl.
    exact: Forall2_lookup_lr.
  Qed.

  #[global] Instance arrR_mono ty : Proper (Forall2 (⊢) ==> (⊢)) (arrR ty).
  Proof.
    intros l1 l2 Hl. rewrite arrR_eq /arrR_def.
    have Hlen : length l1 = length l2 by exact: Forall2_length.
    f_equiv. f_equiv. by rewrite Hlen. f_equiv.
    apply big_sepL_gen_mono; first done.
    move=>k y1 y2 Hl1 Hl2. apply _offsetR_mono, bi.sep_mono; first done.
    exact: Forall2_lookup_lr.
  Qed.

  #[global] Instance arrR_flip_mono ty : Proper (flip (Forall2 (⊢)) ==> flip (⊢)) (arrR ty).
  Proof. solve_proper. Qed.

  (** We don't register this as an instance because it doesn't hold in
      arbitrary non-affine BIs. *)
  Remark arrR_timeless_when_mpred_affine ty Rs :
    TCForall Timeless Rs → Timeless (arrR ty Rs).
  Proof.
    rewrite TCForall_Forall Forall_forall=>HR. rewrite arrR_eq /arrR_def.
    apply: bi.sep_timeless.
    apply: bi.sep_timeless.
    apply big_sepL_gen_timeless=>k x Hk.
    apply _offsetR_timeless, (bi.sep_timeless _ _ _), HR. exact: elem_of_list_lookup_2.
  Qed.
  #[global] Instance arrR_persistent ty Rs :
    TCForall Persistent Rs → Persistent (arrR ty Rs).
  Proof.
    rewrite TCForall_Forall Forall_forall=>HR. rewrite arrR_eq /arrR_def.
    apply: bi.sep_persistent.
    apply: bi.sep_persistent.
    apply big_sepL_gen_persistent=>k x Hk.
    apply _offsetR_persistent, (bi.sep_persistent _ _ _), HR. exact: elem_of_list_lookup_2.
  Qed.
  #[global] Instance arrR_affine ty Rs :
    TCForall Affine Rs → Affine (arrR ty Rs).
  Proof.
    rewrite TCForall_Forall Forall_forall=>HR. rewrite arrR_eq /arrR_def.
    apply: bi.sep_affine.
  Qed.

  #[global] Instance arrR_size_of_observe {ty ys} : Observe [| is_Some (size_of σ ty) |] (arrR ty ys).
  Proof. rewrite arrR_eq/arrR_def; apply _. Qed.

  #[global] Instance arrR_valid_end ty Rs : Observe (.[ ty ! length Rs ] |-> validR) (arrR ty Rs).
  Proof. rewrite arrR_eq /arrR_def /=. refine _. Qed.

  Lemma arrR_nil ty : arrR ty [] -|- validR ** [| is_Some (size_of σ ty) |].
  Proof.
    rewrite arrR_eq /arrR_def /= right_id.
    apply: (observe_both (is_Some (size_of σ ty))).
    intro. by rewrite _offsetR_sub_0.
  Qed.

  Lemma arrR_cons ty R Rs :
    arrR ty (R :: Rs) -|- type_ptrR ty ** R ** .[ ty ! 1 ] |-> arrR ty Rs.
  Proof.
    rewrite arrR_eq/arrR_def /= !_offsetR_sep !_offsetR_only_provable.
    apply: (observe_both (is_Some (size_of σ ty))) => Hsz.
    rewrite !_offsetR_sub_0 // _offsetR_big_sepL -assoc.
    rewrite _offsetR_succ_sub Nat2Z.inj_succ;
      setoid_rewrite _offsetR_succ_sub; setoid_rewrite Nat2Z.inj_succ.
    iSplit; [ iIntros "(? & ? & ? & ? & ?)" | iIntros "(? & ? & ? & _ & ?)"];
      by iFrame.
  Qed.

  Lemma arrR_valid_obs ty Rs (i : Z) (Hi : (0 ≤ i ≤ Z.of_nat (length Rs))%Z) :
    Observe (.[ ty ! i ] |-> validR) (arrR ty Rs).
  Proof.
    apply: observe_intro.
    apply: (observe_lhs (is_Some (size_of σ ty))) => Hsz.
    generalize dependent i.
    induction Rs => i Hi /=; [ rewrite arrR_nil | rewrite arrR_cons ].
    { simpl in *; have ->:i = 0; first lia.
      rewrite _offsetR_sub_0 //. iIntros "[#$ $]". }
    { case (decide (0 < i)%Z) => Hlt.
      { rewrite {1}(IHRs (i -1)%Z); last by simpl in *; split; lia.
        rewrite _offsetR_sep _offsetR_sub_sub. iIntros "($ & $ & $ & x)".
        iStopProof. f_equiv. f_equiv. lia. }
      { have ->: i = 0; first by lia.
        rewrite -svalidR_validR -type_ptrR_svalidR _offsetR_sub_0 //.
        iIntros "(#$ & $ & $)". } }
  Qed.

  #[global] Instance arrR_validR_observe {ty ys} : Observe validR (arrR ty ys).
  Proof.
    destruct ys.
    { rewrite arrR_nil. refine _. }
    { rewrite arrR_cons. rewrite type_ptrR_svalidR svalidR_validR; refine _. }
  Qed.

  Lemma arrR_append ty ys xs :
    arrR ty (xs ++ ys) -|- arrR ty xs ** .[ ty ! length xs ] |-> arrR ty ys.
  Proof.
    induction xs => /=.
    { apply: (observe_both (is_Some _)) => Hsz.
      rewrite arrR_nil /= _offsetR_sub_0 //.
      iSplit; last iIntros "[_ $]". iIntros "X"; repeat iSplit => //.
      iApply (observe with "X"). }
    { by rewrite !arrR_cons IHxs !_offsetR_sep !_offsetR_succ_sub Nat2Z.inj_succ -!assoc. }
  Qed.

  Lemma arrR_singleton ty R : arrR ty [R] -|- type_ptrR ty ** R.
  Proof.
    rewrite arrR_cons arrR_nil _offsetR_sep _offsetR_only_provable.
    iSplit.
    { iIntros "($ & $ & _ & %)". }
    { iIntros "(#tp & $)". rewrite -type_ptrR_validR_plus_one.
      iFrame "tp". iApply (observe with "tp"). }
  Qed.

  Lemma arrR_snoc ty xs (y : Rep) :
    arrR ty (xs ++ [y]) -|- arrR ty xs ** .[ ty ! length xs ] |-> (type_ptrR ty ** y).
  Proof. by rewrite arrR_append arrR_singleton. Qed.
End arrR.

Definition arrayR_def `{Σ : cpp_logic} {X : Type} {σ : genv} ty (P : X → Rep) (xs : list X) : Rep :=
  arrR ty (P <$> xs).
Definition arrayR_aux : seal (@arrayR_def). Proof. by eexists. Qed.
Definition arrayR := arrayR_aux.(unseal).
Definition arrayR_eq : @arrayR = _ := arrayR_aux.(seal_eq).
Arguments arrayR {_ _ _ _ _} _%_cpp_type _%_function_scope _%_list_scope : assert.
#[global] Instance: Params (@arrayR) 6 := {}.	(** TODO: [genv] weakening *)

Module arrayR_proper_ho.
Section arrayR_proper_ho.
  Context `{Σ : cpp_logic, resolve : genv}.
  Context {X : Type} (R : X -> Rep) (ty : Rtype).

  #[export] Instance arrayR_ne_ho {T : ofe} t n :
    Proper ((dist n ==> dist n) ==> dist n ==> dist n) (arrayR (X:=T) t).
  Proof.
    rewrite arrayR_eq/arrayR_def.
    move => ? ? H ? ? H'.
    f_equiv.
    induction H' => //=; f_equiv; eauto.
  Qed.

  #[export] Instance arrayR_proper_ho `{Equiv T} t :
    Proper (((≡) ==> (≡)) ==> (≡) ==> (≡)) (arrayR (X:=T) t).
  Proof.
    rewrite arrayR_eq/arrayR_def.
    move => ? ? Hf ? ? Hl.
    f_equiv.
    induction Hl => //=; f_equiv; eauto.
  Qed.

  #[export] Instance arrayR_mono_ho `{Equiv T} t :
    Proper (((≡) ==> (⊢)) ==> (≡) ==> (⊢)) (arrayR (X:=T) t).
  Proof.
    rewrite arrayR_eq/arrayR_def.
    move => ? ? Hf ? ? Hl.
    f_equiv.
    induction Hl => //=; f_equiv; eauto.
  Qed.

  #[export] Instance arrayR_flip_mono_ho `{Equiv T} t :
    Proper ((flip (≡) ==> flip (⊢)) ==> flip (≡) ==> flip (⊢)) (arrayR (X:=T) t).
  Proof.
    move => ? ? Hf ? ? Hl.
    apply arrayR_mono_ho => // ???.
    by apply Hf.
  Qed.
End arrayR_proper_ho.
End arrayR_proper_ho.

Section with_array_R.
  Context `{Σ : cpp_logic, resolve : genv}.
  Context {X : Type} (R : X -> Rep) (ty : Rtype).

  #[global] Instance arrayR_ne {T : ofe} n :
    Proper (pointwise_relation _ (dist n) ==> (=) ==> dist n) (arrayR (X:=T) ty).
  Proof.
    rewrite arrayR_eq/arrayR_def => f g Hf xs _ <-; f_equiv.
    exact: list_fmap_ext_ne.
  Qed.

  #[global] Instance arrayR_proper :
    Proper ((pointwise_relation X (≡)) ==> (=) ==> (≡)) (arrayR ty).
  Proof.
    rewrite arrayR_eq/arrayR_def => f g Hf xs _ <-; f_equiv.
    exact: list_fmap_equiv_ext.
  Qed.

  #[global] Instance arrayR_mono :
    Proper (pointwise_relation X (⊢) ==> (=) ==> (⊢)) (arrayR ty).
  Proof.
    rewrite arrayR_eq/arrayR_def => f g Hf xs _ <-; f_equiv.
    decompose_Forall.
  Qed.

  #[global] Instance arrayR_flip_mono :
    Proper (pointwise_relation X (flip (⊢)) ==> (=) ==> flip (⊢)) (arrayR ty).
  Proof. solve_proper. Qed.

  Lemma arrayR_nil : arrayR ty R [] -|- validR ** [| is_Some (size_of resolve ty) |].
  Proof. by rewrite arrayR_eq /arrayR_def arrR_nil. Qed.

  (** Compared to [array'_valid], this is a bientailment *)
  Lemma arrayR_cons x xs :
    arrayR ty R (x :: xs) -|- type_ptrR ty ** R x ** .[ ty ! 1 ] |-> arrayR ty R xs.
  Proof. rewrite arrayR_eq. exact: arrR_cons. Qed.

  Lemma arrayR_cons_obs x xs `{Hobs : ∀ x, Observe (type_ptrR ty) (R x)} :
    arrayR ty R (x :: xs) -|- R x ** .[ ty ! 1 ] |-> arrayR ty R xs.
  Proof. rewrite arrayR_cons. rewrite assoc. f_equiv. rewrite comm. exact: observe_equiv. Qed.

  #[global] Instance arrayR_timeless {T} t (P : T → Rep) l `{!∀ x, Timeless (P x)} :
    Timeless (arrayR t P l).
  Proof.
    rewrite arrayR_eq/arrayR_def. apply arrR_timeless_when_mpred_affine.
    by induction l; constructor.
  Qed.
  #[global] Instance arrayR_affine {T} t (P : T → Rep) l `{!∀ x, Affine (P x)} :
    Affine (arrayR t P l).
  Proof.
    rewrite arrayR_eq/arrayR_def. apply arrR_affine.
    by induction l; constructor.
  Qed.
  #[global] Instance arrayR_persistent {T} t (P : T → Rep) l `{!∀ x, Persistent (P x)} :
    Persistent (arrayR t P l).
  Proof.
    rewrite arrayR_eq/arrayR_def. apply arrR_persistent.
    by induction l; constructor.
  Qed.

  Lemma arrayR_singleton x : arrayR ty R [x] -|- type_ptrR ty ** R x.
  Proof. rewrite arrayR_eq. exact: arrR_singleton. Qed.

  Lemma arrayR_snoc xs y :
    arrayR ty R (xs ++ [y]) -|- arrayR ty R xs ** .[ ty ! length xs ] |-> (type_ptrR ty ** R y).
  Proof. by rewrite arrayR_eq /arrayR_def fmap_app arrR_snoc length_fmap. Qed.

  Lemma arrayR_snoc_obs p xs y
        `{Hobs : ∀ x, Observe (type_ptrR ty) (R x)} :
        p |-> arrayR ty R (xs ++ [y])
    -|- p |-> arrayR ty R xs ** p .[ty ! Z.of_nat (length xs)] |-> R y.
  Proof.
    rewrite arrayR_snoc !_at_sep !_at_offsetR _at_sep. f_equiv.
    rewrite (comm bi_sep).
    exact: observe_equiv.
  Qed.

  #[global] Instance arrayR_valid_type_obs l :
    Observe [| is_Some (size_of resolve ty) |] (arrayR ty R l).
  Proof. rewrite arrayR_eq/arrayR_def; apply arrR_size_of_observe. Qed.

  Lemma arrayR_sub_type_ptr_nat_obs (i : nat) xs
        (Hlen : i < length xs) :
    Observe (.[ ty ! i ] |-> type_ptrR ty) (arrayR ty R xs).
  Proof.
    apply: observe_intro_persistent.
    elim: xs i Hlen => [|x xs IHxs] [|i] /= Hlen; try lia;
                        rewrite arrayR_cons.
    { apply: (observe_lhs (is_Some (size_of resolve ty))) => Hsz.
      rewrite _offsetR_sub_0 //. iDestruct 1 as "[$ _]". }
    { rewrite (IHxs i); try lia.
      rewrite _offsetR_succ_sub Nat2Z.inj_succ.
      iDestruct 1 as "(_ & _ & $)". }
  Qed.

  Lemma arrayR_sub_type_ptr_obs (i : Z) xs :
    (0 ≤ i < Z.of_nat $ length xs)%Z →
    Observe (.[ ty ! i ] |-> type_ptrR ty) (arrayR ty R xs).
  Proof.
    intros []. have := arrayR_sub_type_ptr_nat_obs (Z.to_nat i) xs.
    rewrite Z2Nat.id //. apply. lia.
  Qed.

  Lemma _at_arrayR_sub_type_ptrR_nat_obs (i : nat) p xs
        (Hlen : i < length xs) :
    Observe (p .[ ty ! i ] |-> type_ptrR ty) (p |-> arrayR ty R xs).
  Proof.
    rewrite -_at_offsetR. by apply _at_observe, arrayR_sub_type_ptr_nat_obs.
  Qed.

  Lemma _at_arrayR_sub_type_ptrR_obs (i : Z) p xs
        (Hlen : (0 ≤ i < Z.of_nat $ length xs)%Z) :
    Observe (p .[ ty ! i ] |-> type_ptrR ty) (p |-> arrayR ty R xs).
  Proof.
    rewrite -_at_offsetR. by apply _at_observe, arrayR_sub_type_ptr_obs.
  Qed.

  Lemma arrayR_sub_svalidR_obs (i : Z) xs :
    (0 ≤ i < Z.of_nat $ length xs)%Z →
    Observe (.[ ty ! i ] |-> svalidR) (arrayR ty R xs).
  Proof. intros. rewrite -type_ptrR_svalidR. exact: arrayR_sub_type_ptr_obs. Qed.

  Lemma arrayR_validR_obs (i : Z) xs :
    (0 ≤ i ≤ Z.of_nat $ length xs)%Z →
    Observe (.[ ty ! i ] |-> validR) (arrayR ty R xs).
  Proof. intros. rewrite arrayR_eq/arrayR_def. apply arrR_valid_obs. rewrite length_fmap. lia. Qed.

  Lemma arrayR_valid_obs i xs
        (Hi : i ≤ length xs) :
    Observe (.[ ty ! i ] |-> validR) (arrayR ty R xs).
  Proof.
    rewrite arrayR_eq/arrayR_def.
    apply arrR_valid_obs. rewrite length_fmap; lia.
  Qed.

  Lemma _at_arrayR_valid_obs i xs p
        (Hi : i ≤ length xs) :
    Observe (p .[ ty ! i ] |-> validR) (p |-> arrayR ty R xs).
  Proof.
    rewrite -_at_offsetR.
    by apply _at_observe, arrayR_valid_obs.
  Qed.

  #[global] Instance arrayR_valid_base_obs {xs} : Observe validR (arrayR ty R xs).
  Proof. rewrite arrayR_eq/arrayR_def. apply _. Qed.

  (** Closer to [array'_valid] *)
  Lemma _at_arrayR_valid i xs p
        (Hi : i ≤ length xs) :
    p |-> arrayR ty R xs -|-
      p |-> arrayR ty R xs ** p .[ ty ! i ] |-> validR.
  Proof.
    split'; last exact: bi.sep_elim_l.
      by apply observe_elim, _at_arrayR_valid_obs.
  Qed.

  (* TODO: backfill versions of the following using Observe and on Reps. *)

  (** Compared to [array'_split] this is a bientailment and does not need an index *)
  Lemma arrayR_app xs ys :
    arrayR ty R (xs ++ ys) -|- arrayR ty R xs ** .[ ty ! length xs ] |-> arrayR ty R ys.
  Proof.
      by rewrite arrayR_eq/arrayR_def fmap_app arrR_append length_fmap.
  Qed.

  (** Compared to [array'_split], this takes [i] as first *)
  Lemma arrayR_split i xs :
    i <= length xs ->
        arrayR ty R xs
    |-- arrayR ty R (take i xs) ** .[ ty ! i ] |-> arrayR ty R (drop i xs).
  Proof.
    intros. rewrite -{1}(take_drop i xs) arrayR_app.
    f_equiv.
    rewrite length_take_le; eauto.
  Qed.

  (** Compared to [array'_combine], this takes [i] is first *)
  Lemma arrayR_combine i xs :
    arrayR ty R (take i xs) **
        .[ ty ! i ] |-> arrayR ty R (drop i xs)
    |-- arrayR ty R xs.
  Proof.
    rewrite -{3}(take_drop i xs).
    destruct (decide (i <= length xs)).
    - rewrite -{3}(length_take_le xs i) // arrayR_app.
      f_equiv. rewrite length_take_le //.
    - rewrite take_ge ?drop_ge /=; [ |lia|lia].
      by rewrite bi.sep_elim_l app_nil_r.
  Qed.

  (** Compare [arrayR_cell], [array_idx_with_addr] *)
  Lemma arrayR_cell xs i x iZ :
    iZ = Z.of_nat i →	(** Ease [eapply] *)
    xs !! i = Some x →	(** We have an [i]th element *)
    arrayR ty R xs -|-
           arrayR ty R (take i xs) **
           _sub ty iZ |-> type_ptrR ty **
           _sub ty iZ |-> R x **
           _sub ty (iZ + 1) |-> arrayR ty R (drop (S i) xs).
  Proof.
    intros Hi Hl.
    rewrite -{1}(take_drop_middle xs i _ Hl) arrayR_app arrayR_cons !_offsetR_sep.
    f_equiv.
    enough (length (take i xs) = i) as ->.
    { subst. by rewrite _offsetR_sub_sub. }
    { apply length_take_le.
      apply lookup_lt_Some in Hl. lia. }
  Qed.
End with_array_R.

Section with_array_Rs.
  Context `{Σ : cpp_logic, resolve : genv} {X : Type} {ty : Rtype}.

  Lemma arrayR_sep {V} (A B : V -> Rep) xs :
    arrayR ty (fun v : V => A v ** B v) xs -|-
    arrayR ty (fun v : V => A v) xs **
    arrayR ty (fun v : V => B v) xs.
  Proof.
    elim: xs => [|x xs IH] /=;
      rewrite !(arrayR_nil, arrayR_cons).
    2: rewrite {}IH _offsetR_sep.
    all: iSplit; iCancel.
  Qed.

  Lemma arrayR_pureR (R : X -> mpred) (l : list X) :
    arrayR ty (λ v, pureR (R v)) l ⊣⊢
    pureR ([∗ list] x ∈ l, R x) ∗ arrayR ty (funI _ => emp) l.
  Proof.
    elim: l => [|x xs IH] /=;
      rewrite !(arrayR_nil, arrayR_cons).
    { by rewrite pureR_emp left_id. }
    rewrite {}IH !_offsetR_sep.
    rewrite !_offsetR_pureR !pureR_sep.
    iSplit; iCancel.
  Qed.
End with_array_Rs.

Section arrayR_agree.
  Context `{Σ : cpp_logic, resolve : genv} {X T : Type} (ty : Rtype).
  Context (R : T -> X -> Rep).

  (** This is not phrased as an instance because TC resolution cannot
      always solve the unification problem for [R]. *)
  Lemma arrayR_agree q1 q2 l k :
    (∀ q1 q2 x1 x2, Observe2 [| x1 = x2 |] (R q1 x1) (R q2 x2)) ->
    length l = length k ->
    Observe2 [| l = k |] (arrayR ty (R q1) l) (arrayR ty (R q2) k).
  Proof.
    intros ? Hlen.
    rewrite -(_offsetR_id (arrayR _ _ l)) -(_offsetR_id (arrayR _ _ k));
      move: o_id => o.
    iIntros "L K". iInduction k as [|y k IH] "IH" forall (o l Hlen).
    { apply nil_length_inv in Hlen. simplify_eq. by auto. }
    destruct l as [|x l]; first done.
    rewrite !arrayR_cons !_offsetR_sep.
    iDestruct "L" as "(_ & X & L)". iDestruct "K" as "(_ & Y & K)".
    iDestruct (observe_2 [| x = y |] with "X Y") as %->.
    rewrite !_offsetR_dot. iDestruct ("IH" with "[] L K") as %->; auto.
  Qed.

  (** This is *not* an instance because TC resolution cannot
      always solve the unification problem for [R]. *)
  Lemma arrayR_agree_prefix q1 q2 l k :
    (∀ q1 q2 x1 x2, Observe2 [| x1 = x2 |] (R q1 x1) (R q2 x2)) ->
    length l <= length k ->
    Observe2 [| l = take (length l) k |] (arrayR ty (R q1) l) (arrayR ty (R q2) k).
  Proof.
    intros ? Hlen.
    rewrite -(_offsetR_id (arrayR _ _ l)) -(_offsetR_id (arrayR _ _ k));
      move: o_id => o.
    iIntros "L K". iInduction k as [|y k IH] "IH" forall (o l Hlen).
    { move: Hlen=>/Nat.le_0_r/nil_length_inv->.
      by iIntros "!>//=". }
    destruct l as [|x l]; first by iIntros "!>".
    rewrite !arrayR_cons !_offsetR_sep.
    iDestruct "L" as "(_ & X & L)". iDestruct "K" as "(_ & Y & K)".
    iDestruct (observe_2 [| x = y |] with "X Y") as %->.
    rewrite !_offsetR_dot. iDestruct ("IH" with "[] L K") as %Hlen';
        first by move: Hlen=>//= /le_S_n ?.
    by rewrite length_cons /= -Hlen'; iIntros "!>".
  Qed.

End arrayR_agree.

Section with_array_frac.
  Context `{Σ : cpp_logic, resolve : genv} {X : Type} (ty : Rtype).

  #[global] Instance arrayR_fractional (R : Qp -> X -> Rep) l
  `{HF : !∀ x, Fractional (λ q, R q x)} :
    Fractional (λ q, arrayR ty (R q) l).
  Proof.
    red. intros.
    induction l.
    { rewrite !arrayR_nil. iSplit; iCancel. }
    { rewrite !arrayR_cons IHl HF !_offsetR_sep. iSplit; iCancel. }
  Qed.

  #[global] Instance arrayR_as_fractional (R : X -> Rep) (R' : X -> Qp -> Rep)
    l q `{!forall x, AsFractional (R x) (R' x) q} :
    AsFractional (arrayR ty R l) (λ q, arrayR ty (fun x => R' x q) l) q.
  Proof.
    constructor.
    - f_equiv => ?; apply as_fractional.
    - apply arrayR_fractional => ?.
      autoapply @as_fractional_fractional with typeclass_instances.
      apply H.
  Qed.

End with_array_frac.

Section with_array_cfrac.
  Context `{Σ : cpp_logic, resolve : genv} {X : Type} (ty : Rtype).

  #[global] Instance arrayR_cfractional (R : cQp.t -> X -> Rep)
    l `{HF : CFractional1 R} :
    CFractional (λ q, arrayR ty (R q) l).
  Proof.
    red. intros.
    induction l.
    { rewrite !arrayR_nil. iSplit; iCancel. }
    { rewrite !arrayR_cons IHl HF !_offsetR_sep. iSplit; iCancel. }
  Qed.

  #[global] Instance arrayR_as_cfractional (R : X -> Rep) (R' : X -> cQp.t -> Rep)
    l q `{!forall x, AsCFractional (R x) (R' x) q} :
    AsCFractional (arrayR ty R l) (λ q, arrayR ty (fun x => R' x q) l) q.
  Proof.
    constructor.
    - f_equiv => ?; apply as_cfractional.
    - apply arrayR_cfractional => ?.
      autoapply @as_cfractional_cfractional with typeclass_instances.
      apply H.
  Qed.

End with_array_cfrac.

#[global] Hint Opaque arrR arrayR : typeclass_instances.
