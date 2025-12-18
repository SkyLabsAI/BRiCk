(*
 * Copyright (c) 2021 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.iris.extra.proofmode.proofmode.

Require Import skylabs.lang.cpp.semantics.
Require Import skylabs.lang.cpp.logic.pred.
Require Import skylabs.lang.cpp.logic.wp.

Section defs.
  Context `{Σ : cpp_logic}.

  (**
  Function specifications written in weakest pre-condition style.

  In other words, [fs_spec] asserts that arguments satisfy the function's
  precondition _and_ that the continuation coincides with the function's
  postcondition.
   *)
  Record function_spec : Type :=
    { fs_cc : calling_conv
    ; fs_arity : function_arity
    ; fs_return : type
    ; fs_arguments : list type
    ; fs_spec : list ptr -d> (ptr -> mpred) -d> mpredO
    }.

  #[global] Instance function_spec_inhabited : Inhabited function_spec :=
    populate (Build_function_spec inhabitant inhabitant inhabitant inhabitant inhabitant).

  Definition type_of_spec (fs : function_spec) : type :=
    normalize_type (Tfunction {| ft_cc:=fs.(fs_cc) ; ft_arity:=fs.(fs_arity) ; ft_return := fs.(fs_return) ; ft_params := fs.(fs_arguments) |}).

  Lemma cc_type_of_spec fs1 fs2 :
    type_of_spec fs1 = type_of_spec fs2 →
    fs1.(fs_cc) = fs2.(fs_cc).
  Proof.
    destruct fs1, fs2. intros [=]. by simplify_eq/=.
  Qed.

  Lemma length_type_of_spec fs1 fs2 :
    type_of_spec fs1 = type_of_spec fs2 →
    length (fs_arguments fs1) = length (fs_arguments fs2).
  Proof.
    destruct fs1, fs2; rewrite /type_of_spec/=; intros [= _ _ _ Hmap].
    erewrite <-length_map, Hmap.
    by rewrite length_map.
  Qed.

  Section ofe.
    Implicit Types P Q : function_spec.

    Instance function_spec_equiv : Equiv function_spec := fun P Q =>
      type_of_spec P = type_of_spec Q /\
      P.(fs_spec) ≡ Q.(fs_spec).
    Instance function_spec_dist : Dist function_spec := fun (n : nat) P Q =>
      type_of_spec P = type_of_spec Q /\
      P.(fs_spec) ≡{n}≡ Q.(fs_spec).

    Lemma function_spec_ofe_mixin : OfeMixin function_spec.
    Proof.
      split.
      - intros P Q. split.
        + intros [] n. split. done. by apply equiv_dist.
        + intros HPQ. split; first by destruct (HPQ 0).
          apply equiv_dist=>n. by destruct (HPQ n).
      - intros n. split.
        + done.
        + by intros P Q [].
        + intros P Q R [Ht1 HPQ] [Ht2 HQR]. split.
          * by rewrite Ht1 Ht2.
          * etrans. by apply HPQ. done.
      - intros n m P Q [] ?. split; first done. by eapply dist_le.
    Qed.
    Canonical Structure function_specO := Ofe function_spec function_spec_ofe_mixin.

    #[global] Instance type_of_spec_ne (n : nat) :
      Proper (dist n ==> eq) type_of_spec.
    Proof. by intros P Q [? _]. Qed.

    #[global] Instance fs_spec_ne : NonExpansive fs_spec.
    Proof. by intros n P Q [_ ?]. Qed.

    #[global] Instance fs_cc_ne (n : nat) : Proper (dist n ==> eq) fs_cc.
    Proof. move=>P Q /type_of_spec_ne. exact: cc_type_of_spec. Qed.

    #[global] Instance length_fs_arguments_ne (n : nat) :
      Proper (dist n ==> eq) (fun P => length (fs_arguments P)).
    Proof. move=>P Q /type_of_spec_ne. exact: length_type_of_spec. Qed.
  End ofe.

  #[global,program] Instance function_spec_cofe : Cofe function_specO :=
    cofe_finite (fun c => {|
      fs_cc := (c 0).(fs_cc);
      fs_arity := (c 0).(fs_arity);
      fs_return := (c 0).(fs_return);
      fs_arguments := (c 0).(fs_arguments);
      fs_spec := compl (chain_map fs_spec c);
  |}) _.
  Next Obligation.
    intros n c. split; simpl.
    - destruct (chain_cauchy c 0 n) as [-> _]. cbn; lia. done.
    - intros. apply conv_compl.
  Qed.

  Lemma fs_equivI_type P Q :
    P ≡ Q ⊢@{mpredI} [| type_of_spec P = type_of_spec Q |].
  Proof.
    rewrite only_provable_equiv.
    constructor => ?.
    rewrite monPred_at_internal_eq monPred_at_and monPred_at_emp monPred_at_pure.
    repeat uPred.unseal. constructor => n x ?. by intros [? _].
  Qed.

  Lemma fs_equivI_spec P Q vs K :
    P ≡ Q ⊢@{mpredI} P.(fs_spec) vs K ≡ Q.(fs_spec) vs K.
  Proof.
    constructor => ?. rewrite !monPred_at_internal_eq.
    repeat uPred.unseal. constructor=>n x ? [_ HPQ]. apply HPQ.
  Qed.

  Lemma fs_equivI_intro P Q :
    type_of_spec P = type_of_spec Q ->
    Forall vs K, P.(fs_spec) vs K ≡ Q.(fs_spec) vs K ⊢@{mpredI} P ≡ Q.
  Proof.
    intros.
    constructor => ?.
    repeat setoid_rewrite monPred_at_forall.
    repeat setoid_rewrite monPred_at_internal_eq.
    repeat uPred.unseal. constructor=>x ?; by split.
  Qed.

  Lemma fs_equivI P Q :
    P ≡ Q ⊣⊢@{mpredI}
    [| type_of_spec P = type_of_spec Q |] **
    Forall vs K, P.(fs_spec) vs K ≡ Q.(fs_spec) vs K.
  Proof.
    split'.
    - iIntros "?". iSplit; first by rewrite fs_equivI_type.
      iIntros (vs K). by rewrite fs_equivI_spec.
    - iIntros "[% ?]". by rewrite fs_equivI_intro.
  Qed.

  (** [mpred] implication on [function_spec].
  Here, [Q] is a lower-level spec, and [P] is a derived/higher-level spec.

    [fs_impl] and [fs_entails] are mostly used to derive
    properties like properness and non-expansiveness for [cptrR].

    Note that [function_spec] and co ([fs_impl] and [fs_entails])
    do not package the usually expected properties for
    weakest-precondition.
    [cptrR] gets those properties from axioms for [wp_fptr].
   *)
  Definition fs_impl (Q P : function_spec) : mpred :=
    [| type_of_spec P = type_of_spec Q |] ∗
    □ ∀ vs K, P.(fs_spec) vs K -∗ Q.(fs_spec) vs K.
  Lemma fs_impl_reflexive P : |-- fs_impl P P.
  Proof. iSplit; auto. Qed.
  Lemma fs_impl_transitive P Q R : fs_impl P Q |-- fs_impl Q R -* fs_impl P R.
  Proof.
    rewrite /fs_impl; iIntros "(-> & #H1) (-> & #H2)".
    iSplit; first done.
    iIntros "!>" (vs K) "Y".
    iApply ("H1" with "(H2 Y)").
  Qed.

  Definition fs_entails (P Q : function_spec) : Prop := |-- fs_impl P Q.

  #[global] Instance fs_entails_preorder : PreOrder fs_entails.
  Proof.
    split; rewrite /fs_entails.
    - intro x. exact: fs_impl_reflexive.
    - intros ? ? ? H1 H2. by iApply (fs_impl_transitive).
  Qed.
  #[global] Instance : RewriteRelation fs_entails := {}.

  (* [mpred] bi-implication on [function_spec] *)
  Definition fs_equiv (P Q : function_spec) : mpred :=
    [| type_of_spec P = type_of_spec Q |] ∗
    □ ∀ vs K, P.(fs_spec) vs K ∗-∗ Q.(fs_spec) vs K.

  Lemma fs_equivI_equiv P Q : P ≡ Q |-- fs_equiv P Q.
  Proof.
    rewrite fs_equivI /fs_equiv. f_equiv.
    rewrite -(bi.intuitionistic_intuitionistically (Forall _, _)).
    repeat f_equiv. rewrite prop_ext plainly_elim_persistently.
    by iIntros "#$".
  Qed.

  Lemma fs_equiv_equivI P Q : ■ fs_equiv P Q |-- P ≡ Q.
  Proof.
    iIntros "[% #EQ]". iApply fs_equivI_intro; first done.
    iIntros (vs K). iApply prop_ext. iModIntro. iApply "EQ".
  Qed.

  Lemma fs_equiv_split P Q : fs_equiv P Q -|- fs_impl P Q ** fs_impl Q P.
  Proof.
    rewrite /fs_equiv /fs_impl; iSplit.
    - iIntros "(-> & #W)"; repeat iSplit => //;
      iIntros "!>" (??) "A"; iApply ("W" with "A").
    - iIntros "((-> & #W1) & (_ & #W2))".
      iSplit => //; iIntros "!>" (??); iSplit;
        [by iApply "W2" | by iApply "W1"].
  Qed.

  Lemma function_spec_equiv_iff P Q : P ≡ Q <-> |-- fs_equiv P Q.
  Proof.
    enough (HEQ : P ≡ Q <-> ⊢@{mpredI} P ≡ Q).
    { rewrite {}HEQ. split.
      - by rewrite fs_equivI_equiv.
      - rewrite /bi_emp_valid {2}plainly_emp_2=>->. by rewrite fs_equiv_equivI. }
    split.
    - intros->. apply internal_eq_refl.
    - rewrite monPred_internal_eq_unfold => /embed_emp_valid_inj.
      apply uPred.internal_eq_soundness.
  Qed.

  Lemma function_spec_equiv_split P Q : P ≡ Q ↔ fs_entails P Q /\ fs_entails Q P.
  Proof.
    rewrite /fs_entails function_spec_equiv_iff fs_equiv_split; split.
    { by intros H; split; iDestruct H as "[??]". }
    { intros [H1 H2]. iDestruct H1 as "$". iDestruct H2 as "$". }
  Qed.


  (* this is the core definition that the program logic will be based on.
     it is really an assertion about assembly.
   *)
  Definition cptrR_def {resolve : genv} (fs : function_spec) : Rep :=
    as_Rep (fun p =>
         strict_valid_ptr p **
         □ (Forall vs Q,
         fs.(fs_spec) vs Q -*
         wp_fptr resolve.(genv_tu).(types) (type_of_spec fs) p vs Q)).
  Definition cptrR_aux : seal (@cptrR_def). Proof. by eexists. Qed.
  Definition cptrR := cptrR_aux.(unseal).
  Definition cptrR_eq : @cptrR = _ := cptrR_aux.(seal_eq).

  #[global] Hint Opaque cptrR : typeclass_instances.

  (** A version of [fs_impl] and [fs_entails] with [fupd].
    These are used in stating strong wp properties for [cptrR],
    like [cptrR_fs_impl_fupd] and [cptrR_fs_entails_fupd] (see below).
   *)
  Definition fs_impl_fupd (Q P : function_spec) : mpred :=
    [| type_of_spec P = type_of_spec Q |] ∗
    □ ∀ vs K, P.(fs_spec) vs K -∗ |={top}=> Q.(fs_spec) vs (λ v, |={top}=> K v).
  Definition fs_entails_fupd (P Q : function_spec) : Prop := |-- fs_impl_fupd P Q.
End defs.

#[global] Instance: Params (@cptrR) 4 := {}.

#[global] Arguments cptrR {_ _ Σ resolve} _ : rename.

Section with_cpp.
  Context `{Σ : cpp_logic} {resolve : genv}.

  #[global] Instance cptrR_persistent {s} : Persistent (cptrR s).
  Proof. rewrite cptrR_eq. apply _. Qed.
  #[global] Instance cptrR_affine {s} : Affine (cptrR s).
  Proof. rewrite cptrR_eq. apply _. Qed.

  Lemma cptrR_strict_valid_observe (p : ptr) f : Observe (strict_valid_ptr p) (_at p (cptrR f)).
  Proof.
    apply observe_intro_persistent; refine _.
    rewrite cptrR_eq/cptrR_def.
    rewrite _at_as_Rep.
    iIntros "[$ _]".
  Qed.

  (* NOTE this should become an instance. *)
  Lemma cptrR_valid_observe (p : ptr) f : Observe (valid_ptr p) (_at p (cptrR f)).
  Proof. apply observe_strict_valid_valid; apply cptrR_strict_valid_observe. Qed.

  #[local] Opaque type_of_spec.
  Lemma cptrR_fs_impl f g :
    pureR (fs_impl f g) |-- cptrR f -* cptrR g.
  Proof.
    rewrite cptrR_eq/cptrR_def /pureR /as_Rep.
    constructor => p; rewrite Rep_wand_force; iIntros "#(%ty & fs_impl)" => /=.
    iIntros "(val & #rest)"; iFrame.
    rewrite ty. iModIntro. iIntros (vs Q) "fs_g".
    iApply "rest".
    by iApply "fs_impl".
  Qed.

  Lemma cptrR_fs_impl_fupd f g :
    pureR (fs_impl_fupd f g) |-- cptrR f -* cptrR g.
  Proof.
    rewrite cptrR_eq/cptrR_def /pureR /as_Rep.
    constructor => p; rewrite Rep_wand_force; iIntros "#(%ty & fs_impl)" => /=.
    iIntros "(val & #rest)"; iFrame.
    rewrite ty. iModIntro. iIntros (vs Q) "fs_g".
    iApply wp_fptr_fupd. iApply fupd_spec.
    iApply "rest".
    by iApply "fs_impl".
  Qed.
  #[local] Transparent type_of_spec.

  #[global] Instance cptrR_ne : NonExpansive cptrR.
  Proof.
    intros n P Q HPQ. rewrite cptrR_eq/cptrR_def.
    apply as_Rep_ne=>p. (do 2!f_equiv). do 5 f_equiv. by apply fs_spec_ne.
    f_equiv. apply HPQ.
  Qed.
  #[global] Instance cptrR_proper : Proper (equiv ==> equiv) cptrR.
  Proof. exact: ne_proper. Qed.

  #[global] Instance cptrR_mono : Proper (fs_entails ==> (⊢)) cptrR.
  Proof.
    intros ??; rewrite /fs_entails/flip => impl. iApply cptrR_fs_impl.
    by rewrite -impl pureR_emp.
  Qed.

  Lemma _at_cptrR_mono (p : ptr) (spec spec' : function_spec) :
    fs_entails spec spec' ->
    p |-> cptrR spec |-- p |-> cptrR spec'.
  Proof. intros; rewrite cptrR_mono; eauto. Qed.

  #[global] Instance cptrR_flip_mono : Proper (flip fs_entails ==> flip (⊢)) cptrR.
  Proof. by intros ?? <-. Qed.

  Lemma cptrR_mono_fupd : Proper (fs_entails_fupd ==> (⊢)) cptrR.
  Proof.
    intros ??; rewrite /fs_entails_fupd/flip => impl. iApply cptrR_fs_impl_fupd.
    by rewrite -impl pureR_emp.
  Qed.

  Lemma cptrR_flip_mono_fupd : Proper (flip fs_entails_fupd ==> flip (⊢)) cptrR.
  Proof. repeat intro. by rewrite -cptrR_mono_fupd. Qed.
End with_cpp.

#[global] Instance Persistent_spec `{cpp_logic} {resolve:genv} p s :
  Persistent (_at p (cptrR s)) := _.
#[global] Instance Affine_spec `{cpp_logic} {resolve:genv} p s :
  Affine (_at p (cptrR s)) := _.
