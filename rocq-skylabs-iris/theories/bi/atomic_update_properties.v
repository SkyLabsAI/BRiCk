(*
 * Copyright (C) 2020 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import stdpp.coPset.
Require Import iris.bi.lib.fixpoint_mono.
Require Import iris.bi.lib.laterable.
Require Import bluerock.iris.extra.bi.derived_laws.
Require Export bluerock.iris.extra.bi.atomic_update.
Require Import bluerock.iris.extra.bi.telescopes.
Require Import bluerock.iris.extra.bi.fupd_iff.
Require Import bluerock.iris.extra.proofmode.proofmode.
Set Default Proof Using "Type".

Local Tactic Notation "iSplit" "?" := repeat iSplit.

(** * Atomic accessors and atomic updates *)

(** Our theories for atomic accessors and updates have a lot in
common (where [AU ∈ {aacc,aupd}, M ∈ {fupd,wand}]):

<<
  AU_proper	[Proper] for [≡] (in [atomic_udpate.v])
  AU_update	"strong monotonicity" lemmas for changing all components

  AU_mask_{weaken,strengthen}	change masks
  AU_{apre,apost,ppost}_M	change individual components
  aacc_ppre_M

  fupd_aacc, AU_fupd		compatibility with fancy updates

  AU_{apre,apost,ppost}_frame_{l,r}	frame affine, persistent resources
  aacc_ppre_frame_{l,r}

  AU_{apre,apost,ppost}_mono	monotonicity
  aacc_ppost_mono
  AU_{,flip_}mono'		[Proper] for [⊢], [⊣]
>>

We also provide a few proof mode instances for atomic accessors, and a
few higher-level lemmas for atomic updates. These are described below.
*)

(**
NOTE: any uses of [Laterable] and [make_laterable] are no longer necessary,
thanks to later credits. Some of the sections below are kept as documentation.
*)

(** This is an introduction. If you want the theory, skip down.

An _atomic accessor_

<<
  Definition atomic_acc Eo Ei α P β Φ : PROP :=
    (|={Eo, Ei}=> ∃.. x, α x ∗	(** OPEN *)
          ((α x ={Ei, Eo}=∗ P) ∧	(** ABORT *)
           (∀.. y, β x y ={Ei, Eo}=∗ Φ x y))	(** COMMIT *)
    )%I.
>>

is a fancy update (call it OPEN) enabling a callee to access a
caller's _atomic precondition_ [α x] (for some x) and then take one
of two fancy updates:

- ABORT lets the callee give [α x] back to the caller in exchange for
  the _public precondition_ [P]

- COMMIT lets the callee, if she can change [α x] to the _atomic
  postcondition_ [β x y] (for some y), return [β x y] to the callee in
  exchange for the _public postcondition_ [Φ x y].

An _atomic update_ is (roughly) an atomic accessor whose public
precondition is the atomic update itself:

<<
  atomic_update Eo Ei α β Φ ≈	(** [†] *)
    atomic_accessor Eo ei α (atomic_update Eo Ei α β Φ) β Φ
>>

In fact, atomic updates satisfy the following recursive equation,
which adds a [make_laterable] to [†]. *)

Local Existing Instance atomic_update_pre_mono.
Local Lemma aupd_unfold `{BiFUpd PROP} {TA TB : tele} Eo Ei
    (α : TA → PROP) (β Φ : TA → TB → PROP) :
  atomic_update Eo Ei α β Φ ⊣⊢
  atomic_acc Eo Ei α (atomic_update Eo Ei α β Φ) β Φ.
Proof.
  rewrite atomic.atomic_update_unseal /atomic.atomic_update_def /atomic_update_pre /=.
  exact: greatest_fixpoint_unfold.
Qed.

(** ** Laterable assertions *)

(** The point of baking [make_laterable] into the definition of atomic
updates is to ensure that atomic updates are themselves [Laterable].
Because [Laterable] propositions are relevant to the introduction of
atomic updates, we go into some detail.

If you run [Print Instances Laterable], you'll see that the class of
[Laterable] propositions includes timeless propositions, [▷ P],
[make_laterable P], and is closed under separating conjuction:

<<
  timeless_laterable       P : Timeless P → Laterable P
  later_laterable          P : Laterable (▷ P)
  sep_laterable          P Q : Laterable P → Laterable Q → Laterable (P ∗ Q)
  make_laterable_laterable P : Laterable (make_laterable P)

  (* so that *)
  aupd_laterable Eo Ei α β Φ : Laterable (atomic_update Eo Ei α β Φ)
>>

A [Laterable P] satisfies

<<
  laterable_fupd E : P ⊢ ∃ Q, ▷ Q ∗ □ (▷ Q ={E}=∗ P)
>>

We can thus decompose a laterable [P] into [▷ Q] for some [Q] as well as
knowledge of a fancy update sending [▷ Q] back to [P] (with any mask). *)

(** ** Except at zero *)

(** The preceding characterization [laterable_fupd] of [Laterable]
assertions is just a lemma (proved below). [Laterable P] is _defined_
in terms of the modality [◇ P], read "except at zero, [P]":

<<
  laterable : P ⊢ ∃ Q, ▷ Q ∗ □ (▷ Q -∗ ◇ P)
>>

The except at zero modality [◇ P] usually remains hidden during
verification efforts. In practice, you can read it as "[P] up to
updates". In the model of Iris' base logic, [◇ P] means precisely the
same thing as [P] _except_ at step-index zero (when all bets are off).

Perhaps a more familiar place where the except at zero modality arises
is in the definition of timelessness. A [Timeless P] satisfies

<<
  timeless : ▷ P -∗ ◇ P
>>

Because both concepts build on except at zero, we can easily relate
[Timeless] and [Laterable] propositions to fancy updates (something
the Iris proof mode usually takes care of). See the following lemmas
[timeless_fupd] and [laterable_fupd]. *)

Section except_0_fupd.
  Context `{BiFUpd PROP}.
  Implicit Types P : PROP.

  Local Lemma except_0_fupd_simple P E : ◇ P ⊢ |={E}=> P.
  Proof. rewrite -fupd_except_0. apply fupd_intro. Qed.

  Lemma timeless_fupd `{HP : !Timeless P} E : ▷ P ⊢ |={E}=> P.
  Proof. unfold Timeless in HP. rewrite HP. apply except_0_fupd_simple. Qed.

  Lemma laterable_fupd `{HP : !Laterable P} E : P ⊢ ∃ Q, ▷ Q ∗ □ (▷ Q ={E}=∗ P).
  Proof.
    unfold Laterable in HP. rewrite {1}HP. do 5!f_equiv.
    apply except_0_fupd_simple.
  Qed.
End except_0_fupd.

(** * Atomic accessors *)
Section atomic_acc.
  Context `{BiFUpd PROP} {TA TB : tele}.
  Implicit Types (α : TA → PROP).
  Implicit Types (β Φ : TA → TB → PROP).

  (** Workhorse for rewriting parts of an atomic accessor. *)
  Lemma aacc_update Eo1 Eo2 Ei1 Ei2 α1 α2 P1 P2 β1 β2 Φ1 Φ2 :
    Eo1 ⊆ Eo2 → Ei2 ⊆ Ei1 →
    atomic_acc Eo1 Ei1 α1 P1 β1 Φ1 ⊢
    ((□ ∀.. x, α1 x ∗={Ei1}=∗ α2 x) ∗
     (P1 ={Eo1}=∗ P2) ∧
     ((∀.. x y, β2 x y ={Ei2}=∗ β1 x y) ∗
      (∀.. x y, Φ1 x y ={Eo1}=∗ Φ2 x y))) -∗
    atomic_acc Eo2 Ei2 α2 P2 β2 Φ2.
  Proof.
    iIntros (??) "AU (#Apre & PP)". rewrite/atomic_acc.
    iMod (fupd_mask_subseteq Eo1) as "CloseO"; first done.
    iMod "AU" as (x) "[Hα Close]". iExists x.
    iMod ("Apre" with "Hα") as "$".
    iMod (fupd_mask_subseteq Ei2) as "CloseI"; first done.
    iModIntro. iSplit.
    - iIntros "Hα". iMod "CloseI" as "_". iMod ("Apre" with "Hα") as "Hα".
      iMod ("Close" with "Hα") as "P". iMod ("PP" with "P") as "$".
      iExact "CloseO".
    - iIntros (y) "Hβ". iDestruct "PP" as "[_ [Apost Ppost]]".
      iMod ("Apost" with "Hβ") as "Hβ". iMod "CloseI" as "_".
      iMod ("Close" with "Hβ") as "HΦ". iMod ("Ppost" with "HΦ") as "$".
      iExact "CloseO".
  Qed.

  (** Easy corollaries of [aacc_update] *)
  Section updates.
    Lemma aacc_mask_weaken Eo1 Eo2 Ei α P β Φ :
      Eo1 ⊆ Eo2 → atomic_acc Eo1 Ei α P β Φ ⊢ atomic_acc Eo2 Ei α P β Φ.
    Proof.
      iIntros (?) "AU". iApply (aacc_update with "AU"); auto.
      iSplit?; [iModIntro|..|iSplitL]; auto.
    Qed.

    Lemma aacc_mask_strengthen Ei1 Ei2 Eo α P β Φ :
      Ei1 ⊆ Ei2 → atomic_acc Eo Ei2 α P β Φ ⊢ atomic_acc Eo Ei1 α P β Φ.
    Proof.
      iIntros (?) "AU". iApply (aacc_update with "AU"); auto.
      iSplit?; [iModIntro|..|iSplitL]; auto.
    Qed.

    Lemma aacc_apre_fupd α1 α2 Eo Ei P β Φ :
      atomic_acc Eo Ei α1 P β Φ ⊢
      □ (∀.. x, α1 x ∗={Ei}=∗ α2 x) -∗ atomic_acc Eo Ei α2 P β Φ.
    Proof.
      iIntros "AU #?". iApply (aacc_update with "AU"); auto.
      iSplit?; [iModIntro|..|iSplitL]; auto.
    Qed.
    Lemma aacc_apre_wand α1 α2 Eo Ei P β Φ :
      atomic_acc Eo Ei α1 P β Φ ⊢
      □ (∀.. x, α1 x ∗-∗ α2 x) -∗ atomic_acc Eo Ei α2 P β Φ.
    Proof. rewrite aacc_apre_fupd. repeat f_equiv. apply fupd_iff_intro. Qed.

    (* Here and below, we need [<affine>] because the fancy update will only be used on AU aborts. *)
    Lemma aacc_ppre_fupd P1 P2 Eo Ei α β Φ :
      atomic_acc Eo Ei α P1 β Φ ⊢
      <affine> (P1 ={Eo}=∗ P2) -∗ atomic_acc Eo Ei α P2 β Φ.
    Proof.
      iIntros "AU ?". iApply (aacc_update with "AU"); auto.
      iSplit?; [iModIntro|..|iSplitR]; auto.
    Qed.
    Lemma aacc_ppre_wand P1 P2 Eo Ei α β Φ :
      atomic_acc Eo Ei α P1 β Φ ⊢ <affine> (P1 -∗ P2) -∗ atomic_acc Eo Ei α P2 β Φ.
    Proof. rewrite aacc_ppre_fupd. repeat f_equiv. apply fupd_intro. Qed.

    Lemma aacc_apost_fupd β1 β2 Eo Ei α P Φ :
      atomic_acc Eo Ei α P β1 Φ ⊢
      <affine> (∀.. x y, β2 x y ={Ei}=∗ β1 x y) -∗ atomic_acc Eo Ei α P β2 Φ.
    Proof.
      iIntros "AU ?". iApply (aacc_update with "AU"); auto.
      iSplit?; [iModIntro|..|iSplitL]; auto.
    Qed.
    Lemma aacc_apost_wand β1 β2 Eo Ei α P Φ :
      atomic_acc Eo Ei α P β1 Φ ⊢
      <affine> (∀.. x y, β2 x y -∗ β1 x y) -∗ atomic_acc Eo Ei α P β2 Φ.
    Proof. rewrite aacc_apost_fupd. repeat f_equiv. apply fupd_intro. Qed.

    Lemma aacc_ppost_fupd Φ1 Φ2 Eo Ei α P β :
      atomic_acc Eo Ei α P β Φ1 ⊢
      <affine> (∀.. x y, Φ1 x y ={Eo}=∗ Φ2 x y) -∗ atomic_acc Eo Ei α P β Φ2.
    Proof.
      iIntros "AU ?". iApply (aacc_update with "AU"); auto.
      iSplit?; [iModIntro|..|iSplitR]; auto.
    Qed.
    Lemma aacc_ppost_wand Φ1 Φ2 Eo Ei α P β :
      atomic_acc Eo Ei α P β Φ1 ⊢
      <affine> (∀.. x y, Φ1 x y -∗ Φ2 x y) -∗ atomic_acc Eo Ei α P β Φ2.
    Proof. rewrite aacc_ppost_fupd. repeat f_equiv. apply fupd_intro. Qed.
  End updates.

  (** Atomic accessors and the outer mask *)
  (** Attribution: The following are inspired by Iris' interface for
  weakestpre. *)
  Lemma fupd_aacc Eo Ei α P β Φ :
    (|={Eo}=> atomic_acc Eo Ei α P β Φ) ⊢ atomic_acc Eo Ei α P β Φ.
  Proof. iIntros "AU". by iMod "AU" as "$". Qed.
  Lemma aacc_fupd Eo Ei α P β Φ :
    atomic_acc Eo Ei α P β (λ.. x y, |={Eo}=> Φ x y) ⊢ atomic_acc Eo Ei α P β Φ.
  Proof.
    iIntros "AU". iApply (aacc_ppost_fupd with "AU").
    iIntros "!>" (x y) "HΦ". rewrite !tele_app_bind. iExact "HΦ".
  Qed.
  (* PDS: Analog of [wp_atomic]? *)

  (** We can frame knowledge into any component of an atomic accessor.

  We can't frame arbitrary resources, as in [fupd_frame_r], but some
  of the rules could be strengthened to framing any [Affine R]
  (dropping the [Persistent] assumption). Consider framing [R] into a
  public postcondition [Φ]. We get both [R] and a conjunction of
  updates [ABORT //\\ COMMIT] and we have to prove [ABORT //\\
  COMMIT'] (where [COMMIT'] mentions [R]). To handle the [ABORT] case,
  we need [Affine R], but we don't care if it's persistent. *)
  Section framing.
    Local Set Default Proof Using "Type*".
    Context (R : PROP) `{!Affine R, !Persistent R}.
    Context (Eo Ei : coPset) α (P : PROP) β Φ.

    Lemma aacc_apre_frame_l :
      R ∗ atomic_acc Eo Ei α P β Φ ⊢ atomic_acc Eo Ei (λ.. x, R ∗ α x) P β Φ.
    Proof.
      iIntros "[#R AU]". iApply (aacc_apre_wand with "AU"); auto.
      iIntros "!>" (x). rewrite tele_app_bind. iSplit. (* R ⊢ (P ∗-∗ R ∗ P) *)
      - iIntros "$". iFrame "R".
      - iIntros "[_ $]".
    Qed.
    Lemma aacc_apre_frame_r :
      atomic_acc Eo Ei α P β Φ ∗ R ⊢ atomic_acc Eo Ei (λ.. x, α x ∗ R) P β Φ.
    Proof.
      rewrite comm aacc_apre_frame_l.
      iIntros "AU". iApply (aacc_apre_wand with "AU"); auto.
      iIntros "!>" (x). rewrite !tele_app_bind comm. auto.
    Qed.

    Lemma aacc_ppre_frame_l :
      R ∗ atomic_acc Eo Ei α P β Φ ⊢ atomic_acc Eo Ei α (R ∗ P) β Φ.
    Proof. iIntros "[#R AU]". iApply (aacc_ppre_wand with "AU"); auto. Qed.
    Lemma aacc_ppre_frame_r :
      atomic_acc Eo Ei α P β Φ ∗ R ⊢ atomic_acc Eo Ei α (P ∗ R) β Φ.
    Proof. by rewrite comm aacc_ppre_frame_l [(R ∗ P)%I]comm. Qed.

    Lemma aacc_apost_frame_l :
      R ∗ atomic_acc Eo Ei α P β Φ ⊢
      atomic_acc Eo Ei α P (λ.. x y, R ∗ β x y) Φ.
    Proof.
      iIntros "[#R AU]". iApply (aacc_apost_wand with "AU"); auto.
      iIntros "!>" (x y). rewrite !tele_app_bind. iIntros "[_ $]".
    Qed.
    Lemma aacc_apost_frame_r :
      atomic_acc Eo Ei α P β Φ ∗ R ⊢
      atomic_acc Eo Ei α P (λ.. x y, β x y ∗ R) Φ.
    Proof.
      rewrite comm aacc_apost_frame_l.
      iIntros "AU". iApply (aacc_apost_wand with "AU"); auto.
      iIntros "!>" (x y). rewrite !tele_app_bind comm. auto.
    Qed.

    Lemma aacc_ppost_frame_l :
      R ∗ atomic_acc Eo Ei α P β Φ ⊢
      atomic_acc Eo Ei α P β (λ.. x y, R ∗ Φ x y).
    Proof.
      iIntros "[#R AU]". iApply (aacc_ppost_wand with "AU"); auto.
      iIntros "!>" (x y). rewrite !tele_app_bind. iIntros "$". iFrame "R".
    Qed.
    Lemma aacc_ppost_frame_r :
      atomic_acc Eo Ei α P β Φ ∗ R ⊢
      atomic_acc Eo Ei α P β (λ.. x y, Φ x y ∗ R).
    Proof.
      rewrite comm aacc_ppost_frame_l.
      iIntros "AU". iApply (aacc_ppost_wand with "AU"); auto.
      iIntros "!>" (x y). rewrite !tele_app_bind comm. auto.
    Qed.
  End framing.

  (** Monotonicity *)
  Lemma aacc_apre_mono α1 α2 Eo Ei P β Φ :
    (∀.. x, α1 x ⊣⊢ α2 x) →
    atomic_acc Eo Ei α1 P β Φ ⊢ atomic_acc Eo Ei α2 P β Φ.
  Proof.
    rewrite tforall_forall.
    iIntros (Hα) "AU". iApply (aacc_apre_wand with "AU"); auto.
    (* PDS: Proofmode vs telescopes: should be able to [iApply] here. *)
    iIntros "!>" (x). iApply Hα.
  Qed.
  Lemma aacc_ppre_mono P1 P2 Eo Ei α β Φ :
    (P1 ⊢ P2) → atomic_acc Eo Ei α P1 β Φ ⊢ atomic_acc Eo Ei α P2 β Φ.
  Proof.
    iIntros (Hα) "AU". iApply (aacc_ppre_wand with "AU"); auto. iApply Hα.
  Qed.
  Lemma aacc_apost_mono β1 β2 Eo Ei α P Φ :
    (∀.. x y, β2 x y ⊢ β1 x y) →
    atomic_acc Eo Ei α P β1 Φ ⊢ atomic_acc Eo Ei α P β2 Φ.
  Proof.
    iIntros (Hβ) "AU". iApply (aacc_apost_wand with "AU"); auto.
    (* PDS: Proofmode vs telescopes: should be able to [iApply] here. *)
    iIntros "!>" (x y).
    move: Hβ=>/tforall_forall/(_ x) /tforall_forall/(_ y)=>Hβ.
    iApply Hβ.
  Qed.
  Lemma aacc_ppost_mono Φ1 Φ2 Eo Ei α P β :
    (∀.. x y, Φ1 x y ⊢ Φ2 x y) →
    atomic_acc Eo Ei α P β Φ1 ⊢ atomic_acc Eo Ei α P β Φ2.
  Proof.
    iIntros (HΦ) "AU". iApply (aacc_ppost_wand with "AU"); auto.
    (* PDS: Proofmode vs telescopes: should be able to [iApply] here. *)
    iIntros "!>" (x y).
    move: HΦ=>/tforall_forall/(_ x) /tforall_forall/(_ y)=>HΦ.
    iApply HΦ.
  Qed.

  Section proofmode.
    (** We prove no [Frame] instances. Atomic preconditions and atomic
    postconditions seem incompatible with [Frame]. Framing in the public
    precondition seems useless, and an instance would slow down IPM
    framing. We _want_ a [Frame] instance for public postconditions.

    PDS: Proving various [Frame] instances for public postconditions is
    easy. Writing them so they work, or debugging the typeclass
    resolution problems that arise is not (at least for me). *)

    (** We don't need an [IsExecpt0] instance for [atomic_acc], which
    lets the IPM strip laters from, e.g., timeless propositions when the
    goal is an atomic accessor. It's covered by the forwarding instance
    [elim_modal_acc], the [IsExcept0] instance for fancy updates, and
    the fact that the proof mode strips laters using [ElimModal]. *)
    Lemma test_is_except_0 Q Eo Ei α P β Φ `{!Timeless Q} :
      ▷ Q ⊢ atomic_acc Eo Ei α P β Φ.
    Proof. iIntros ">Q". Abort.

    (** Using [iMod] to eliminate an [atomic_acc] when the goal can be
    transformed into a fancy update at [Eo]. *)
    Lemma test_before Eo Ei α P β Φ :
      atomic_acc Eo Ei α P β Φ ⊢ |={Eo}=> emp.
    Proof. iIntros "AU". Fail iMod "AU". Abort.
    Global Instance elim_mod_aacc φ E Q Q' Eo Ei α β P Φ :
      (∀ R, ElimModal φ false false (|={E,Ei}=> R) R Q Q') →
      ElimModal (φ ∧ Eo ⊆ E) false false
        (atomic_acc Eo Ei α P β Φ)
        (∃.. x, α x ∗
          (α x ={Ei,E}=∗ P) ∧
          (∀.. y, β x y ={Ei,E}=∗ Φ x y)) Q Q'.
    Proof.
      intros ?. rewrite/ElimModal. simpl. iIntros ([??]) "[AU HQ]".
      rewrite (aacc_mask_weaken _ E)// /atomic_acc. iMod "AU".
      by iApply "HQ".
    Qed.
    Lemma test_after Eo Ei α P β Φ :
      atomic_acc Eo Ei α P β Φ ⊢ |={Eo}=> emp.
    Proof. iIntros "AU". iMod "AU". Abort.

    (** Let the proof mode specialization pattern [[> H1 ... Hn]] add
    fancy updates when the goal is an atomic accessor. *)
    Lemma test_before R Q Eo Ei α P β Φ :
      (R -∗ atomic_acc Eo Ei α P β Φ) ⊢ Q -∗ atomic_acc Eo Ei α P β Φ.
    Proof. iIntros "HR Q". Fail iSpecialize ("HR" with "[> Q]"). Abort.
    Global Instance add_modal_fupd_aacc R Eo Ei α P β Φ :
      AddModal (|={Eo}=> R) R (atomic_acc Eo Ei α P β Φ).
    Proof. rewrite/atomic_acc. apply _. Qed.
    Lemma test_after R Q Eo Ei α P β Φ :
      (R -∗ atomic_acc Eo Ei α P β Φ) ⊢ Q -∗ atomic_acc Eo Ei α P β Φ.
    Proof. iIntros "HR Q". iSpecialize ("HR" with "[> Q]"). Abort.
  End proofmode.
End atomic_acc.

(** * Atomic updates *)
Section atomic_update.
  Context `{BiFUpd PROP} {TA TB : tele}.
  Implicit Types (α : TA → PROP).
  Implicit Types (β Φ : TA → TB → PROP).

  (** Workhorse for rewriting parts of an atomic update. *)
  Lemma aupd_update Eo1 Eo2 Ei1 Ei2 α1 α2 β1 β2 Φ1 Φ2 :
    Eo1 ⊆ Eo2 → Ei2 ⊆ Ei1 →
    atomic_update Eo1 Ei1 α1 β1 Φ1 ⊢
    ((□ ∀.. x, α1 x ∗={Ei1}=∗ α2 x) ∗
     (∀.. x y, β2 x y ={Ei2}=∗ β1 x y) ∗
     (∀.. x y, Φ1 x y ={Eo1}=∗ Φ2 x y)) -∗
    atomic_update Eo2 Ei2 α2 β2 Φ2.
  Proof.
    iIntros (??) "AU (#Apre & Apost & Ppost)". iAuIntro. rewrite {1}aupd_aacc.
    iApply (aacc_update with "AU"); auto.
    iSplit?; [iModIntro|iIntros "$ !>"|..]; eauto with iFrame.
  Qed.

  (** Easy corollaries of [aupd_update] *)
  Section updates.
    Lemma aupd_mask_weaken Eo1 Eo2 Ei α β Φ :
      Eo1 ⊆ Eo2 → atomic_update Eo1 Ei α β Φ ⊢ atomic_update Eo2 Ei α β Φ.
    Proof.
      iIntros (?) "AU". iApply (aupd_update with "AU"); auto.
      iSplit?; [iModIntro|..|iSplitR]; auto.
    Qed.
    Lemma aupd_mask_strengthen Ei1 Ei2 Eo α β Φ :
      Ei1 ⊆ Ei2 → atomic_update Eo Ei2 α β Φ ⊢ atomic_update Eo Ei1 α β Φ.
    Proof.
      iIntros (?) "AU". iApply (aupd_update with "AU"); auto.
      iSplit?; [iModIntro|..|iSplitR]; auto.
    Qed.

    Lemma aupd_apre_fupd α1 α2 Eo Ei β Φ :
      atomic_update Eo Ei α1 β Φ ⊢
      □ (∀.. x, α1 x ∗={Ei}=∗ α2 x) -∗ atomic_update Eo Ei α2 β Φ.
    Proof.
      iIntros "AU #?". iApply (aupd_update with "AU"); auto.
      iSplit?; [iModIntro|..|iSplitR]; auto.
    Qed.
    Lemma aupd_apre_wand α1 α2 Eo Ei β Φ :
      atomic_update Eo Ei α1 β Φ ⊢
      □ (∀.. x, α1 x ∗-∗ α2 x) -∗ atomic_update Eo Ei α2 β Φ.
    Proof. rewrite aupd_apre_fupd. repeat f_equiv. apply fupd_iff_intro. Qed.

    Lemma aupd_apost_fupd β1 β2 Eo Ei α Φ :
      atomic_update Eo Ei α β1 Φ ⊢
      (∀.. x y, β2 x y ={Ei}=∗ β1 x y) -∗ atomic_update Eo Ei α β2 Φ.
    Proof.
      iIntros "AU ?". iApply (aupd_update with "AU"); auto.
      iSplit?; [iModIntro|..|iSplitL]; auto.
    Qed.
    Lemma aupd_apost_wand β1 β2 Eo Ei α Φ :
      atomic_update Eo Ei α β1 Φ ⊢
      (∀.. x y, β2 x y -∗ β1 x y) -∗ atomic_update Eo Ei α β2 Φ.
    Proof. rewrite aupd_apost_fupd. repeat f_equiv. apply fupd_intro. Qed.

    Lemma aupd_ppost_fupd Φ1 Φ2 Eo Ei α β :
      atomic_update Eo Ei α β Φ1 ⊢
      (∀.. x y, Φ1 x y ={Eo}=∗ Φ2 x y) -∗ atomic_update Eo Ei α β Φ2.
    Proof.
      iIntros "AU ?". iApply (aupd_update with "AU"); auto.
      iSplit?; [iModIntro|..|iSplitR]; auto.
    Qed.
    Lemma aupd_ppost_wand Φ1 Φ2 Eo Ei α β :
      atomic_update Eo Ei α β Φ1 ⊢
      (∀.. x y, Φ1 x y -∗ Φ2 x y) -∗ atomic_update Eo Ei α β Φ2.
    Proof. rewrite aupd_ppost_fupd. repeat f_equiv. apply fupd_intro. Qed.
  End updates.

  (** The analog [fupd_aupd] to [fupd_aacc] is unsound because fancy
  updates aren't [Laterable]. *)

  Lemma aupd_fupd Eo Ei α β Φ :
    atomic_update Eo Ei α β (λ.. x y, |={Eo}=> Φ x y) ⊢
    atomic_update Eo Ei α β Φ.
  Proof.
    iIntros "AU". iApply (aupd_update with "AU"); auto.
    iSplit?; [iModIntro|..|iSplitR]; auto.
    iIntros (x y) "HΦ". rewrite !tele_app_bind. iExact "HΦ".
  Qed.

  Section framing.
    Local Set Default Proof Using "Type*".
    Context (R : PROP) `{!Affine R, !Persistent R}.
    Context (Eo Ei : coPset) α β Φ.

    Lemma aupd_apre_frame_l :
      R ∗ atomic_update Eo Ei α β Φ ⊢ atomic_update Eo Ei (λ.. x, R ∗ α x) β Φ.
    Proof.
      iIntros "[#R AU]". iApply (aupd_apre_wand with "AU"); auto.
      iIntros "!>" (x). rewrite tele_app_bind. iSplit. (* R ⊢ (P ∗-∗ R ∗ P) *)
      - iIntros "$". iFrame "R".
      - iIntros "[_ $]".
    Qed.
    Lemma aupd_apre_frame_r :
      atomic_update Eo Ei α β Φ ∗ R ⊢ atomic_update Eo Ei (λ.. x, α x ∗ R) β Φ.
    Proof.
      rewrite comm aupd_apre_frame_l.
      iIntros "AU". iApply (aupd_apre_wand with "AU"); auto.
      iIntros "!>" (x). rewrite !tele_app_bind comm. auto.
    Qed.

    Lemma aupd_apost_frame_l :
      R ∗ atomic_update Eo Ei α β Φ ⊢
      atomic_update Eo Ei α (λ.. x y, R ∗ β x y) Φ.
    Proof.
      iIntros "[#R AU]". iApply (aupd_apost_wand with "AU"); auto.
      iIntros (x y). rewrite !tele_app_bind. iIntros "[_ $]".
    Qed.
    Lemma aupd_apost_frame_r :
      atomic_update Eo Ei α β Φ ∗ R ⊢
      atomic_update Eo Ei α (λ.. x y, β x y ∗ R) Φ.
    Proof.
      rewrite comm aupd_apost_frame_l.
      iIntros "AU". iApply (aupd_apost_wand with "AU"); auto.
      iIntros (x y). rewrite !tele_app_bind comm. auto.
    Qed.

    Lemma aupd_ppost_frame_l :
      R ∗ atomic_update Eo Ei α β Φ ⊢
      atomic_update Eo Ei α β (λ.. x y, R ∗ Φ x y).
    Proof.
      iIntros "[#R AU]". iApply (aupd_ppost_wand with "AU"); auto.
      iIntros (x y). rewrite !tele_app_bind. iIntros "$". iFrame "R".
    Qed.
    Lemma aupd_ppost_frame_r :
      atomic_update Eo Ei α β Φ ∗ R ⊢
      atomic_update Eo Ei α β (λ.. x y, Φ x y ∗ R).
    Proof.
      rewrite comm aupd_ppost_frame_l.
      iIntros "AU". iApply (aupd_ppost_wand with "AU"); auto.
      iIntros (x y). rewrite !tele_app_bind comm. auto.
    Qed.
  End framing.

  (** Monotonicity *)
  Lemma aupd_apre_mono α1 α2 Eo Ei β Φ :
    (∀.. x, α1 x ⊣⊢ α2 x) →
    atomic_update Eo Ei α1 β Φ ⊢ atomic_update Eo Ei α2 β Φ.
  Proof.
    rewrite tforall_forall.
    iIntros (Hα) "AU". iApply (aupd_apre_wand with "AU"); auto.
    (* PDS: Proofmode vs telescopes: should be able to [iApply] here. *)
    iIntros "!>" (x). iApply Hα.
  Qed.
  Lemma aupd_apost_mono β1 β2 Eo Ei α Φ :
    (∀.. x y, β2 x y ⊢ β1 x y) →
    atomic_update Eo Ei α β1 Φ ⊢ atomic_update Eo Ei α β2 Φ.
  Proof.
    iIntros (Hβ) "AU". iApply (aupd_apost_wand with "AU"); auto.
    (* PDS: Proofmode vs telescopes: should be able to [iApply] here. *)
    iIntros (x y).
    move: Hβ=>/tforall_forall/(_ x) /tforall_forall/(_ y)=>Hβ.
    iApply Hβ.
  Qed.
  Lemma aupd_ppost_mono Φ1 Φ2 Eo Ei α β :
    (∀.. x y, Φ1 x y ⊢ Φ2 x y) →
    atomic_update Eo Ei α β Φ1 ⊢ atomic_update Eo Ei α β Φ2.
  Proof.
    iIntros (HΦ) "AU". iApply (aupd_ppost_wand with "AU"); auto.
    (* PDS: Proofmode vs telescopes: should be able to [iApply] here. *)
    iIntros (x y).
    move: HΦ=>/tforall_forall/(_ x) /tforall_forall/(_ y)=>HΦ.
    iApply HΦ.
  Qed.

  (** Properties relevant to automation *)
  Section auto.
    (** Learn from an atomic precondition. (To use the bound variables
    [x], pick [P := ∃ x, P' x].) *)
    Lemma aupd_obs_fupd P Eo Ei α β Φ :
      atomic_update Eo Ei α β Φ ⊢
      (∀.. x, α x ={Ei}=∗ α x ∗ P) ={Eo}=∗ atomic_update Eo Ei α β Φ ∗ P.
    Proof.
      iIntros "AU Obs". iMod "AU" as (x) "[Hα Close]".
      iMod ("Obs" with "Hα") as "[Hα $]". by iMod ("Close" with "Hα") as "$".
    Qed.
    Lemma aupd_obs_wand P Eo Ei α β Φ :
      atomic_update Eo Ei α β Φ ⊢
      (∀.. x, α x -∗ α x ∗ P) ={Eo}=∗ atomic_update Eo Ei α β Φ ∗ P.
    Proof.
      iIntros "AU Obs". iApply (aupd_obs_fupd with "AU [Obs]").
      iIntros (x) "Hα !>". by iApply "Obs".
    Qed.
    Lemma aupd_obs P Eo Ei α β Φ :
      (∀.. x, α x ⊢ α x ∗ P) →
      atomic_update Eo Ei α β Φ ⊢ |={Eo}=> atomic_update Eo Ei α β Φ ∗ P.
    Proof.
      rewrite tforall_forall. iIntros (Hobs) "AU".
      iMod (aupd_obs_wand P with "AU []") as "$"; auto.
      iIntros (x). iApply Hobs.
    Qed.

    (** PDS: This is intended to help with zeta#390.

    Our aim is to change an atomic precondition based on knowledge
    gleaned from it. A common place where this can be used is to
    manifest pointers outside of atomic updates, e.g.

    [[ AU << this ., _foo |-> ... >> ... ]]

    becomes

    [[ valid_ptr (this ., _foo) ** AU << this ., _foo |-> ... >> ...]]. *)
    Lemma aupd_normalize (P : PROP) `{!Affine P, !Persistent P} α α' Eo Ei β Φ :
      (∀.. x, α x ⊣⊢ α' x ∗ P) →
      atomic_update Eo Ei α β Φ ⊢ |={Eo}=> atomic_update Eo Ei α' β Φ ∗ P.
    Proof.
      rewrite tforall_forall=>Obs. iIntros "AU".
      iMod (aupd_obs P with "AU") as "[AU #P]".
      { rewrite tforall_forall=>x. rewrite (Obs x). iIntros "[$ #$]". }
      iFrame "P". iModIntro. iApply (aupd_apre_wand with "AU").
      iIntros "!>" (x). rewrite (Obs x). iSplit.
      by iIntros "[$ _]". by iIntros "$"; iFrame "P".
    Qed.
  End auto.
End atomic_update.
