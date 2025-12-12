(*
 * Copyright (C) 2020-21 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bluerock.lang.cpp.semantics.values.
Require Import bluerock.lang.cpp.logic.pred.
Require Import bluerock.iris.extra.proofmode.proofmode.
Require Import iris.proofmode.classes.

(** * Proof mode instances *)

(** We provide [_at], [_offsetR], and [pureR] instances for several
proof mode classes. Here's a subset, displayed here for [_at]:

- [IntoSep], [FromSep] for [loc |-> R1 ** R2]

- [IntoOr], [FromOr] for [loc |-> R1 \\// R2]

- [IntoAnd], [FromAnd] for [loc |-> R1 //\\ R2]

- [Frame] framing around [loc |-> R] if you can frame around [R]

Additional instances are available in

- [bluerock.proofmode.cpp._at_as_Rep]

- [bluerock.proofmode.cpp._at_pureR]

 *)

(** * Instances for [_at] *)
Section _at_instances.
  Context `{Σ : cpp_logic}.
  Implicit Types l : ptr.
  Implicit Types R : Rep.

  (** Feed the introduction pattern ["[H1 H2]"]. *)
  Lemma test_before l R1 R2 : l |-> (R1 ** R2) |-- l |-> R1 ** l |-> R2.
  Proof. Fail by iIntros "[$$]". Abort.

  #[global] Instance into_sep_at l R R1 R2 :
    IntoSep R R1 R2 → IntoSep (l |-> R) (l |-> R1) (l |-> R2).
  Proof.
    intros. rewrite /IntoSep. by rewrite (into_sep R) _at_sep.
  Qed.

  Lemma test_after l R1 R2 : l |-> (R1 ** R2) |-- l |-> R1 ** l |-> R2.
  Proof. by iIntros "[$$]". Abort.

  (** Feed the [iSplitL], [iSplitR], [iCombine] tactics. *)
  Lemma test_before l R1 R2 : l |-> R1 |-- l |-> R2 -* l |-> (R1 ** R2).
  Proof. iIntros "H1 H2". Fail by iSplitL "H1". Abort.
  Lemma test_before l R1 R2 : l |-> R1 |-- l |-> R2 -* l |-> (R1 ** R2).
  Proof. iIntros "H1 H2". Fail by iSplitR "H2". Abort.
  Lemma test_before l R1 R2 : l |-> R1 |-- l |-> R2 -* l |-> (R1 ** R2).
  Proof. iIntros "H1 H2". Fail by iCombine "H1 H2" as "H". Abort.

  #[global] Instance from_sep_at l R R1 R2 :
    FromSep R R1 R2 → FromSep (l |-> R) (l |-> R1) (l |-> R2).
  Proof.
    intros. rewrite /FromSep. by rewrite -_at_sep (from_sep R).
  Qed.

  #[global] Instance combine_sep_as_at l R R1 R2 :
    CombineSepAs R1 R2 R → CombineSepAs (l |-> R1) (l |-> R2) (l |-> R) | 10.
  Proof.
    intros. rewrite /CombineSepAs. by rewrite -_at_sep H.
  Qed.

  (* [CombineSepAs] does not have a base instance for [bi_sep] (unlike [FromSep]. *)
  #[global] Instance combine_sep_as_at_base l R1 R2 :
    CombineSepAs (l |-> R1) (l |-> R2) (l |-> (R1 ** R2)) | 100.
  Proof.
    intros. rewrite /CombineSepAs. by rewrite -_at_sep.
  Qed.

  Lemma test_after l R1 R2 : l |-> R1 |-- l |-> R2 -* l |-> (R1 ** R2).
  Proof. iIntros "H1 H2". by iSplitL "H1". Abort.
  Lemma test_after l R1 R2 : l |-> R1 |-- l |-> R2 -* l |-> (R1 ** R2).
  Proof. iIntros "H1 H2". by iSplitR "H2". Abort.
  Lemma test_after l R1 R2 : l |-> R1 |-- l |-> R2 -* l |-> (R1 ** R2).
  Proof. iIntros "H1 H2". by iCombine "H1 H2" as "H". Abort.


  (** [IntoWand], [FromWand] *)
  Lemma test_before l R1 R2 : l |-> (R1 -* R2) |-- l |-> R1 -* l |-> R2.
  Proof. iIntros "H R1". Fail iApply ("H" with "R1"). Abort.
  Lemma test_before l R : |-- l |-> (R -* R).
  Proof. Fail iIntros "R". Abort.

  #[global] Instance into_wand_at l p q R R1 R2 :
    IntoWand p q R R1 R2 → IntoWand p q (l |-> R) (l |-> R1) (l |-> R2).
  Proof.
    intros. rewrite /IntoWand -!_at_intuitionistically_if.
    by rewrite -_at_wand (into_wand p q R).
  Qed.
  #[global] Instance from_wand_at l R R1 R2 :
    FromWand R R1 R2 → FromWand (l |-> R) (l |-> R1) (l |-> R2).
  Proof.
    intros. rewrite /FromWand. by rewrite -_at_wand (from_wand R).
  Qed.

  Lemma test_after l R1 R2 : l |-> (R1 -* R2) |-- l |-> R1 -* l |-> R2.
  Proof. iIntros "H R1". iApply ("H" with "R1"). Abort.
  Lemma test_after l R : |-- l |-> (R -* R).
  Proof. iIntros "R". Abort.

  (** Feed the introduction pattern ["[]"] *)
  Lemma test_before (p : ptr) : p |-> False |-- False.
  Proof. Fail iIntros "[]". Abort.

  #[global] Instance _at_from_assumption pers (p : ptr) (R : Rep) (Q : Prop) :
    FromAssumption pers R (bi_pure Q) ->
    KnownLFromAssumption pers (p |-> R) (bi_pure Q).
  Proof.
    rewrite /FromAssumption; do 2 red; destruct pers; simpl;
      [ rewrite -_at_intuitionistically | ]; move => ->; by rewrite _at_pure.
  Qed.

  Lemma test_after (p : ptr) : p |-> False |-- False.
  Proof. iIntros "[]". Succeed Qed. Abort.

  (** Feed the introduction pattern ["[H1 H2]"]. *)
  Lemma test_before l R1 R2 : l |-> (R1 //\\ R2) |-- l |-> R1.
  Proof. Fail by iIntros "[$ _]". Abort.
  Lemma test_before l R1 R2 : l |-> (R1 //\\ R2) |-- l |-> R2.
  Proof. Fail by iIntros "[_ $]". Abort.

  #[global] Instance into_and_at p l R R1 R2 :
    IntoAnd p R R1 R2 → IntoAnd p (l |-> R) (l |-> R1) (l |-> R2).
  Proof.
    intros. rewrite /IntoAnd. rewrite -_at_intuitionistically_if into_and.
    by rewrite _at_intuitionistically_if _at_and.
  Qed.

  Lemma test_after l R1 R2 : l |-> (R1 //\\ R2) |-- l |-> R1.
  Proof. by iIntros "[$ _]". Abort.
  Lemma test_after l R1 R2 : l |-> (R1 //\\ R2) |-- l |-> R2.
  Proof. by iIntros "[_ $]". Abort.

  (** Feed the introduction pattern ["[H1|H2]"]. *)

  Lemma test_before l R1 R2 : l |-> (R1 \\// R2) |-- (l |-> R1 \\// l |-> R2).
  Proof. Fail by iIntros "[$ | $]". Abort.

  #[global] Instance into_or_at l R R1 R2 :
    IntoOr R R1 R2 -> IntoOr (l |-> R) (l |-> R1) (l |-> R2).
  Proof. intros. rewrite/IntoOr (into_or R) _at_or //. Qed.

  Lemma test_after l R1 R2 : l |-> (R1 \\// R2) |-- (l |-> R1 \\// l |-> R2).
  Proof. by iIntros "[$ | $]". Abort.

  (** Feed the [iSplit] tactic. *)
  Lemma test_before l R1 R2 : l |-> R1 //\\ l |-> R2 |-- l |-> (R1 //\\ R2).
  Proof. iIntros "H". Fail iSplit. Abort.

  #[global] Instance from_and_at l R R1 R2 :
    FromAnd R R1 R2 → FromAnd (l |-> R) (l |-> R1) (l |-> R2).
  Proof.
    intros. rewrite /FromAnd. by rewrite -_at_and (from_and R).
  Qed.

  Lemma test_after l R1 R2 : l |-> R1 //\\ l |-> R2 |-- l |-> (R1 //\\ R2).
  Proof. iIntros "H". iSplit. Abort.

  (** Feed the [iLeft] and [iRight] tactic. *)

  Lemma test_before l R1 R2 : l |-> R1 |-- l |-> (R1 \\// R2).
  Proof. iIntros "H". Fail iLeft. Abort.

  Lemma test_before l R1 R2 : l |-> R2 |-- l |-> (R1 \\// R2).
  Proof. iIntros "H". Fail iRight. Abort.

  #[global] Instance from_or_at l R R1 R2 :
    FromOr R R1 R2 -> FromOr (l |-> R) (l |-> R1) (l |-> R2).
  Proof. intros. rewrite/FromOr -_at_or (from_or R) //. Qed.

  Lemma test_after l R1 R2 : l |-> R1 |-- l |-> (R1 \\// R2).
  Proof. iIntros "H". by iLeft. Abort.

  Lemma test_after l R1 R2 : l |-> R2 |-- l |-> (R1 \\// R2).
  Proof. iIntros "H". by iRight. Abort.

  (** Feed the [iFrame] tactic. *)
  Lemma test_before l R1 R2 : l |-> R1 |-- l |-> R2 -* l |-> (R1 ** R2).
  Proof. iIntros "H1 H2". Fail iFrame "H1". Abort.
  Lemma test_before l R1 R2 : l |-> R1 |-- l |-> R2 -* l |-> (R1 ** R2).
  Proof. iIntros "H1 H2". Fail iFrame "H2". Abort.

  #[global] Instance frame_at p l R R1 R2 :
    Frame p R R1 R2 →
    Frame p (l |-> R) (l |-> R1) (l |-> R2) | 2. (* Prio 2 to not shadow [frame_here]. *)
  Proof.
    rewrite/Frame=><-. by rewrite -_at_intuitionistically_if -_at_sep.
  Qed.

  Lemma test_after l R1 R2 : l |-> R1 |-- l |-> R2 -* l |-> (R1 ** R2).
  Proof. iIntros "H1 H2". iFrame "H1". Abort.
  Lemma test_after l R1 R2 : l |-> R1 |-- l |-> R2 -* l |-> (R1 ** R2).
  Proof. iIntros "H1 H2". iFrame "H2". Abort.

  (** Framing between [P] and [_at p (pureR P)]. *)
  Lemma test_before l P : l |-> pureR P |-- P.
  Proof. Fail iIntros "$". Abort.
  #[global] Instance frame_at_pureR b l P :
    Frame b (l |-> pureR P) P emp | 2. (* Prio 2 to not shadow [frame_here]. *)
  Proof.
    rewrite /Frame _at_pureR. by rewrite bi.intuitionistically_if_elim right_id.
  Qed.
  Lemma test_after l P : l |-> pureR P |-- P.
  Proof. by iIntros "$". Abort.

  Lemma test_before l (P : mpred) : P |-- l |-> pureR P.
  Proof. Fail iIntros "$". Abort.
  #[global] Instance frame_pureR_at b l (P : mpred) :
    Frame b P (l |-> pureR P) emp | 2. (* Prio 2 to not shadow [frame_here]. *)
  Proof.
    rewrite /Frame _at_pureR. by rewrite bi.intuitionistically_if_elim right_id.
  Qed.
  Lemma test_after l (P : mpred) : P |-- l |-> pureR P.
  Proof. by iIntros "$". Abort.

  (** TODO (PDS): The following two instances suggest we should
      refactor and, perhaps, reproduce some of the monpred proofmode
      machinery for [_at]. We're repeating things that the proofmode
      already knows how to do. *)
  Lemma test_before l (P : mpred) R : P |-- l |-> (pureR P ** R).
  Proof. Fail iIntros "$". Abort.
  #[global] Instance frame_at_pureR_l l b (P1 P2 Q : mpred) R :
    Frame b P1 (P2 ** l |-> R) Q ->
    Frame b P1 (l |-> (pureR P2 ** R)) Q | 2. (* Prio 2 to not shadow [frame_here]. *)
  Proof. rewrite/Frame. by rewrite _at_sep _at_pureR. Qed.
  Lemma test_after l (P : mpred) R : P |-- l |-> (pureR P ** R).
  Proof. iIntros "$". Abort.

  Lemma test_before l (P : mpred) R : P |-- l |-> (R ** pureR P).
  Proof. Fail iIntros "$". Abort.
  #[global] Instance frame_at_pureR_r l b (P1 P2 Q : mpred) R :
    Frame b P1 (l |-> R ** P2) Q ->
    Frame b P1 (l |-> (R ** pureR P2)) Q | 2. (* Prio 2 to not shadow [frame_here]. *)
  Proof. rewrite/Frame. by rewrite _at_sep _at_pureR. Qed.
  Lemma test_after l (P : mpred) R : P |-- l |-> (R ** pureR P).
  Proof. iIntros "$". Abort.

  (** [IntoExist], [FromExist] *)
  Lemma test_before {A} l (Φ : A → Rep) :
    l |-> (Exists x, Φ x) |-- Exists x, l |-> Φ x.
  Proof. Fail iDestruct 1 as (x) "HΦ". Abort.
  Lemma test_before {A} l (Φ : A → Rep) :
    Exists x, l |-> Φ x |-- l |-> (Exists x, Φ x).
  Proof. iDestruct 1 as (x) "HΦ". Fail iExists x. Abort.

  #[global] Instance into_exist_at {A} {f} l R (Φ : A → Rep) :
    IntoExist R Φ f → IntoExist (l |-> R) (λ x, l |-> Φ x) f.
  Proof. intros H. by rewrite /IntoExist H _at_exists. Qed.
  #[global] Instance from_exist_at {A} l R (Φ : A → Rep) :
    FromExist R Φ → FromExist (l |-> R) (λ x, l |-> Φ x).
  Proof. intros H. by rewrite/FromExist -H _at_exists. Qed.

  Lemma test_after {A} l (Φ : A → Rep) :
    l |-> (Exists x, Φ x) |-- Exists x, l |-> Φ x.
  Proof. iDestruct 1 as (x) "HΦ". Abort.
  Lemma test_after {A} l (Φ : A → Rep) :
    Exists x, l |-> Φ x |-- l |-> (Exists x, Φ x).
  Proof. iDestruct 1 as (x) "HΦ". iExists x. Abort.

  (** [IntoForall], [FromForall] *)
  Lemma test_before {A} l (Φ : A → Rep) :
    l |-> (Forall x, Φ x) |-- Forall x, l |-> Φ x.
  Proof. iIntros "HΦ" (x). Fail iSpecialize ("HΦ" $! x). Abort.
  Lemma test_before {A} l (Φ : A → Rep) :
    Forall x, l |-> Φ x |-- l |-> Forall x, Φ x.
  Proof. Fail iIntros "HΦ" (x). Abort.

  #[global] Instance into_forall_at {A} l R (Φ : A → Rep) :
    IntoForall R Φ → IntoForall (l |-> R) (λ x, l |-> Φ x).
  Proof. intros H. by rewrite /IntoForall H _at_forall. Qed.
  #[global] Instance from_forall_at {A} l R (Φ : A → Rep) name :
    FromForall R Φ name → FromForall (l |-> R) (λ x, l |-> Φ x) name.
  Proof. intros H. by rewrite /FromForall -_at_forall H. Qed.

  Lemma test_after {A} l (Φ : A → Rep) :
    l |-> (Forall x, Φ x) |-- Forall x, l |-> Φ x.
  Proof. iIntros "HΦ" (x). iSpecialize ("HΦ" $! x). Abort.
  Lemma test_after {A} l (Φ : A → Rep) :
    Forall x, l |-> Φ x |-- l |-> Forall x, Φ x.
  Proof. iIntros "H" (x). iApply "H". Abort.

  (* [ElimModal] instance.
     NOTE Instances like this one that generate sub-derivations using [pureR] require
     corresponding instances for [pureR] (see below).
   *)
  #[global] Instance _at_elim_modal (pt : ptr) ϕ p p' P P' Q Q' :
    ElimModal ϕ p p' P P' (pureR Q) (pureR Q') ->
    ElimModal ϕ p p' (_at pt P) (_at pt P') Q Q'.
  Proof.
    intros H HPQ. apply H, bi.wand_intro_r in HPQ.
    rewrite -!_at_intuitionistically_if HPQ !_at_wand !_at_pureR.
    iIntros "[A B]". by iApply "A".
  Qed.

  (* [IntoPure] instance. *)
  Lemma test_before {P : Prop} (p : ptr) : _at p (bi_pure P) |-- True.
  Proof. Fail iIntros "%". Abort.

  #[global] Instance _at_into_pure {p P T} : IntoPure P T -> IntoPure (_at p P) T.
  Proof. by red; intros ->; rewrite _at_pure. Qed.

  Lemma test_after {P : Prop} (p : ptr) : _at p (bi_pure P) |-- True.
  Proof. iIntros "%". Abort.

  Lemma test_before {P : Prop} (p : ptr) : ⊢@{mpredI} _at p (bi_pure P).
  Proof. iIntros. Fail iPureIntro. Abort.

  #[global] Instance _at_from_pure {a p R T} (H : FromPure a R T) : FromPure a (_at p R) T.
  Proof. by red; red in H; rewrite -H _at_affinely_if _at_pure. Qed.

  Lemma test_after {P : Prop} (p : ptr) : ⊢@{mpredI} _at p (bi_pure P).
  Proof. iIntros. iPureIntro. Abort.

  (* [IsExcept0] *)
  #[global] Instance is_except0_at {R p} (H : IsExcept0 R) : IsExcept0 (_at p R).
  Proof. red. by rewrite -_at_except_0 H. Qed.

End _at_instances.

(** * Instances for [_offsetR] *)
Section _offsetR_instances.
  Context `{Σ : cpp_logic}.
  Implicit Types o : offset.
  Implicit Types R : Rep.
  Implicit Types P : mpred.

  (** Feed the introduction pattern ["[H1 H2]"]. *)
  Lemma test_before o R1 R2 : o |-> (R1 ** R2) |-- o |-> R1 ** o |-> R2.
  Proof. Fail by iIntros "[$$]". Abort.

  #[global] Instance into_sep_offsetR o R R1 R2 :
    IntoSep R R1 R2 → IntoSep (o |-> R) (o |-> R1) (o |-> R2).
  Proof.
    intros. rewrite /IntoSep. by rewrite (into_sep R) _offsetR_sep.
  Qed.

  Lemma test_after o R1 R2 : o |-> (R1 ** R2) |-- o |-> R1 ** o |-> R2.
  Proof. by iIntros "[$$]". Abort.

  (** Feed the introduction pattern ["[H1|H2]"]. *)

  Lemma test_before o R1 R2 : o |-> (R1 \\// R2) |-- (o |-> R1 \\// o |-> R2).
  Proof. Fail by iIntros "[$|$]". Abort.

  #[global] Instance into_or_offsetR o R R1 R2 :
    IntoOr R R1 R2 -> IntoOr (o |-> R) (o |-> R1) (o |-> R2).
  Proof. intros. rewrite /IntoOr. by rewrite (into_or R) _offsetR_or. Qed.

  Lemma test_after o R1 R2 : o |-> (R1 \\// R2) |-- (o |-> R1 \\// o |-> R2).
  Proof. by iIntros "[$|$]". Abort.

  (** Feed the [iSplitL], [iSplitR], [iCombine] tactics. *)
  Lemma test_before o R1 R2 : o |-> R1 |-- o |-> R2 -* o |-> (R1 ** R2).
  Proof. iIntros "H1 H2". Fail by iSplitL "H1". Abort.
  Lemma test_before o R1 R2 : o |-> R1 |-- o |-> R2 -* o |-> (R1 ** R2).
  Proof. iIntros "H1 H2". Fail by iSplitR "H2". Abort.
  Lemma test_before o R1 R2 : o |-> R1 |-- o |-> R2 -* o |-> (R1 ** R2).
  Proof. iIntros "H1 H2". Fail by iCombine "H1 H2" as "H". Abort.

  #[global] Instance from_sep_offsetR o R R1 R2 :
    FromSep R R1 R2 → FromSep (o |-> R) (o |-> R1) (o |-> R2).
  Proof.
    intros. rewrite /FromSep. by rewrite -_offsetR_sep (from_sep R).
  Qed.

  #[global] Instance combine_sep_as_offsetR o R R1 R2 :
    CombineSepAs R1 R2 R → CombineSepAs (o |-> R1) (o |-> R2) (o |-> R) | 10.
  Proof.
    intros. rewrite /CombineSepAs. by rewrite -_offsetR_sep H.
  Qed.

  (* [CombineSepAs] does not have a base instance for [bi_sep] (unlike [FromSep]. *)
  #[global] Instance combine_sep_as_at_offsetR o R1 R2 :
    CombineSepAs (o |-> R1) (o |-> R2) (o |-> (R1 ** R2)) | 100.
  Proof.
    intros. rewrite /CombineSepAs. by rewrite -_offsetR_sep.
  Qed.

  Lemma test_after o R1 R2 : o |-> R1 |-- o |-> R2 -* o |-> (R1 ** R2).
  Proof. iIntros "H1 H2". by iSplitL "H1". Abort.
  Lemma test_after o R1 R2 : o |-> R1 |-- o |-> R2 -* o |-> (R1 ** R2).
  Proof. iIntros "H1 H2". by iSplitR "H2". Abort.
  Lemma test_after o R1 R2 : o |-> R1 |-- o |-> R2 -* o |-> (R1 ** R2).
  Proof. iIntros "H1 H2". by iCombine "H1 H2" as "H". Abort.

  (** Feed the [iLeft] and [iRight] tactics. *)
  Lemma test_before o R1 R2 : o |-> R1 |-- o |-> (R1 \\// R2).
  Proof. iIntros "H". Fail by iLeft. Abort.

  Lemma test_before o R1 R2 : o |-> R2 |-- o |-> (R1 \\// R2).
  Proof. iIntros "H". Fail by iRight. Abort.

  #[global] Instance from_or_offsetR o R R1 R2 :
    FromOr R R1 R2 -> FromOr (o |-> R) (o |-> R1) (o |-> R2).
  Proof. intros. rewrite /FromOr. by rewrite -_offsetR_or (from_or R). Qed.

  Lemma test_after o R1 R2 : o |-> R1 |-- o |-> (R1 \\// R2).
  Proof. iIntros "H". by iLeft. Abort.

  Lemma test_after o R1 R2 : o |-> R2 |-- o |-> (R1 \\// R2).
  Proof. iIntros "H". by iRight. Abort.

  (** [IntoWand], [FromWand] *)
  Lemma test_before o R1 R2 : o |-> (R1 -* R2) |-- o |-> R1 -* o |-> R2.
  Proof. iIntros "H R1". Fail iApply ("H" with "R1"). Abort.
  Lemma test_before o R : |-- o |-> (R -* R).
  Proof. Fail iIntros "R". Abort.

  #[global] Instance into_wand_offsetR o p q R R1 R2 :
    IntoWand p q R R1 R2 → IntoWand p q (o |-> R) (o |-> R1) (o |-> R2).
  Proof.
    intros. rewrite /IntoWand -!_offsetR_intuitionistically_if.
    by rewrite -_offsetR_wand (into_wand p q R).
  Qed.
  #[global] Instance from_wand_offsetR o R R1 R2 :
    FromWand R R1 R2 → FromWand (o |-> R) (o |-> R1) (o |-> R2).
  Proof.
    intros. rewrite /FromWand. by rewrite -_offsetR_wand (from_wand R).
  Qed.

  Lemma test_after o R1 R2 : o |-> (R1 -* R2) |-- o |-> R1 -* o |-> R2.
  Proof. iIntros "H R1". iApply ("H" with "R1"). Abort.
  Lemma test_after o R : |-- o |-> (R -* R).
  Proof. iIntros "R". Abort.

  (** Feed the introduction pattern ["[]"] *)
  Lemma test_before (o : offset) : o |-> False |-- False.
  Proof. Fail iIntros "[]". Abort.

  #[global] Instance _offsetR_from_assumption pers (o : offset) (R : Rep) (Q : Prop) :
    FromAssumption pers R (bi_pure Q) ->
    KnownLFromAssumption pers (o |-> R) (bi_pure Q).
  Proof.
    rewrite /FromAssumption; do 2 red; destruct pers; simpl;
      [ rewrite -_offsetR_intuitionistically | ]; move => ->; by rewrite _offsetR_pure.
  Qed.

  Lemma test_after (o : offset) : o |-> False |-- False.
  Proof. iIntros "[]". Succeed Qed. Abort.

  (** Feed the introduction pattern ["[H1 H2]"]. *)
  Lemma test_before o R1 R2 : o |-> (R1 //\\ R2) |-- o |-> R1.
  Proof. Fail by iIntros "[$ _]". Abort.
  Lemma test_before o R1 R2 : o |-> (R1 //\\ R2) |-- o |-> R2.
  Proof. Fail by iIntros "[_ $]". Abort.

  #[global] Instance into_and_offsetR p o R R1 R2 :
    IntoAnd p R R1 R2 → IntoAnd p (o |-> R) (o |-> R1) (o |-> R2).
  Proof.
    intros. rewrite /IntoAnd. rewrite -_offsetR_intuitionistically_if into_and.
    by rewrite _offsetR_intuitionistically_if _offsetR_and.
  Qed.

  Lemma test_before o R1 R2 : o |-> (R1 //\\ R2) |-- o |-> R1.
  Proof. by iIntros "[$ _]". Abort.
  Lemma test_before o R1 R2 : o |-> (R1 //\\ R2) |-- o |-> R2.
  Proof. by iIntros "[_ $]". Abort.

  (** Feed the [iSplit] tactic. *)
  Lemma test_before o R1 R2 : o |-> R1 //\\ o |-> R2 |-- o |-> (R1 //\\ R2).
  Proof. iIntros "H". Fail iSplit. Abort.

  #[global] Instance from_and_offsetR o R R1 R2 :
    FromAnd R R1 R2 → FromAnd (o |-> R) (o |-> R1) (o |-> R2).
  Proof.
    intros. rewrite /FromAnd. by rewrite -_offsetR_and (from_and R).
  Qed.

  Lemma test_after o R1 R2 : o |-> R1 //\\ o |-> R2 |-- o |-> (R1 //\\ R2).
  Proof. iIntros "H". iSplit. Abort.

  (** Feed the [iFrame] tactic. *)
  Lemma test_before o R1 R2 : o |-> R1 |-- o |-> R2 -* o |-> (R1 ** R2).
  Proof. iIntros "H1 H2". Fail iFrame "H1". Abort.
  Lemma test_before o R1 R2 : o |-> R1 |-- o |-> R2 -* o |-> (R1 ** R2).
  Proof. iIntros "H1 H2". Fail iFrame "H2". Abort.

  #[global] Instance frame_offsetR p o R R1 R2 :
    Frame p R R1 R2 →
    Frame p (o |-> R) (o |-> R1) (o |-> R2) | 2. (* Prio 2 to not shadow [frame_here]. *)
  Proof.
    rewrite/Frame=><-. by rewrite -_offsetR_intuitionistically_if -_offsetR_sep.
  Qed.

  Lemma test_after o R1 R2 : o |-> R1 |-- o |-> R2 -* o |-> (R1 ** R2).
  Proof. iIntros "H1 H2". iFrame "H1". Abort.
  Lemma test_after o R1 R2 : o |-> R1 |-- o |-> R2 -* o |-> (R1 ** R2).
  Proof. iIntros "H1 H2". iFrame "H2". Abort.

  (** Framing between [P] and [_offsetR o (pureR P)]. *)

  Lemma test_before (p : ptr) o R : p |-> o |-> R |-- p ,, o |-> R.
  Proof. Fail by iIntros "$". Abort.
  #[global] Instance frame_at_offsetR_1 b (p : ptr) o R P (Q : mpred) :
    Frame b (p ,, o |-> R) P Q ->
    Frame b (p |-> o |-> R) P Q | 2. (* Prio 2 to not shadow [frame_here]. *)
  Proof. by rewrite/Frame _at_offsetR=>->. Qed.
  Lemma test_after (p : ptr) o R : p |-> o |-> R |-- p ,, o |-> R.
  Proof. by iIntros "$". Abort.

  (** TODO (PDS): Both the preceding and the following would make TC
      resolution diverge. [Hint Cut] might help, as might enabling the
      IPM's [monPred] framing instances to apply to [_at]. *)
  Section todo.
    Lemma test_before (p : ptr) o R : p ,, o |-> R |-- p |-> o |-> R.
    Proof. Fail by iIntros "$". Abort.
    (** TODO (proofmode): Given [p ,, o |-> R] we should be able to
        frame to get [p |-> o |-> R]. *)
    Lemma frame_at_offsetR_2 b (p : ptr) o R P (Q : mpred) :
      Frame b (p |-> o |-> R) P Q ->
      Frame b (p ,, o |-> R) P Q.
    Proof. by rewrite/Frame _at_offsetR=>->. Qed.
    Existing Instance frame_at_offsetR_2 | 2. (* Prio 2 to not shadow [frame_here]. *)
    Lemma test_after (p : ptr) o R : p ,, o |-> R |-- p |-> o |-> R.
    Proof. by iIntros "$". Abort.
  End todo.

  (** [IntoExist], [FromExist] *)
  Lemma test_before {A} o (R : A → Rep) :
    o |-> (Exists x, R x) |-- Exists x, o |-> R x.
  Proof. Fail iDestruct 1 as (x) "R". Abort.
  Lemma test_before {A} o (R : A → Rep) :
    Exists x, o |-> R x |-- o |-> (Exists x, R x).
  Proof. iDestruct 1 as (x) "R". Fail iExists x. Abort.

  #[global] Instance into_exist_offsetR {A} o R1 (R2 : A → Rep) name :
    IntoExist R1 R2 name → IntoExist (o |-> R1) (λ x, o |-> R2 x) name.
  Proof. intros H. by rewrite /IntoExist H _offsetR_exists. Qed.
  #[global] Instance from_exist_offsetR {A} o R1 (R2 : A → Rep) :
    FromExist R1 R2 → FromExist (o |-> R1) (λ x, o |-> R2 x).
  Proof. intros H. by rewrite/FromExist -H _offsetR_exists. Qed.

  Lemma test_after {A} o (R : A → Rep) :
    o |-> (Exists x, R x) |-- Exists x, o |-> R x.
  Proof. iDestruct 1 as (x) "R". Abort.
  Lemma test_after {A} o (R : A → Rep) :
    Exists x, o |-> R x |-- o |-> (Exists x, R x).
  Proof. iDestruct 1 as (x) "R". iExists x. Abort.

  (** [IntoForall], [FromForall] *)
  Lemma test_before {A} o (R : A → Rep) :
    o |-> (Forall x, R x) |-- Forall x, o |-> R x.
  Proof. iIntros "R" (x). Fail iSpecialize ("R" $! x). Abort.
  Lemma test_before {A} o (R : A → Rep) :
    Forall x, o |-> R x |-- o |-> Forall x, R x.
  Proof. Fail iIntros "R" (x). Abort.

  #[global] Instance into_forall_offsetR {A} o R1 (R2 : A → Rep) :
    IntoForall R1 R2 → IntoForall (o |-> R1) (λ x, o |-> R2 x).
  Proof. intros H. by rewrite /IntoForall H _offsetR_forall. Qed.
  #[global] Instance from_forall_offsetR {A} o R1 (R2 : A → Rep) name :
    FromForall R1 R2 name → FromForall (o |-> R1) (λ x, o |-> R2 x) name.
  Proof. intros H. by rewrite /FromForall -_offsetR_forall H. Qed.

  Lemma test_after {A} o (R : A → Rep) :
    o |-> (Forall x, R x) |-- Forall x, o |-> R x.
  Proof. iIntros "R" (x). iSpecialize ("R" $! x). Abort.
  Lemma test_after {A} o (R : A → Rep) :
    Forall x, o |-> R x |-- o |-> Forall x, R x.
  Proof. iIntros "R" (x). iApply "R". Abort.

  (* [FromPure] *)
  Lemma test_before {P : Prop} (o : offset) : |-- _offsetR o (bi_pure P).
  Proof. iIntros. Fail iPureIntro. Abort.

  #[global] Instance _offsetR_from_pure {a o R T} (H : FromPure a R T) : FromPure a (_offsetR o R) T.
  Proof. by red; red in H; rewrite -H _offsetR_affinely_if _offsetR_pure. Qed.

  Lemma test_after {P : Prop} (o : offset) : |-- _offsetR o (bi_pure P).
  Proof. iIntros. iPureIntro. Abort.

  (* [IntoPure] *)
  #[global] Instance _offsetR_into_pure {p} {P : Rep} {T} : IntoPure P T -> IntoPure (_offsetR p P) T.
  Proof. red; intros ->; by rewrite _offsetR_pure. Qed.

  Lemma test_after {P : Prop} (o : offset) : _offsetR o (bi_pure P) |-- True.
  Proof. iIntros "%". Abort.

  (* [IsExcept0] *)
  #[global] Instance is_except0_offsetR {R o} (H : IsExcept0 R) : IsExcept0 (_offsetR o R).
  Proof. red. by rewrite -_offsetR_except_0 H. Qed.

End _offsetR_instances.

(** * Instances for [pureR] *)
Section pureR_instances.
  Context `{Σ : cpp_logic}.
  Implicit Types R : Rep.
  Implicit Types P : mpred.

  (** Feed the introduction pattern ["[H1 H2]"]. *)
  Lemma test_before P1 P2 : pureR (P1 ** P2) |-- pureR P1 ** pureR P2.
  Proof. Fail by iIntros "[$$]". Abort.

  #[global] Instance into_sep_pureR P P1 P2 :
    IntoSep P P1 P2 → IntoSep (pureR P) (pureR P1) (pureR P2).
  Proof.
    intros. rewrite /IntoSep. by rewrite (into_sep P) pureR_sep.
  Qed.

  Lemma test_after P1 P2 : pureR (P1 ** P2) |-- pureR P1 ** pureR P2.
  Proof. by iIntros "[$$]". Abort.

  (** Feed the [iSplitL], [iSplitR], [iCombine] tactics. *)
  Lemma test_before P1 P2 : pureR P1 |-- pureR P2 -* pureR (P1 ** P2).
  Proof. iIntros "H1 H2". Fail by iSplitL "H1". Abort.
  Lemma test_before P1 P2 : pureR P1 |-- pureR P2 -* pureR (P1 ** P2).
  Proof. iIntros "H1 H2". Fail by iSplitR "H2". Abort.
  Lemma test_before P1 P2 : pureR P1 |-- pureR P2 -* pureR (P1 ** P2).
  Proof. iIntros "H1 H2". Fail by iCombine "H1 H2" as "H". Abort.

  #[global] Instance from_sep_pureR P P1 P2 :
    FromSep P P1 P2 → FromSep (pureR P) (pureR P1) (pureR P2).
  Proof.
    intros. rewrite /FromSep. by rewrite -pureR_sep (from_sep P).
  Qed.

  #[global] Instance combine_sep_as_pureR P P1 P2 :
    CombineSepAs P1 P2 P → CombineSepAs (pureR P1) (pureR P2) (pureR P) | 10.
  Proof.
    intros. rewrite /CombineSepAs. by rewrite -pureR_sep H.
  Qed.

  (* [CombineSepAs] does not have a base instance for [bi_sep] (unlike [FromSep]. *)
  #[global] Instance combine_sep_as_pureR_base P1 P2 :
    CombineSepAs (pureR P1) (pureR P2) (pureR (P1 ** P2)) | 100.
  Proof.
    intros. rewrite /CombineSepAs. by rewrite -pureR_sep.
  Qed.

  Lemma test_after P1 P2 : pureR P1 |-- pureR P2 -* pureR (P1 ** P2).
  Proof. iIntros "H1 H2". by iSplitL "H1". Abort.
  Lemma test_after P1 P2 : pureR P1 |-- pureR P2 -* pureR (P1 ** P2).
  Proof. iIntros "H1 H2". by iSplitR "H2". Abort.
  Lemma test_after P1 P2 : pureR P1 |-- pureR P2 -* pureR (P1 ** P2).
  Proof. iIntros "H1 H2". by iCombine "H1 H2" as "H". Abort.

  (** [IntoWand], [FromWand] *)
  Lemma test_before P1 P2 : pureR (P1 -* P2) |-- pureR P1 -* pureR P2.
  Proof. iIntros "H P1". Fail iApply ("H" with "P1"). Abort.
  Lemma test_before P : |-- pureR (P -* P).
  Proof. Fail iIntros "P". Abort.

  #[global] Instance into_wand_pureR p q P P1 P2 :
    IntoWand p q P P1 P2 → IntoWand p q (pureR P) (pureR P1) (pureR P2).
  Proof.
    intros. rewrite /IntoWand -!pureR_intuitionistically_if.
    by rewrite -pureR_wand (into_wand p q P).
  Qed.
  #[global] Instance from_wand_pureR P P1 P2 :
    FromWand P P1 P2 → FromWand (pureR P) (pureR P1) (pureR P2).
  Proof.
    intros. rewrite /FromWand. by rewrite -pureR_wand (from_wand P).
  Qed.

  Lemma test_after P1 P2 : pureR (P1 -* P2) |-- pureR P1 -* pureR P2.
  Proof. iIntros "H P1". iApply ("H" with "P1"). Abort.
  Lemma test_after P : |-- pureR (P -* P).
  Proof. iIntros "P". Abort.

  (** Feed the introduction pattern ["[H1 H2]"]. *)
  Lemma test_before P1 P2 : pureR (P1 //\\ P2) |-- pureR P1.
  Proof. Fail by iIntros "[$ _]". Abort.
  Lemma test_before P1 P2 : pureR (P1 //\\ P2) |-- pureR P2.
  Proof. Fail by iIntros "[_ $]". Abort.

  #[global] Instance into_and_pureR p P P1 P2 :
    IntoAnd p P P1 P2 → IntoAnd p (pureR P) (pureR P1) (pureR P2).
  Proof.
    intros. rewrite /IntoAnd. rewrite -pureR_intuitionistically_if into_and.
    by rewrite pureR_intuitionistically_if pureR_and.
  Qed.

  Lemma test_before P1 P2 : pureR (P1 //\\ P2) |-- pureR P1.
  Proof. by iIntros "[$ _]". Abort.
  Lemma test_before P1 P2 : pureR (P1 //\\ P2) |-- pureR P2.
  Proof. by iIntros "[_ $]". Abort.

  (** Feed the [iSplit] tactic. *)
  Lemma test_before P1 P2 : pureR P1 //\\ pureR P2 |-- pureR (P1 //\\ P2).
  Proof. iIntros "H". Fail iSplit. Abort.

  #[global] Instance from_and_pureR P P1 P2 :
    FromAnd P P1 P2 → FromAnd (pureR P) (pureR P1) (pureR P2).
  Proof.
    intros. rewrite /FromAnd. by rewrite -pureR_and (from_and P).
  Qed.

  Lemma test_after P1 P2 : pureR P1 //\\ pureR P2 |-- pureR (P1 //\\ P2).
  Proof. iIntros "H". iSplit. Abort.

  (** Feed the [iFrame] tactic. *)
  Lemma test_before P1 P2 : pureR P1 |-- pureR P2 -* pureR (P1 ** P2).
  Proof. iIntros "H1 H2". Fail iFrame "H1". Abort.
  Lemma test_before P1 P2 : pureR P1 |-- pureR P2 -* pureR (P1 ** P2).
  Proof. iIntros "H1 H2". Fail iFrame "H2". Abort.

  #[global] Instance frame_pureR p P P1 P2 :
    Frame p P P1 P2 →
    Frame p (pureR P) (pureR P1) (pureR P2) | 2. (* Prio 2 to not shadow [frame_here]. *)
  Proof.
    rewrite/Frame=><-. by rewrite -pureR_intuitionistically_if -pureR_sep.
  Qed.

  Lemma test_after P1 P2 : pureR P1 |-- pureR P2 -* pureR (P1 ** P2).
  Proof. iIntros "H1 H2". iFrame "H1". Abort.
  Lemma test_after P1 P2 : pureR P1 |-- pureR P2 -* pureR (P1 ** P2).
  Proof. iIntros "H1 H2". iFrame "H2". Abort.

  (** [IntoExist], [FromExist] *)
  Lemma test_before {A} (P : A → mpred) :
    pureR (Exists x, P x) |-- Exists x, pureR (P x).
  Proof. Fail iDestruct 1 as (x) "P". Abort.
  Lemma test_before {A} (P : A → mpred) :
    Exists x, pureR (P x) |-- pureR (Exists x, P x).
  Proof. iDestruct 1 as (x) "P". Fail iExists x. Abort.

  #[global] Instance into_exist_pureR {A} P1 (P2 : A → mpred) name :
    IntoExist P1 P2 name → IntoExist (pureR P1) (λ x, pureR (P2 x)) name.
  Proof. intros H. by rewrite /IntoExist H pureR_exist. Qed.
  #[global] Instance from_exist_pureR {A} P1 (P2 : A → mpred) :
    FromExist P1 P2 → FromExist (pureR P1) (λ x, pureR (P2 x)).
  Proof. intros H. by rewrite/FromExist -H pureR_exist. Qed.

  Lemma test_after {A} (P : A → mpred) :
    pureR (Exists x, P x) |-- Exists x, pureR (P x).
  Proof. iDestruct 1 as (x) "P". Abort.
  Lemma test_after {A} (P : A → mpred) :
    Exists x, pureR (P x) |-- pureR (Exists x, P x).
  Proof. iDestruct 1 as (x) "P". iExists x. Abort.

  (** [IntoForall], [FromForall] *)
  Lemma test_before {A} (P : A → mpred) :
    pureR (Forall x, P x) |-- Forall x, pureR (P x).
  Proof. iIntros "P" (x). Fail iSpecialize ("P" $! x). Abort.
  Lemma test_before {A} (P : A → mpred) :
    Forall x, pureR (P x) |-- pureR (Forall x, P x).
  Proof. Fail iIntros "P" (x). Abort.

  #[global] Instance into_forall_pureR {A} P1 (P2 : A → mpred) :
    IntoForall P1 P2 → IntoForall (pureR P1) (λ x, pureR (P2 x)).
  Proof. intros H. by rewrite /IntoForall H pureR_forall. Qed.
  #[global] Instance from_forall_pureR {A} P1 (P2 : A → mpred) name :
    FromForall P1 P2 name → FromForall (pureR P1) (λ x, pureR (P2 x)) name.
  Proof. intros H. by rewrite /FromForall -pureR_forall H. Qed.

  Lemma test_after {A} (P : A → mpred) :
    pureR (Forall x, P x) |-- Forall x, pureR (P x).
  Proof. iIntros "P" (x). iSpecialize ("P" $! x). Abort.
  Lemma test_after {A} (P : A → mpred) :
    Forall x, pureR (P x) |-- pureR (Forall x, P x).
  Proof. iIntros "P" (x). iApply "P". Abort.

  (** Feeding the [iInv] tactic to open invariants written [pureR Inv]
  or [offset |-> pureR Inv] doesn't currently seem possible. The
  generality of the proof mode's [IntoAcc] and [accessor] wrt
  arbitrary modalities doesn't work well with [monPred]. We can
  specialize those to fancy updates (which covers all
  invariant-related [IntoAcc] instances in Iris), but a problem
  remains. The underlying lemma [coq_tactics.tac_inv_elim] generates
  an entailment involving [monPred] that the tactic [iInv] seems
  unable to handle. *)

  #[global] Instance is_except0_pureR {P} (H : IsExcept0 P) : IsExcept0 (pureR P).
  Proof.
    red. red in H. apply Rep_entails_at => p.
      by rewrite !_at_pureR !_at_except_0 !_at_pureR.
  Qed.

  Lemma test_before {P : Prop} (p : ptr) : p |-> pureR (bi_pure P) |-- True.
  Proof. Fail iIntros "%". Abort.

  #[global] Instance into_pure_pureR {P T} (H : IntoPure P T) : IntoPure (pureR P) T.
  Proof. red. apply Rep_entails_at => p. by rewrite H !_at_pure _at_pureR. Qed.

  Lemma test_after {P : Prop} (p : ptr) : p |-> pureR (bi_pure P) |-- True.
  Proof. iIntros "%". Abort.

  (* [FromPure] *)
  Lemma test_before {P : Prop} (p : ptr) : |-- p |-> pureR (bi_pure P).
  Proof. iIntros. Fail iPureIntro. Abort.

  #[global] Instance from_pure_pureR {a P T} (H : FromPure a P T) : FromPure a (pureR P) T.
  Proof.
    apply Rep_entails_at => p. by rewrite _at_affinely_if _at_pure _at_pureR.
  Qed.

  Lemma test_after {P : Prop} (p : ptr) : |-- p |-> pureR (bi_pure P).
  Proof. iIntros. iPureIntro. Abort.

  (** Feed the introduction pattern ["[]"] *)
  Lemma test_before (o : offset) : o |-> pureR False |-- False.
  Proof. Fail iIntros "[]". Abort.

  #[global] Instance pureR_from_assumption pers P (Q : Prop) :
    FromAssumption pers P (bi_pure Q) ->
    KnownLFromAssumption pers (pureR P) (bi_pure Q).
  Proof.
    rewrite /FromAssumption; do 2 red; destruct pers; simpl;
      [ rewrite -pureR_intuitionistically | ]; move => ->; eauto.
  Qed.

  Lemma test_after (o : offset) : o |-> pureR False |-- False.
  Proof. iIntros "[]". Succeed Qed. Abort.

End pureR_instances.
