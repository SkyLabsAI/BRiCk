(*
 * Copyright (c) 2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
(** Definitions for the semantics
 *)
Require Import skylabs.prelude.base.

Require Import stdpp.coPset.
Require Import iris.bi.monpred.
Require Import skylabs.iris.extra.proofmode.proofmode.
Require Import iris.proofmode.classes.

Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.semantics.
Require Import skylabs.lang.cpp.logic.pred.
Require Import skylabs.lang.cpp.logic.heap_pred.
Require Import skylabs.lang.cpp.logic.translation_unit.
Require Import skylabs.lang.cpp.logic.free_temps.
Require Import skylabs.iris.extra.bi.errors.

#[local] Set Primitive Projections.

(* expression continuations
 * - in full C++, this includes exceptions, but our current semantics
 *   doesn't treat those.
 *)
Definition epred `{cpp_logic} := mpred.
Notation epredO := mpredO (only parsing).
Bind Scope bi_scope with epred.

Require skylabs.iris.extra.bi.linearity.

(* continuations
 * C++ statements can terminate in 4 ways.
 *
 * note(gmm): technically, they can also raise exceptions; however,
 * our current semantics doesn't capture this. if we want to support
 * exceptions, we should be able to add another case,
 * `k_throw : val -> mpred`.
 *)
Variant ReturnType : Set :=
| Normal
| Break
| Continue
| ReturnVal (_ : ptr)
| ReturnVoid
.
#[global] Instance ReturnType_ihn : Inhabited ReturnType.
Proof. repeat constructor. Qed.

Canonical Structure rt_biIndex : biIndex :=
  {| bi_index_type := ReturnType
   ; bi_index_rel := eq
   |}.
Definition KpredI `{!cpp_logic thread_info Σ} : bi := monPredI rt_biIndex (@mpredI thread_info Σ).
#[global] Notation Kpred := (bi_car KpredI).

Definition KP `{cpp_logic} (P : ReturnType -> mpred) : Kpred := MonPred P _.
#[global] Arguments KP {_ _ _} _%_I : assert.
#[global] Hint Opaque KP : typeclass_instances.

Section KP.
  Context `{Σ : cpp_logic}.

  Lemma KP_frame (Q1 Q2 : ReturnType -> mpred) (rt : ReturnType) :
    Q1 rt -* Q2 rt
    |-- KP Q1 rt -* KP Q2 rt.
  Proof. done. Qed.
End KP.

Definition Kat_exit `{Σ : cpp_logic} (Q : mpred -> mpred) (k : Kpred) : Kpred :=
  KP $ fun rt => Q (k rt).
#[global] Hint Opaque Kat_exit : typeclass_instances.

Section Kat_exit.
  Context `{Σ : cpp_logic}.

  Lemma Kat_exit_frame (Q Q' : mpred -> mpred) (k k' : Kpred) :
    Forall R R' : mpred, (R -* R') -* Q R -* Q' R' |--
    Forall rt : ReturnType, (k rt -* k' rt) -*
    Kat_exit Q k rt -* Kat_exit Q' k' rt.
  Proof.
    iIntros "HQ %rt Hk". destruct rt; cbn.
    all: by iApply "HQ".
  Qed.
End Kat_exit.

(*
NOTE KpredI does not embed into mpredI because it doesn't respect
existentials.
*)
#[global] Instance mpred_Kpred_BiEmbed `{Σ : cpp_logic} : BiEmbed mpredI KpredI := _.

Section with_cpp.
  Context `{Σ : cpp_logic}.

  Import linearity.


  #[local] Opaque FreeTemps.canon.

  #[local]
  Lemma K_entails (K : forall free : FreeTemps.t, FreeTemps.IsCanonical free -> mpred)
    free1 free2 pf1 pf2 :
    free1 ≡ free2 -> K free1 pf1 |-- K free2 pf2.
  Proof. intros. rewrite FreeTemps.K_ext; eauto. Qed.

  (* the monad for expression evaluation *)
  Record M {t : Type} := mk
    { _wp : (t -> forall free : FreeTemps.t, FreeTemps.IsCanonical free -> mpred) -> mpred
    ; _ok : forall K1 K2, (Forall x free pf, K1 x free pf -* K2 x free pf) |-- _wp K1 -* _wp K2 }.
  #[global] Arguments M _ : clear implicits.
  #[local] Coercion _wp : M >-> Funclass.

  (* The canonical notion of equivalence on [M _]

     This definition doesn't work, but it isn't clear how to fix it.
     The issues:
     - if you use pointwise equivalence for the [FreeTemps.t], then you
       lose the monad laws.
       You can get the bind-ret and ret-bind laws if you reify the unit,
       but you can not get bind-bind.
       **Idea**: use smart constructors that can canonicalize the definitions.
     - if you use the equivalence on [FreeTemps.t], then you can not prove
       this relation transitive because it requires that all functions satisfy
       the equivalence.
   *)
  #[global] Instance M_equiv [T] : Equiv (M T) :=
    fun a b =>
      forall K1 K2, (forall x y z, K1 x y z ⊣⊢ K2 x y z) -> a K1 ⊣⊢ b K2.
  #[global] Instance M_equiv_refl {T} : Reflexive (≡@{M T}).
  Proof.
    repeat red. intros.
    split'.
    { iApply _ok; iIntros (???). rewrite H; eauto. }
    { iApply _ok; iIntros (???). rewrite H; eauto. }
  Qed.
  #[global] Instance M_equiv_sym {T} : Symmetric (≡@{M T}).
  Proof.
    do 3 red; simpl; intros. symmetry; apply H.
    intros; symmetry. apply H0.
  Qed.
  #[global] Instance M_equiv_trans {T} : Transitive (≡@{M T}).
  Proof.
    repeat intro; simpl. etrans. eapply H. eapply H1.
    eapply H0. intros. reflexivity.
  Qed.

  (* The canonical notation of approximation/entailment
     Effectively, [a ⊆ b] if all behaviors of [a] are included in [b].
   *)
  #[global] Instance M_subseteq {T} : SubsetEq (M T) :=
    fun a b =>
      forall K1 K2, (forall x y z, K1 x y z ⊢ K2 x y z) -> a K1 ⊢ b K2.
  #[global] Instance M_subseteq_refl {T} : Reflexive (⊆@{M T}).
  Proof. repeat intro. iApply _ok; iIntros (???); iApply H. Qed.
  #[global] Instance M_subseteq_trans {T} : Transitive (⊆@{M T}).
  Proof.
    repeat intro. etrans.
    { iApply H. reflexivity. }
    { iApply H0. apply H1. }
  Qed.

  (** The distance metric on [M].
      TODO: will this work?
   *)
  #[global] Instance M_Dist {T} : Dist (M T) :=
    fun n a b =>
      forall K1 K2, (forall m (_ : m <= n) x y z, K1 x y z ≡{m}≡ K2 x y z) -> a K1 ≡{n}≡ b K2.

  (** ** Monad Operators *)

  #[program]
  Definition Mret {t : Type} (v : t) : M t :=
    {| _wp K := K v FreeTemps.id _ |}.
  Next Obligation.
    intros; simpl. iIntros "X"; iApply "X".
  Qed.

  #[program]
  Definition Mmap {t u : Type} (f : t -> u) (m : M t) : M u :=
    {| _wp K := m.(_wp) (fun t => K (f t)) |}.
  Next Obligation.
    intros; simpl.
    iIntros "X"; iApply _ok.
    iIntros (??); iApply "X".
  Qed.

  (* Question: Should we implement [ap]? *)

  #[program] Definition Mbind {T U} (c : M T) (k : T -> M U) : M U :=
    {| _wp K := c (fun v f _ => k v (fun v' f' _ => K v' (FreeTemps.canon $ f' >*> f)%free _)) |}.
  Next Obligation.
    simpl; intros. iIntros "K"; iApply _ok.
    iIntros (???). iApply _ok. iIntros (???); iApply "K".
  Qed.
  Notation "'letWP*' v := e 'in' k" := (Mbind e (fun v => k)) (at level 0, v binder, k at level 200).

  (**  These operations actually form a monad *)
  Lemma mret_mbind {T U} v (k : T -> M U) : Mbind (Mret v) k ≡ k v.
  Proof.
    red. rewrite /M_equiv/Mbind/Mret/=. red. simpl; intros.
    split'.
    { iApply _ok; iIntros (???) "?"; iStopProof.
      rewrite H; apply K_entails.
      by rewrite FreeTemps.canon_equiv FreeTemps.seq_id_unitR. }
    { iApply _ok; iIntros (???) "?"; iStopProof.
      rewrite H; apply K_entails.
      by rewrite FreeTemps.canon_equiv FreeTemps.seq_id_unitR. }
  Qed.

  Lemma mbind_mret {T} (m : M T) : Mbind m Mret ≡ m.
  Proof.
    red; rewrite /M_equiv/Mbind/Mret; red; simpl; intros.
    split'.
    { iApply _ok; iIntros (???) "?"; iStopProof.
      rewrite H; apply K_entails. rewrite FreeTemps.canon_equiv FreeTemps.seq_left_id; eauto. }
    { iApply _ok; iIntros (???) "?"; iStopProof.
      rewrite H; apply K_entails; rewrite FreeTemps.canon_equiv FreeTemps.seq_left_id; eauto. }
  Qed.

  Lemma mbind_mbind {T U V} (m : M T) (k1 : T -> M U) (k2 : U -> M V) :
    Mbind m (fun x => Mbind (k1 x) k2) ≡ Mbind (Mbind m k1) k2.
  Proof.
    red; rewrite /M_equiv/Mbind; red; simpl; intros.
    split';
      iApply _ok; iIntros (???); iApply _ok; iIntros (???); iApply _ok; iIntros (???);
      rewrite H; eauto; iIntros; iStopProof; apply K_entails.
    all: rewrite !FreeTemps.canon_equiv FreeTemps.seq_assoc; eauto.
  Qed.

  (** The interpreter for the monad
      This hides the canonicity proof because that is an implementation detail of the monad.
   *)
  Definition WP {T} (m : M T) (Q : T -> FreeTemps.t -> mpred) : mpred :=
    m (fun x f _ => Q x f).

  Definition Knormal {T U} (k : T -> M U) (Q : U -> FreeTemps.t -> mpred) : T -> FreeTemps.t -> mpred :=
    fun t free => k t (fun u free' _ => Q u (FreeTemps.canon (free' >*> free))).

  Lemma WP_Mbind {T U} (m : M T) (k : T -> M U) Q :
    WP m (Knormal k Q) |-- WP (Mbind m k) Q.
  Proof.
    rewrite /Mbind/WP/Knormal/=.
    iApply _ok; iIntros (???). eauto.
  Qed.

  Lemma WP_ret {T} (v : T) Q :
    Q v FreeTemps.id |-- WP (Mret v) Q.
  Proof. by rewrite /WP/Mret/=. Qed.

  (** ** The Effects of the Monad

      These currently follow the "operational logic" style used by tools
      such as Viper, but these could possibly be re-phrased in an
      operational but non-logical setup.

      Purely logical features such as fancy updates do not fit naturally
      into this setup.
   *)

  #[program]
  Definition Mproduce (P : mpred) : M unit :=
    {| _wp := fun K => P -* K () FreeTemps.id _ |}.
  Next Obligation.
    intros; simpl. iIntros "X Y P". iApply "X". iApply "Y". iApply "P".
  Qed.
  #[program]
    Definition Mconsume (P : mpred) : M unit :=
    {| _wp := fun K => P ** K () FreeTemps.id _ |}.
  Next Obligation.
    intros; simpl. iIntros "X [$ K]". iApply "X". iApply "K".
  Qed.

  Lemma WP_produce P Q :
    P -* Q () FreeTemps.id |-- WP (Mproduce P) Q.
  Proof. reflexivity. Qed.
  Lemma WP_consume P Q :
    P ** Q () FreeTemps.id |-- WP (Mconsume P) Q.
  Proof. reflexivity. Qed.

  Definition Massume (P : Prop) : M unit := Mproduce [| P |].
  Definition Mrequire (P : Prop) : M unit := Mconsume [| P |].

  #[program]
  Definition Mnd (t : Type) : M t :=
    {| _wp K := ∀ x : t, K x FreeTemps.id _ |}%I.
  Next Obligation.
    simpl; intros.
    iIntros "K X" (?); iApply "K"; eauto.
  Qed.
  #[program]
  Definition Mangelic (t : Type) : M t :=
    {| _wp K := ∃ x : t, K x FreeTemps.id _ |}%I.
  Next Obligation.
    simpl; intros.
    iIntros "K X"; iDestruct "X" as (?) "X"; iExists _; iApply "K"; eauto.
  Qed.

  #[program]
  Definition Mub {t : Type} : M t :=
    {| _wp _ := False%I |}.
  Next Obligation. simpl; intros. iIntros "? []". Qed.
  #[program]
  Definition Many {t : Type} : M t :=
    {| _wp _ := True%I |}.
  Next Obligation. simpl; intros; iIntros "? ?". iApply bi.pure_intro; [ trivial | ]. iStopProof. reflexivity. Qed.

  #[program]
  Definition Merror {t : Type} {ERR : Type} (err : ERR) : M t :=
    {| _wp _ := ERROR err |}.
  Next Obligation. simpl; intros. rewrite ERROR_False. iIntros "? []". Qed.

  #[program]
  Definition Mpush_free (f : FreeTemps.t) : M () :=
    {| _wp K := K () (FreeTemps.canon f) _ |}.
  Next Obligation. simpl; intros. iIntros "K"; iApply "K". Qed.

  #[program]
  Definition Matomically {t} (m : M t) : M t :=
    {| _wp K := |={top,∅}=> m.(_wp) (fun r free _ => |={∅,top}=> K r free _) |}%I.
  Next Obligation.
    simpl; intros. iIntros "K >X !>"; iRevert "X".
    iApply _ok. iIntros (???) ">X !>"; iRevert "X"; iApply "K".
  Qed.

  #[program]
  Definition Mnon_atomically {t} (m : M t) : M t :=
    {| _wp K := |={top}=> m.(_wp) (fun r free _ => |={top}=> K r free _) |}%I.
  Next Obligation.
    simpl; intros. iIntros "K >X !>"; iRevert "X".
    iApply _ok. iIntros (???) ">X !>"; iRevert "X"; iApply "K".
  Qed.

  #[program]
  Definition Mfupd (E1 E2 : coPset): M unit :=
    {| _wp K := |={E1,E2}=> K () FreeTemps.id _ |}%I.
  Next Obligation.
    simpl; intros. iIntros "K >X !>"; iRevert "X"; iApply "K".
  Qed.

  #[program]
  Definition Mstable : M unit :=
    {| _wp K := |={top}=> K () FreeTemps.id _ |}%I.
  Next Obligation.
    simpl; intros. iIntros "K >X !>"; iRevert "X"; iApply "K".
  Qed.

  #[program]
  Definition Mboth {t} (a b : M t) : M t :=
    {| _wp K := a K //\\ b K |}.
  Next Obligation.
    simpl; intros. iIntros "K X".
    iSplit; [ iDestruct "X" as "[X _]" | iDestruct "X" as "[_ X]" ]; iRevert "X"; iApply _ok; iIntros (??); iApply "K".
  Qed.

  (*
  Definition Mread {t} (R : t -> mpred) : M t :=
    MonPred (I:=M_index t) (fun K => Exists v, R v ** (R v -* K v FreeTemps.id)) _.
  Definition Mread_with {TT : tele} (R : TT -t> mpred) : M TT :=
    MonPred (I:=M_index TT) (fun K => ∃.. v, tele_app R v ** (tele_app R v -* K v FreeTemps.id))%I _.
   *)

  (** TODO: Probably better as a [Notation] *)
  Definition Frame {T} (a b : M T) : Prop :=
    forall Q Q', (Forall x y z, Q x y z -* Q' x y z) ⊢ a Q -* b Q'.
  Definition FrameWith {T} (P : T -> mpred) (a b : M T) : Prop :=
    forall Q Q', (Forall x y z, P x -* Q x y z -* Q' x y z) ⊢ a Q -* b Q'.
  Notation proper_Frame m := (Frame m m) (only parsing).

  Definition Mframe {T} (a b : M T) : mpred :=
    Forall Q Q', (Forall x y z, Q x y z -* Q' x y z) -* a Q -* b Q'.

  Definition Mimpl {T} (a b : M T) : mpred :=
    ∀ Q, a Q -* b Q.

  Lemma WP_impl {T} (a b : M T) Q : Mimpl a b |-- WP a Q -* WP b Q.
  Proof. rewrite /Mimpl. iIntros "X". iApply "X". Qed.

  Lemma Mmap_frame_strong {T U} c (f : T -> U) :
    Mframe c c
    |-- Forall Q Q', (Forall x y pf, Q (f x) y pf -* Q' (f x) y pf) -* Mmap f c Q -* Mmap f c Q'.
  Proof.
    rewrite /Mframe/Mmap; iIntros "A" (??) "B".
    iApply "A". iIntros (??); iApply "B".
  Qed.

  Lemma Mmap_frame {T U} c1 c2 (f : T -> U) :
    Mframe c1 c2 |-- Mframe (Mmap f c1) (Mmap f c2).
  Proof.
    rewrite /Mframe/Mmap; iIntros "A" (??) "B".
    iApply "A". iIntros (??); iApply "B".
  Qed.


  Lemma Mframe_refl {T} (m : M T) : |-- Mframe m m.
  Proof.
    rewrite /Mframe. iIntros (??) "X".
    iApply _ok. eauto.
  Qed.

  Lemma Mbind_frame {T U} c1 c2 (k1 k2 : T -> M U) :
    Mframe c1 c2 |-- (Forall x, Mframe (k1 x) (k2 x)) -* Mframe (Mbind c1 k1) (Mbind c2 k2).
  Proof.
    rewrite /Mframe/Mbind; iIntros "A B" (??) "C".
    iApply "A". iIntros (???). iApply "B".
    iIntros (???); iApply "C".
  Qed.

  (** *** Indeterminately sequenced computations
      Note that [FreeTemps.t] is sequenced in reverse order of construction
      to encode the stack discipline guaranteed by C++.
      (CITATION NEEDED)
   *)
  #[program]
  Definition nd_seq {T U} (wp1 : M T) (wp2 : M U) : M (T * U) :=
    Mboth (letWP* v1 := wp1 in
           letWP* v2 := wp2 in
           Mret (v1,v2))
          (letWP* v2 := wp2 in
           letWP* v1 := wp1 in
           Mret (v1,v2)).

  Lemma nd_seq_frame {T U} wp1 wp2 :
    Mframe wp1 wp1 |-- Mframe wp2 wp2 -* Mframe (@nd_seq T U wp1 wp2) (nd_seq wp1 wp2).
  Proof.
    iIntros "A B" (??) "C D".
    iSplit; [ iDestruct "D" as "[D _]" | iDestruct "D" as "[_ D]" ]; iRevert "D".
    { iApply "A". iIntros (???). iApply "B"; iIntros (???). iApply "C". }
    { iApply "B". iIntros (???). iApply "A"; iIntros (???). iApply "C". }
  Qed.

  (* Lifting non-deterministic sequencing to lists.

     NOTE: this is like the semantics of argument evaluation in C++.
   *)
  (*
  Fixpoint nd_seqs' {T} (f : nat) (qs : list (M T)) {struct f} : M (list T) :=
    match qs with
    | nil => Mret nil
    | _ :: _ =>
      match f with
      | 0 => Mub
      | S f => fun Q =>
        Forall pre post q, [| qs = pre ++ q :: post |] -*
               let lpre := length pre in
               Mbind q (fun t => Mmap (fun ts => firstn lpre ts ++ t :: skipn lpre ts) (nd_seqs' f (pre ++ post))) Q
      end
    end.
   *)

  Definition nd_seqs {T} (qs : list (M T)) : M (list T). (* := @nd_seqs' T (length qs) qs. *) Admitted.

  (*
  Lemma nd_seqs'_frame_strong {T} n : forall (ls : list (M T)) Q Q',
      n = length ls ->
      Forall x y, [| length x = length ls |] -* Q x y -* Q' x y
      |-- ([∗list] m ∈ ls, Mframe m m) -*
          nd_seqs' n ls Q -* nd_seqs' n ls Q'.
  Proof.
    induction n; simpl; intros.
    { case_match; eauto.
      subst. simpl.
      iIntros "X _". iApply "X". eauto. }
    { destruct ls. exfalso; simpl in *; congruence.
      inversion H.
      iIntros "X LS Y" (???) "%P".
      iSpecialize ("Y" $! pre).
      iSpecialize ("Y" $! post).
      iSpecialize ("Y" $! q).
      iDestruct ("Y" with "[]") as "Y"; first eauto.
      rewrite P.
      iDestruct "LS" as "(a&b&c)".
      iRevert "Y". rewrite /Mbind.
      iApply "b".
      iIntros (??).
      rewrite /Mmap.
      subst.
      assert (length ls = length (pre ++ post)).
      { have: (length (m :: ls) = length (pre ++ q :: post)) by rewrite P.
        rewrite !length_app /=. lia. }
      iDestruct (IHn with "[X]") as "X". eassumption.
      2:{
      iDestruct ("X" with "[a c]") as "X".
      iSplitL "a"; eauto.
      iApply "X". }
      simpl. iIntros (??) "%". iApply "X".
      revert H0 H1. rewrite !length_app/=.
      intros. iPureIntro.
      rewrite firstn_length_le; last lia.
      rewrite length_skipn. lia. }
  Qed.

  Lemma nd_seqs'_frame {T} n : forall (ls : list (M T)),
      n = length ls ->
      ([∗list] m ∈ ls, Mframe m m)
      |-- Mframe (nd_seqs' n ls) (nd_seqs' n ls).
  Proof.
    induction n; simpl; intros.
    { case_match.
      { subst. simpl.
        iIntros "_" (??) "X". iApply "X". }
      { iIntros "?" (??) "? []". } }
    { destruct ls. exfalso; simpl in *; congruence.
      inversion H.
      iIntros "LS" (??) "X Y"; iIntros (???) "%P".
      iSpecialize ("Y" $! pre).
      iSpecialize ("Y" $! post).
      iSpecialize ("Y" $! q).
      iDestruct ("Y" with "[]") as "Y"; first eauto.
      rewrite P.
      iDestruct "LS" as "(a&b&c)".
      iRevert "Y".
      iApply (Mbind_frame with "b [a c]"); eauto.
      iIntros (?).
      iApply Mmap_frame.
      rewrite -H1.
      iApply IHn.
      { have: (length (m :: ls) = length (pre ++ q :: post)) by rewrite P.
        rewrite !length_app /=. lia. }
      iSplitL "a"; eauto. }
  Qed.
  Lemma nd_seqs_frame : forall {T} (ms : list (_ T)),
      ([∗list] m ∈ ms, Mframe m m) |-- Mframe (nd_seqs ms) (nd_seqs ms).
  Proof. intros. by iApply nd_seqs'_frame. Qed.

  (* sanity check on [nd_seq] and [nd_seqs] *)
  Example nd_seq_example : forall {T} (a b : M T),
      Proper (Mrel _) a -> Proper (Mrel _) b ->
      Mequiv _ (nd_seqs [a;b]) (Mmap (fun '(a,b) => [a;b]) $ nd_seq a b).
  Proof.
    rewrite /nd_seqs/=; intros.
    rewrite /Mmap/nd_seq.
    repeat intro.
    iSplit.
    { iIntros "X".
      iSplit.
      { iSpecialize ("X" $! nil [b] a eq_refl).
        iRevert "X".
        iApply H. repeat intro; simpl.
        iIntros "X".
        iSpecialize ("X" $! nil nil b eq_refl).
        iRevert "X".
        iApply H0. repeat intro; simpl.
        rewrite /Mret.
        rewrite (H1 _ _ _) => //. by rewrite FreeTemps.seq_id_unitL. }
      { iSpecialize ("X" $! [a] nil b eq_refl).
        iRevert "X". iApply H0. repeat intro; simpl.
        iIntros "X".
        iSpecialize ("X" $! nil nil a eq_refl).
        iRevert "X".
        iApply H. repeat intro; simpl.
        rewrite /Mret.
        rewrite H1 => //. by rewrite FreeTemps.seq_id_unitL. } }
    { iIntros "X" (pre post m Horder).
      destruct pre.
      { inversion Horder; subst.
        iDestruct "X" as "[X _]".
        rewrite /Mbind. iApply H; last iAssumption.
        iIntros (??) => /=.
        iIntros "X" (pre' post' m' Horder').
        assert (pre' = [] /\ m' = b /\ post' = []) as [?[??]]; last subst.
        { clear - Horder'.
          destruct pre'.
          - inversion Horder'; subst; auto.
          - destruct pre'; inversion Horder'. }
        iApply H0; last iAssumption.
        iIntros (??) => /=; rewrite /Mret/=.
        rewrite H1 => //. by rewrite FreeTemps.seq_id_unitL. }
      { assert (a = m0 /\ b = m /\ pre = [] /\ post = []) as [?[?[??]]]; last subst.
        { clear -Horder.
          inversion Horder; subst.
          destruct pre; inversion H1; subst; eauto.
          destruct pre; inversion H2. }
        iDestruct "X" as "[_ X]".
        rewrite /Mbind. iApply H0; last iAssumption.
        iIntros (??) "H" => /=. iIntros (pre' post' m' Horder')=> /=.
        assert (m0 = m' /\ pre' = [] /\ post' = []) as [?[??]]; last subst.
        { destruct pre'; inversion Horder'; subst; eauto.
          destruct pre'; inversion H4. }
        iApply H; last iAssumption.
        iIntros (??). rewrite /=/Mret/=.
        rewrite H1 => //.
        by rewrite FreeTemps.seq_id_unitL. } }
  Qed.
  *)

  (** *** sequencing of monadic compuations *)
  Definition Mseq {T U} (wp1 : M T) (wp2 : M U) : M (T * U) :=
    Mbind wp1 (fun v => Mmap (fun x => (v, x)) wp2).

  Lemma Mseq_frame {T U} wp1 wp2 :
    Mframe wp1 wp1 |-- Mframe wp2 wp2 -* Mframe (@Mseq T U wp1 wp2) (Mseq wp1 wp2).
  Proof.
    iIntros "A B" (??) "C".
    rewrite /Mseq.
    iApply (Mbind_frame with "A [B]"); last iAssumption.
    iIntros (???) "X". iApply (Mmap_frame with "B"). done.
  Qed.

  (** [seqs es] is sequential evaluation of [es] *)
  Fixpoint seqs {T} (es : list (M T)) : M (list T) :=
    match es with
    | nil => Mret []
    | e :: es => Mmap (fun '(a,b) => a:: b) (Mseq e (seqs es))
    end.

  Lemma seqs_frame_strong {T} : forall (ls : list (M T)) Q Q',
      ([∗list] m ∈ ls, Mframe m m)%I
      |-- (Forall x y pf, [| length x = length ls |] -* Q x y pf -* Q' x y pf) -*
          (seqs ls Q) -* (seqs ls Q').
  Proof.
    induction ls; simpl; intros.
    - iIntros "_ X"; iApply "X"; eauto.
    - iIntros "[A AS] K".
      rewrite /Mbind. iApply "A".
      iIntros (???).
      iApply (IHls with "AS").
      iIntros (????).
      iApply "K". simpl. eauto.
  Qed.

  (** *** interleaving of monadic values

      We encode interleaving through concurrency which we represent through
      separable resources.

      NOTE: this is like the semantics of argument evaluation in C
   *)
  #[program]
  Definition Mpar {T U} (wp1 : M T) (wp2 : M U) : M (T * U) :=
    {| _wp K := Exists Q1 Q2, wp1 Q1 ** wp2 Q2 ** (Forall v1 v2 f1 f2 pf1 pf2, Q1 v1 f1 pf1 -* Q2 v2 f2 pf2 -* K (v1,v2) (FreeTemps.canon (f1 |*| f2)) _) |}.
  Next Obligation.
    simpl; intros.
    iIntros "K X". iDestruct "X" as (??) "[? [? Q]]".
    iExists Q1, Q2; iFrame. iIntros (??????) "Q1 Q2". iApply "K". iApply ("Q" with "Q1 Q2").
  Qed.

  Lemma Mpar_frame {T U} wp1 wp2 :
    Mframe wp1 wp1 |-- Mframe wp2 wp2 -* Mframe (@Mpar T U wp1 wp2) (Mpar wp1 wp2).
  Proof.
    iIntros "A B" (??) "C D".
    rewrite /Mpar/Mframe.
    iDestruct "D" as (??) "(D1 & D2 & K)".
    iExists _, _.
    iSplitL "D1 A".
    iApply "A". 2: eauto. iIntros (???) "X"; iApply "X".
    iSplitL "D2 B".
    iApply "B". 2: eauto. iIntros (???) "X"; iApply "X".
    iIntros (??????) "A B". iApply "C". iApply ("K" with "A B").
  Qed.


  (** lifting [Mpar] to homogeneous lists *)
  Fixpoint Mpars {T} (f : list (M T)) : M (list T) :=
    match f with
    | nil => Mret nil
    | f :: fs => Mmap (fun '(v, vs) => v :: vs) $ Mpar f (Mpars fs)
    end.

  Lemma Mpars_frame_strong {T} : forall (ls : list (M T)) Q Q',
      |-- (Forall x y pf, [| length x = length ls |] -* Q x y pf -* Q' x y pf) -*
          (Mpars ls Q) -* (Mpars ls Q').
  Proof.
    induction ls; simpl; intros.
    - iIntros "X"; iApply "X"; eauto.
    - iIntros "K".
      rewrite /Mmap.
      rewrite /Mpar.
      iIntros "X".
      iDestruct "X" as (??) "(L & R & KK)".
      iExists _, _. iFrame "L".
      iDestruct (IHls with "[] R") as "IH".
      2: iFrame "IH".
      { instantiate (1:=fun x y pf => [| length x = length ls |] ** Q2 x y pf).
        iIntros (???) "$". eauto. }
      iIntros (??????) "? [% ?]".
      iApply ("K" $! (v1::v2) (FreeTemps.canon (f1 |*| f2))).
      { simpl. eauto. }
      iApply ("KK" $! v1 v2 f1 f2 pf1 pf2 with "[$] [$]").
  Qed.

  (** *** evaluation by a scheme *)

  (** [eval eo e1 e2] evaluates [e1], [e2] according to the evaluation scheme [eo] *)
  Definition eval2 (eo : evaluation_order.t) {T U} (e1 : M T) (e2 : M U) : M (T * U) :=
    match eo with
    | evaluation_order.nd => nd_seq e1 e2
    | evaluation_order.l_nd => Mseq e1 e2
    | evaluation_order.rl => Mmap (fun '(a,b) => (b,a)) $ Mseq e2 e1
    end.

  (** [evals eo es] evaluates [es] according to the evaluation scheme [eo] *)
  Definition eval (eo : evaluation_order.t) {T} (es : list (M T)) : M (list T) :=
    match eo with
    | evaluation_order.nd => nd_seqs es
    | evaluation_order.l_nd =>
        match es with
        | e :: es => Mbind e (fun v => Mmap (fun vs => v :: vs) (nd_seqs es))
        | [] => Mret []
        end
    | evaluation_order.rl => Mmap (@rev _) (seqs (rev es))
    end.

  Lemma eval_frame_strong {T} oe : forall (ls : list (M T)) Q Q',
      ([∗list] m ∈ ls, Mframe m m)%I
      |-- (Forall x y pf, [| length x = length ls |] -* Q x y pf -* Q' x y pf) -*
          eval oe ls Q -* eval oe ls Q'.
  Proof. (*
    destruct oe; intros.
    - rewrite /=/nd_seqs. iIntros "A B".
      iApply (nd_seqs'_frame_strong with "B A"). done.
    - simpl.
      destruct ls; simpl.
      { iIntros "_ X"; iApply "X". done. }
      { iIntros "[X Y] K".
        iApply "X". iIntros (??).
        iApply (nd_seqs'_frame_strong with "[K] Y"); eauto.
        iIntros (???).
        rewrite /Mret.
        iApply "K". simpl; eauto. }
    - simpl.
      iIntros "X K".
      rewrite /Mmap. iApply (seqs_frame_strong with "[X]").
      { iStopProof. induction ls; simpl; eauto.
        iIntros "[$ K]".
        iDestruct (IHls with "K") as "$". eauto. }
      { iIntros (???); iApply "K".
        rewrite length_rev. eauto. rewrite -(length_rev ls). eauto. }
  Qed. *) Admitted.

  Fixpoint tuple (ts : list Type) : Type :=
    match ts return Type with
    | nil => unit
    | t :: ts => t * tuple ts
    end.

  (* TODO: this is the heterogeneous extension of [eval] *)
  Parameter heval : forall (eo : evaluation_order.t) {ts} (x : tuple (M <$> ts)), M (tuple ts).
End with_cpp.

Notation "'letWP*' v := e 'in' k" := (Mbind e (fun v => k)) (at level 0, v binder, k at level 200).
