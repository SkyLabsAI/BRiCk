(*
 * Copyright (c) 2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
(** Definitions for the semantics
 *)
Require Import skylabs.prelude.base.
Require Import skylabs.upoly.base.

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


(*
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
*)

Module Compose.
  Section Compose.
    #[local] Set Universe Polymorphism.
    Import UPoly.

    Context {F : Type -> Type} {G : Type -> Type}.

    Record M {t} : Type := mk
                             { _prun : F (G t) }.
    #[global] Arguments mk {_} & _.
    #[global] Arguments M _ : clear implicits.

    #[global] Instance _MRet {F_RET : MRet F} {G_RET : MRet G} : MRet M :=
      fun _ x => mk (mret (M:=F) (mret (M:=G) x)).
    #[global] Instance _FMap {F_FMAP : FMap F} {G_FMAP : FMap G} : FMap M :=
      fun _ _ f x => mk (fmap (M:=F) (fmap (M:=G) f) x.(_prun)).
    #[global] Instance _Ap {FMAP : FMap F} {F_AP : Ap F} {G_AP : Ap G} : Ap M :=
      fun _ _ f x => mk ((ap (F:=G)) <$> f.(_prun) <*> x.(_prun)).

    (* NOTE: [Compose.M] is not a [Monad] in general *)

  End Compose.
  #[global] Arguments M _ _ _ : clear implicits.
End Compose.

Module sumT.
  Section sumT.
    Import UPoly.

    Context {ERR : Type}.
    Context {mM : Type -> Type}.

    Record M {t : Type} : Type :=
      { prun : mM (ERR + t) }.

  End sumT.
End sumT.


Require Import skylabs.prelude.telescopes.

(* TODO: the names here probably need to be in a module *)
Class WpMonad (PROP : bi) {F : BiFUpd PROP} (M : Type -> Type) : Type :=
{ angelic : forall T : Type, M T
; demonic : forall T : Type, M T
; produce : PROP -> M unit
; consume : PROP -> M unit
; check : forall {TT : tele}, (TT -t> PROP) -> M TT
; update : forall {TT1 TT2 : tele}, (TT1 -t> PROP) -> (TT1 -t> TT2 -t> PROP) ->
                               M (tele_arg (tele_append TT1 (tele_bind (fun _ : TT1 => TT2))))
; ac : forall {TT: tele} (Apre : TT -t> PROP) (Eouter Einner : coPset)
         {TT' : tele} (Apost : TT -t> TT' -t> PROP), M (tele_arg (tele_append TT (tele_bind (fun _ : TT => TT'))))

; step : M unit
; ub : forall {T}, M T
; contra : forall {T}, M T
  (* TODO: below this is all that needs Fupd *)
; atomically : forall {T}, M T -> M T
; non_atomically : forall {T}, M T -> M T
}.

mlock
Definition Munsupported `{WP : @WpMonad PROP F M} {T E} (err : E) : M T :=
  ub.

mlock
Definition Merror `{WP : @WpMonad PROP F M} {T E} (err : E) : M T :=
  ub.


Section evaluation.
  Import UPoly.
  #[local] Set Universe Polymorphism.
  Context {M : Type -> Type} {RET : MRet M} {BIND : MBind M}.
  Context (Mforall : forall T, M T).

  Notation Mboth A B := (letM* b := Mforall bool in if b is true then A else B) (only parsing).
  (** *** Indeterminately sequenced computations
      Note that [FreeTemps.t] is sequenced in reverse order of construction
      to encode the stack discipline guaranteed by C++.
      (CITATION NEEDED)
   *)
  #[program]
  Definition nd_seq {T U} (wp1 : M T) (wp2 : M U) : M (T * U) :=
    Mboth (letM* v1 := wp1 in
           letM* v2 := wp2 in
           mret (v1,v2))
          (letM* v2 := wp2 in
           letM* v1 := wp1 in
           mret (v1,v2)).

  (* Lifting non-deterministic sequencing to lists.

     NOTE: this is like the semantics of argument evaluation in C++.
   *)
  Fixpoint nd_seqs' {T} (f : nat) (ms : list (M T)) {struct f} : M (list T) :=
    match ms with
    | nil => mret nil
    | _ :: _ =>
      match f return M (list T) with
      | 0 => mret nil
      | S f =>
        (* NOTE: this is still a finite choice *)
        letM* pre := Mforall (list (M T)) in
        letM* post := Mforall (list (M T)) in
        letM* (m : M T) := Mforall (M T) in
        letM* pf := Mforall (ms = pre ++ m :: post) in
        let lpre := length pre in
        (fun (t : T) (ts : list T) =>
           firstn lpre ts ++ t :: skipn lpre ts) <$> m <*> nd_seqs' f (pre ++ post)
      end
    end.

  Definition nd_seqs {T} (qs : list (M T)) : M (list T) := @nd_seqs' T (length qs) qs.

  (*
  Lemma nd_seqs'_frame_strong {T} n : forall (ls : list (M T)) Q Q',
      n = length ls ->
      Forall x y, [| length x = length ls |] -* Q x y -* Q' x y
      |-- ([∗list] m ∈ ls, FrameI m m) -*
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
      ([∗list] m ∈ ls, FrameI m m)
      |-- FrameI (nd_seqs' n ls) (nd_seqs' n ls).
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
      ([∗list] m ∈ ms, FrameI m m) |-- FrameI (nd_seqs ms) (nd_seqs ms).
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
    pair <$> wp1 <*> wp2.

  (*
  Lemma Mseq_frame {T U} wp1 wp2 :
    FrameI wp1 wp1 |-- FrameI wp2 wp2 -* FrameI (@Mseq T U wp1 wp2) (Mseq wp1 wp2).
  Proof.
    iIntros "A B" (??) "C".
    rewrite /Mseq.
    iApply (Mbind_frame with "A [B]"); last iAssumption.
    iIntros (???) "X". iApply (Mmap_frame with "B"). done.
  Qed.
  *)

  (** [seqs es] is sequential evaluation of [es] *)
  Fixpoint seqs {T} (es : list (M T)) : M (list T) :=
    match es with
    | nil => mret []
    | e :: es => (fun '(a,b) => a :: b) <$> (Mseq e (seqs es))
    end.

  (*
  Lemma seqs_frame_strong {T} : forall (ls : list (M T)) Q Q',
      ([∗list] m ∈ ls, FrameI m m)%I
      |-- (Forall x y pf, [| length x = length ls |] -* Q x y pf -* Q' x y pf) -*
          (seqs ls Q) -* (seqs ls Q').
  Proof.
    induction ls; simpl; intros.
    - iIntros "_ X"; iApply "X"; eauto.
    - iIntros "[A AS] K".
      rewrite /M_bind. iApply "A".
      iIntros (???).
      iApply (IHls with "AS").
      iIntros (????).
      iApply "K". simpl. eauto.
  Qed.
  *)

  (*
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
    FrameI wp1 wp1 |-- FrameI wp2 wp2 -* FrameI (@Mpar T U wp1 wp2) (Mpar wp1 wp2).
  Proof.
    iIntros "A B" (??) "C D".
    rewrite /Mpar/FrameI.
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
    | nil => mret nil
    | f :: fs => (fun '(v, vs) => v :: vs) <$> Mpar f (Mpars fs)
    end.

  Lemma Mpars_frame_strong {T} : forall (ls : list (M T)) Q Q',
      |-- (Forall x y pf, [| length x = length ls |] -* Q x y pf -* Q' x y pf) -*
          (Mpars ls Q) -* (Mpars ls Q').
  Proof.
    induction ls; simpl; intros.
    - iIntros "X"; iApply "X"; eauto.
    - iIntros "K".
      rewrite /M_map.
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
  *)

  (* TODO: Begin C++ *)
  (** *** evaluation by a scheme *)

  (** [eval eo e1 e2] evaluates [e1], [e2] according to the evaluation scheme [eo] *)
  Definition eval2 (eo : evaluation_order.t) {T U} (e1 : M T) (e2 : M U) : M (T * U) :=
    match eo with
    | evaluation_order.nd => nd_seq e1 e2
    | evaluation_order.l_nd => Mseq e1 e2
    | evaluation_order.rl => (fun '(a,b) => (b,a)) <$> Mseq e2 e1
    end.

  (** [evals eo es] evaluates [es] according to the evaluation scheme [eo] *)
  Definition eval (eo : evaluation_order.t) {T} (es : list (M T)) : M (list T) :=
    match eo with
    | evaluation_order.nd => nd_seqs es
    | evaluation_order.l_nd =>
        match es with
        | e :: es => letM* v := e in (fun vs => v :: vs) <$> (nd_seqs es)
        | [] => mret []
        end
    | evaluation_order.rl => (@rev _) <$> (seqs (rev es))
    end.

  (*
  Lemma eval_frame_strong {T} oe : forall (ls : list (M T)) Q Q',
      ([∗list] m ∈ ls, FrameI m m)%I
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
  *)
End evaluation.



(*
Fixpoint tele_append_nd (TT : tele) (TT' : tele) : tele :=
  match TT with
  | TeleO => TT'
  | @TeleS t f => TeleS (fun x : t => tele_append_nd (f x) TT')
  end.

#[program]
Definition Mac `{_ : @WpMonad PROP FUPD M} {TT: tele} (Apre : TT -t> PROP) (Eouter Einner : coPset)
  {TT' : tele} (Apost : TT -t> TT' -t> PROP) : M (tele_arg (tele_append TT (tele_bind (fun _ : TT => TT')))) :=
  {| }
Proof. Admitted.
*)


(** [Mglobal] -- normal + exceptions
      = M ((type * ptr) + t)
    [Mexpr] -- (normal + exceptions + break + return + continue) * freetemps
      = M (Result (ReturnType t))
 *)


(** This monad is language agnostic *)
Module M.
Section M.
  Import UPoly.
  Context {PROP : bi}.

  Record M {t : Type} := mk
  { _wp : (t -> PROP) -> PROP
  ; _frame : forall K1 K2, (∀ x, K1 x -∗ K2 x) ⊢ _wp K1 -∗ _wp K2
  ; _ne : forall n K1 K2, (forall x, K1 x ≡{n}≡ K2 x) -> _wp K1 ≡{n}≡ _wp K2
  }.
  #[global] Arguments M _ : clear implicits.
  #[local] Coercion _wp : M >-> Funclass.

  (* The canonical notion of equivalence on [M _] *)
  #[global] Instance M_equiv [T] : Equiv (M T) :=
    fun a b =>
      forall K1 K2, (forall x, K1 x ⊣⊢ K2 x) -> a K1 ⊣⊢ b K2.
  #[global] Instance M_equiv_refl {T} : Reflexive (≡@{M T}).
  Proof.
    repeat red. intros.
    split'.
    { iApply _frame; iIntros (?). rewrite H; eauto. }
    { iApply _frame; iIntros (?). rewrite H; eauto. }
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
      forall K1 K2, (forall x, K1 x ⊢ K2 x) -> a K1 ⊢ b K2.
  #[global] Instance M_subseteq_refl {T} : Reflexive (⊆@{M T}).
  Proof. repeat intro. iApply _frame; iIntros (?); iApply H. Qed.
  #[global] Instance M_subseteq_trans {T} : Transitive (⊆@{M T}).
  Proof.
    repeat intro. etrans.
    { iApply H. reflexivity. }
    { iApply H0. apply H1. }
  Qed.

  (** The distance metric on [M]. *)
  #[global] Instance M_Dist {T} : Dist (M T) :=
    fun n (a b : M T) =>
      forall K1 K2, (forall x, K1 x ≡{n}≡ K2 x) -> a K1 ≡{n}≡ b K2.

  #[global] Instance M_Dist_refl {T} : forall n, Reflexive (dist (A:=M T) n).
  Proof. intros; intro. red; red. simpl. apply _ne. Qed.
  #[global] Instance M_Dist_sym {T} : forall n, Symmetric (dist (A:=M T) n).
  Proof.
    intros; intro. red; red. simpl. intros.
    symmetry. apply H. intros. symmetry. apply H0.
  Qed.
  #[global] Instance M_Dist_trans {T} : forall n, Transitive (dist (A:=M T) n).
  Proof.
    intros; intro. red; red. simpl. intros.
    etrans. eapply H. eassumption. eapply H0. done.
  Qed.

  #[global,program]
  Instance M_ret : MRet M :=
    fun _ v => {| _wp K := K v |}.
  Next Obligation.
    intros; simpl. iIntros "X"; iApply "X".
  Qed.
  Next Obligation. intros; simpl. auto. Qed.
  #[global,program]
  Instance M_map : FMap M :=
    fun _ _ f m => {| _wp K := m.(_wp) (fun t => K (f t)) |}.
  Next Obligation.
    intros; simpl.
    iIntros "X"; iApply _frame.
    iIntros (?); iApply "X".
  Qed.
  Next Obligation.
    intros; simpl. apply _ne. eauto.
  Qed.
  #[global,program]
  Instance M_bind : MBind M :=
    fun _ _ k c =>
      {| _wp K := c (fun v => (k v).(_wp) K) |}.
  Next Obligation.
    simpl; intros. iIntros "K"; iApply _frame.
    iIntros (?). iApply _frame. done.
  Qed.
  Next Obligation.
    simpl; intros. apply _ne. intros.
    apply _ne. eauto.
  Qed.

  (** *** Additional Monad Operators *)
  Fixpoint tele_arg_append_simple {TT1 TT2 : tele} (x : TT1) (y : TT2)
    : tele_arg (tele_append TT1 (tele_bind (fun _ => TT2))) :=
    match TT1 as TT1 return TT1 -> tele_arg (tele_append TT1 (tele_bind (fun _ : TT1 => TT2))) with
    | TeleO => fun _ => y
    | TeleS TT1 => fun x =>
                     TeleArgCons (tele_arg_head _ x) (tele_arg_append_simple (tele_arg_tail _ x) y)
    end x.

  #[global,program]
  Instance M_WpMonad `{BiFUpd PROP} : WpMonad PROP M :=
  { angelic T := {| _wp K := ∃ x : T, K x |}%I
  ; demonic T := {| _wp K := ∀ x : T, K x |}%I
  ; produce P := {| _wp K := P -∗ K () |}%I
  ; consume P := {| _wp K := P ∗ K () |}%I
  ; check _ P := {| _wp K := ∃.. x, (tele_app P x ∗ True) ∧ K x |}%I
  ; update _ _ P Q :=
      {| _wp K := ∃.. x, tele_app P x ∗
                           (∀.. y, tele_app (tele_app Q x) y -∗ K (tele_arg_append_simple x y)) |}%I
  ; contra _ := {| _wp _K := True |}%I
  ; ub _ := {| _wp _K := False |}%I
  ; step := {| _wp K := ▷ K () |}%I
  ; non_atomically _ m := {| _wp K := |={top}=> m.(_wp) (fun r => |={top}=> K r) |}%I
  ; atomically _ m := {| _wp K := |={top,∅}=> m.(_wp) (fun r => |={top,∅}=> K r) |}%I
  }.
  Admit Obligations.
  (*
  #[program]
  Definition non_atomically `{BiFUpd PROP} {T} (m : M T) : M T :=
    {| _wp K := |={top}=> m.(_wp) (fun r => |={top}=> K r) |}%I.
  Next Obligation.
    simpl. intros. iIntros "K >X !>".
    iRevert "X"; iApply M._ok. iIntros (?) ">X !>". iRevert "X"; iApply "K".
  Qed.

  #[program]
  Definition atomically `{BiFUpd PROP} {T} (m : M T) : M T :=
    {| _wp K := |={top,∅}=> m.(_wp) (fun r => |={top,∅}=> K r) |}%I.
  Next Obligation.
    simpl. intros. iIntros "K >X !>".
    iRevert "X"; iApply M._ok. iIntros (?) ">X !>". iRevert "X"; iApply "K".
  Qed.



  #[program]
  Definition update (step : bool) {TT1 TT2 : tele} (P : TT1 -t> PROP)
                    (Q : TT1 -t> TT2 -t> PROP)
    : M (tele_arg (tele_append TT1 (tele_bind (fun _ : TT1 => TT2)))) :=
    {| M._wp K := ∃.. x : TT1, tele_app P x ∗
                                 (∀.. y : TT2, tele_app (tele_app Q x) y -∗ ▷?step K (tele_arg_append_simple x y)) |}%I.
  Next Obligation.
    simpl; intros.
    iIntros "K".
    rewrite !bi_texist_exist.
    iIntros "X"; iDestruct "X" as (x) "X"; iExists x.
    iDestruct "X" as "[$ X]".
    rewrite !bi_tforall_forall.
    iIntros (y) "Y". iSpecialize ("X" with "Y").
    destruct step; simpl; [ iNext | ]; iApply "K"; auto.
  Qed.

  #[program]
  Definition read (step : bool) {TT1 : tele} (P : TT1 -t> PROP)
    : M TT1 :=
    {| _wp K := ∃.. x : TT1, (tele_app P x ∗ True) ∧ ▷?step K x |}%I.
  Next Obligation.
    simpl; intros.
    iIntros "K".
    rewrite !bi_texist_exist.
    iIntros "X"; iDestruct "X" as (x) "X"; iExists x.
    iSplit.
    - iDestruct "X" as "[[$ ?] _]".
    - iDestruct "X" as "[_ X]".
      destruct step; simpl; [ iNext | ]; iApply "K"; eauto.
  Qed.

  #[program]
  Definition ub {t : Type} : M t :=
    {| _wp _ := False%I |}.
  Next Obligation. simpl; intros. iIntros "? []". Qed.
  #[program]
  Definition contra {t : Type} : M t :=
    {| _wp _ := True%I |}.
  Next Obligation.
    simpl; intros; iIntros "? ?".
    iApply bi.pure_intro; [ trivial | ]. iStopProof. reflexivity.
  Qed.
  *)

End M.
#[global] Arguments M _ _ : clear implicits.
End M.

(** TODO: End generic, begin C++-specific *)

(* This is effectively [Writer] *)
Module with_temps.
Section with_temps.
  Import UPoly.
  Context `{PROP : bi}.

  Record Result {t} : Type :=
    { _result : t
    ; _free : FreeTemps.t
    ; _canon : FreeTemps.IsCanonical _free }.
  #[global] Arguments Result _ : clear implicits.

  #[global] Instance Result_MRet : MRet Result :=
    fun _ x =>
      {| _result := x
       ; _free := FreeTemps.id
       ; _canon := _ |}.
  #[global] Instance Result_FMap : FMap Result :=
    fun _ _ f x =>
      {| _result := f x.(_result)
       ; _free := x.(_free)
       ; _canon := x.(_canon) |}.
  #[global] Instance Result_MBind : MBind Result :=
    fun _ _ k c =>
      let r := k c.(_result) in
      {| _result := r.(_result)
       ; _free   := FreeTemps.canon (r.(_free) >*> c.(_free))
       ; _canon  := _ |}.

  (* the monad for expression evaluation *)
  Definition M := Compose.M (M.M PROP) Result.
  Definition mk {T} (m : M.M PROP (Result T)) : M T :=
    Compose.mk m.
  Definition prun {T} (m : M T) : M.M PROP (Result T) :=
    Compose._prun m.

  Definition _wp {T} (m : M T) := M._wp (prun m).

  (* The canonical notion of equivalence on [M _] *)
  #[global] Instance M_equiv [T] : Equiv (M T) :=
    fun a b => Compose._prun a ≡ Compose._prun b.
  #[global] Instance M_equiv_refl {T} : Reflexive (≡@{M T}).
  Proof. do 3 red; intros; reflexivity. Qed.
  #[global] Instance M_equiv_sym {T} : Symmetric (≡@{M T}).
  Proof. do 3 red; intros; symmetry; done. Qed.
  #[global] Instance M_equiv_trans {T} : Transitive (≡@{M T}).
  Proof. do 3 red; intros; etrans; eassumption. Qed.

  (* The canonical notation of approximation/entailment
     Effectively, [a ⊆ b] if all behaviors of [a] are included in [b].
   *)
  #[global] Instance M_subseteq {T} : SubsetEq (M T) :=
    fun a b => Compose._prun a ⊆ Compose._prun b.
  #[global] Instance M_subseteq_refl {T} : Reflexive (⊆@{M T}).
  Proof. do 3 red; intros; reflexivity. Qed.
  #[global] Instance M_subseteq_trans {T} : Transitive (⊆@{M T}).
  Proof. do 3 red; intros; etrans; eassumption. Qed.

  (** The distance metric on [M]. *)
  #[global] Instance M_Dist {T} : Dist (M T) :=
    fun n (a b : M T) => Compose._prun a ≡{n}≡ Compose._prun b.
  #[global] Instance M_Dist_refl {T} : forall n, Reflexive (dist (A:=M T) n).
  Proof. do 3 red; intros; reflexivity. Qed.
  #[global] Instance M_Dist_sym {T} : forall n, Symmetric (dist (A:=M T) n).
  Proof. do 3 red; intros; symmetry; done. Qed.
  #[global] Instance M_Dist_trans {T} : forall n, Transitive (dist (A:=M T) n).
  Proof. do 3 red; intros; etrans; eassumption. Qed.

  #[global]
  Instance M_ret : MRet M := Compose._MRet.
  #[global]
  Instance M_map : FMap M := Compose._FMap.
  #[global]
  Instance M_ap : Ap M := Compose._Ap.
  #[global]
  Instance M_bind : MBind M :=
    fun _ _ k x => Compose.mk (mbind (fun r =>
                                mbind (fun x => mret {| _result := x.(_result)
                                                   ; _free := FreeTemps.canon (x.(_free) >*> r.(_free))
                                                   ; _canon := _ |}) (k r.(_result)).(Compose._prun)) x.(Compose._prun)).

  #[global] Typeclasses Opaque M.

  Definition push_free (f : FreeTemps.t) : M () :=
    Compose.mk $ mret {| _result := ()
                       ; _free := FreeTemps.canon f
                       ; _canon := _ |}.

End with_temps.
#[global] Arguments M _ _ : clear implicits.
End with_temps.

Module Mglobal.
Section Mglobal.
  Import UPoly.

  Variant Result {t} : Type :=
  | Normal (_ : t)
  | Exception (_ : type) (_ : ptr).
  #[global] Arguments Result _ : clear implicits.

  Instance Result_FMap : FMap Result :=
    fun _ _ f x =>
      match x with
      | Normal x => Normal $ f x
      | Exception t p => Exception t p
      end.
  Instance Result_MBind : MBind Result :=
    fun _ _ k x =>
      match x with
      | Normal x => k x
      | Exception t p => Exception t p
      end.

  #[local] Notation PROP := (mpredI).

  (* the monad for global evaluation *)
  Definition M `{Σ : cpp_logic} t := M.M PROP (Result t).

  Context `{Σ : cpp_logic}.

  Definition _wp {T} (m : M T) := M._wp m.

  (* The canonical notion of equivalence on [M _] *)
  #[global] Instance M_equiv [T] : Equiv (M T) :=
    fun a b => a ≡ b.
  #[global] Instance M_equiv_refl {T} : Reflexive (≡@{M T}).
  Proof. do 3 red; intros; reflexivity. Qed.
  #[global] Instance M_equiv_sym {T} : Symmetric (≡@{M T}).
  Proof. do 3 red; intros; symmetry; done. Qed.
  #[global] Instance M_equiv_trans {T} : Transitive (≡@{M T}).
  Proof. do 3 red; intros; etrans; eassumption. Qed.

  (* The canonical notation of approximation/entailment
     Effectively, [a ⊆ b] if all behaviors of [a] are included in [b].
   *)
  #[global] Instance M_subseteq {T} : SubsetEq (M T) :=
    fun a b => a ⊆ b.
  #[global] Instance M_subseteq_refl {T} : Reflexive (⊆@{M T}).
  Proof. do 3 red; intros; reflexivity. Qed.
  #[global] Instance M_subseteq_trans {T} : Transitive (⊆@{M T}).
  Proof. do 3 red; intros; etrans; eassumption. Qed.

  (** The distance metric on [M]. *)
  #[global] Instance M_Dist {T} : Dist (M T) :=
    fun n (a b : M T) => a ≡{n}≡ b.
  #[global] Instance M_Dist_refl {T} : forall n, Reflexive (dist (A:=M T) n).
  Proof. do 3 red; intros; reflexivity. Qed.
  #[global] Instance M_Dist_sym {T} : forall n, Symmetric (dist (A:=M T) n).
  Proof. do 3 red; intros; symmetry; done. Qed.
  #[global] Instance M_Dist_trans {T} : forall n, Transitive (dist (A:=M T) n).
  Proof. do 3 red; intros; etrans; eassumption. Qed.


  #[global]
  Instance M_ret : MRet M :=
    fun _ v => mret (M:=M.M PROP) (Normal v).
  #[global]
  Instance Mlocal_map : FMap M :=
    fun _ _ f => fmap (M:=M.M PROP) (fmap f).
  #[global]
  Instance Mlocal_bind : MBind M :=
    fun _ _ k => mbind (M:=M.M PROP) (fun r =>
                                match r with
                                | Normal x => k x
                                | Exception t p => mret (Exception t p)
                                end).

  #[global] Typeclasses Opaque M.
  #[global] Declare Instance _WpMonad : WpMonad PROP M.

  Definition eval : evaluation_order.t -> forall {T}, list (M T) -> M (list T) := @eval M _ _ demonic.

  Definition throw {T} (ty : type) (p : ptr) : M T :=
    mret (M:=M.M PROP) (Exception ty p).

End Mglobal.
End Mglobal.
Notation Mglobal := Mglobal.M (only parsing).

(** The monad [Mexpr.M] represents the semantic domain of expressions.
    Expressions can terminate in one of the following ways:
    - [Normal v] returning a value
    Statement expressions (a GNU extension) also allows expressions to
    introduce control flow. This adds the following termination types:
    - [Break]
    - [Continue]
    - [ReturnVal p]
    - [ReturnVoid]

 *)
Module Mexpr.
Section Mexpr.
  Import UPoly.

  (* continuations
   * C++ statements can terminate in 4 ways.
   *
   * note(gmm): technically, they can also raise exceptions; however,
   * our current semantics doesn't capture this. if we want to support
   * exceptions, we should be able to add another case,
   * `k_throw : val -> mpred`.
   *)
  Variant Result {T : Type} : Type :=
    | Normal (_ : T)
    | Exception (_ : type) (_ : ptr)
    | Break
    | Continue
    | ReturnVal (_ : ptr)
    | ReturnVoid
  .
  #[global] Arguments Result _ : clear implicits.
  #[global] Instance Result_inh {T} : Inhabited (Result T).
  Proof. constructor; apply Break. Qed.

  #[global] Instance Result_MRet : MRet Result :=
    fun _ => Normal.
  #[global] Instance Result_FMap : FMap Result :=
    fun _ _ f x =>
      match x with
      | Normal x => Normal (f x)
      | Exception ty p => Exception ty p
      | Break => Break
      | Continue => Continue
      | ReturnVal p => ReturnVal p
      | ReturnVoid => ReturnVoid
      end.
  #[global] Instance Result_Ap : Ap Result :=
    fun _ _ f x =>
      match f with
      | Normal f =>
          match x with
          | Normal x => Normal (f x)
          | Exception ty p => Exception ty p
          | Break => Break
          | Continue => Continue
          | ReturnVoid => ReturnVoid
          | ReturnVal p => ReturnVal p
          end
      | Exception ty p => Exception ty p
      | Break => Break
      | Continue => Continue
      | ReturnVal p => ReturnVal p
      | ReturnVoid => ReturnVoid
      end.

  #[local] Notation PROP := mpredI.

  Definition M `{Σ : cpp_logic} := Compose.M (with_temps.M PROP) Result.

  Context `{Σ : cpp_logic}.

  Definition mk {T} (m : M.M PROP (with_temps.Result (Result T))) : M T :=
    Compose.mk (Compose.mk m).
  Definition prun {T} (m : M T) : M.M PROP (with_temps.Result (Result T)) :=
    Compose._prun $ Compose._prun m.

  Definition _wp {T} (m : M T) := M._wp (prun m).

  (* The canonical notion of equivalence on [M _] *)
  #[global] Instance M_equiv [T] : Equiv (M T) :=
    fun a b => Compose._prun a ≡ Compose._prun b.
  #[global] Instance M_equiv_refl {T} : Reflexive (≡@{M T}).
  Proof. do 3 red; intros; reflexivity. Qed.
  #[global] Instance M_equiv_sym {T} : Symmetric (≡@{M T}).
  Proof. do 3 red; intros; symmetry; done. Qed.
  #[global] Instance M_equiv_trans {T} : Transitive (≡@{M T}).
  Proof. do 3 red; intros; etrans; eassumption. Qed.

  (* The canonical notation of approximation/entailment
     Effectively, [a ⊆ b] if all behaviors of [a] are included in [b].
   *)
  #[global] Instance M_subseteq {T} : SubsetEq (M T) :=
    fun a b => Compose._prun a ⊆ Compose._prun b.
  #[global] Instance M_subseteq_refl {T} : Reflexive (⊆@{M T}).
  Proof. do 3 red; intros; reflexivity. Qed.
  #[global] Instance M_subseteq_trans {T} : Transitive (⊆@{M T}).
  Proof. do 3 red; intros; etrans; eassumption. Qed.

  (** The distance metric on [M]. *)
  #[global] Instance M_Dist {T} : Dist (M T) :=
    fun n (a b : M T) => Compose._prun a ≡{n}≡ Compose._prun b.
  #[global] Instance M_Dist_refl {T} : forall n, Reflexive (dist (A:=M T) n).
  Proof. do 3 red; intros; reflexivity. Qed.
  #[global] Instance M_Dist_sym {T} : forall n, Symmetric (dist (A:=M T) n).
  Proof. do 3 red; intros; symmetry; done. Qed.
  #[global] Instance M_Dist_trans {T} : forall n, Transitive (dist (A:=M T) n).
  Proof. do 3 red; intros; etrans; eassumption. Qed.

  #[global] Instance _MRet : MRet M := Compose._MRet.
  #[global] Instance _FMap : FMap M := Compose._FMap.
  #[global] Instance _Ap : Ap M := Compose._Ap.
  #[global] Instance _MBind : MBind M :=
    fun _ _ k m => Compose.mk $ mbind (M:=with_temps.M PROP)
                  (fun r =>
                     match r with
                     | Normal v => (k v).(Compose._prun)
                     | Exception ty p => mret (Exception ty p)
                     | Break => mret Break
                     | Continue => mret Continue
                     | ReturnVoid => mret ReturnVoid
                     | ReturnVal p => mret $ ReturnVal p
                     end) (Compose._prun m).

  #[global] Declare Instance _WpMonad : WpMonad PROP M.

  Definition eval : evaluation_order.t -> forall {T}, list (M T) -> M (list T) := @eval M _ _ demonic.

  Definition push_free (f : FreeTemps.t) : M () :=
    Compose.mk $ Normal <$> with_temps.push_free f.

  Definition continue {T} : M T :=
    mk (mret (M:=M.M PROP) (mret Continue)).
  Definition break {T} : M T :=
    mk (mret (M:=M.M PROP) (mret Break)).
  Definition return_void {T} : M T :=
    mk (mret (M:=M.M PROP) (mret ReturnVoid)).
  Definition return_val {T} (p : ptr) : M T :=
    mk (mret (M:=M.M PROP) (mret (ReturnVal p))).
  Definition throw {T} (ty : type) (p : ptr) : M T :=
    mk (mret (M:=M.M PROP) (mret (Exception ty p))).

  Definition handle {T} (m : Mexpr.M T) : with_temps.M mpredI (Result T) :=
    Compose._prun m.

End Mexpr.
End Mexpr.
Notation Mlocal := Mexpr.M (only parsing).

Section with_prop.
  Import UPoly.
  Context `{Σ : cpp_logic}.
  #[local] Notation PROP := mpredI (only parsing).

  Definition to_local {T} (m : Mglobal.M T) : Mexpr.M T :=
    Compose.mk (with_temps.mk ((fun r => mret (M:=with_temps.Result)
                                        match r with
                                        | Mglobal.Normal v => Mexpr.Normal v
                                        | Mglobal.Exception ty p => Mexpr.Exception ty p
                                        end) <$> m)).

End with_prop.

(***
(** V1 *)

Module M.
Section M.
  Context {PROP : bi}.

  Record M {t : Type} := mk
  { _wp : (t -> PROP) -> PROP
  ; _ok : forall K1 K2, (Forall x, K1 x -* K2 x) |-- _wp K1 -* _wp K2 }.
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
      forall K1 K2, (forall x, K1 x ⊣⊢ K2 x) -> a K1 ⊣⊢ b K2.
  #[global] Instance M_equiv_refl {T} : Reflexive (≡@{M T}).
  Proof.
    repeat red. intros.
    split'.
    { iApply _ok; iIntros (?). rewrite H; eauto. }
    { iApply _ok; iIntros (?). rewrite H; eauto. }
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
      forall K1 K2, (forall x, K1 x ⊢ K2 x) -> a K1 ⊢ b K2.
  #[global] Instance M_subseteq_refl {T} : Reflexive (⊆@{M T}).
  Proof. repeat intro. iApply _ok; iIntros (?); iApply H. Qed.
  #[global] Instance M_subseteq_trans {T} : Transitive (⊆@{M T}).
  Proof.
    repeat intro. etrans.
    { iApply H. reflexivity. }
    { iApply H0. apply H1. }
  Qed.

  (** The distance metric on [M].
   *)
  #[global] Instance M_Dist {T} : Dist (M T) :=
    fun n (a b : M T) =>
      forall K1 K2, (forall x, K1 x ≡{n}≡ K2 x) -> a K1 ≡{n}≡ b K2.

  #[global,program]
  Instance M_ret : MRet M :=
    fun _ v => {| _wp K := K v |}.
  Next Obligation.
    intros; simpl. iIntros "X"; iApply "X".
  Qed.
  #[global,program]
  Instance Mlocal_map : FMap M :=
    fun _ _ f m => {| _wp K := m.(_wp) (fun t => K (f t)) |}.
  Next Obligation.
    intros; simpl.
    iIntros "X"; iApply _ok.
    iIntros (?); iApply "X".
  Qed.
  #[global,program]
  Instance Mlocal_bind : MBind M :=
    fun _ _ k c =>
      {| _wp K := c (fun v => (k v).(_wp) K) |}.
  Next Obligation.
    simpl; intros. iIntros "K"; iApply _ok.
    iIntros (?). iApply _ok. done.
  Qed.

End M.
End M.


Module Mlocal.
Section Mlocal.
  Context `{PROP : bi}.

  Record Result {t} : Type :=
    { _result : t
    ; _free : FreeTemps.t
    ; _canon : FreeTemps.IsCanonical _free }.
  Arguments Result _ : clear implicits.

  Instance Result_FMap : FMap Result :=
    fun _ _ f x =>
      {| _result := f x.(_result)
       ; _free := x.(_free)
       ; _canon := x.(_canon) |}.
  Instance Result_MBind : MBind Result :=
    fun _ _ k c =>
      let r := k c.(_result) in
      {| _result := r.(_result)
       ; _free   := FreeTemps.canon (r.(_free) >*> c.(_free))
       ; _canon  := _ |}.

  (* the monad for expression evaluation *)
  Definition M t := M.M (PROP:=PROP) (Result t).

  #[global]
  Instance M_ret : MRet M :=
    fun _ v => mret {| _result := v ; _free := FreeTemps.id ; _canon := _ |}.
  #[global]
  Instance Mlocal_map : FMap M :=
    fun _ _ f => fmap (M:=M.M) (fmap f).
  #[global]
  Instance Mlocal_bind : MBind M :=
    fun _ _ k => mbind (M:=M.M) (fun r =>
                                mbind (M:=M.M) (fun x => mret (M:=M.M) {| _result := x.(_result)
                                                                     ; _free := FreeTemps.canon (x.(_free) >*> r.(_free))
                                                                     ; _canon := _ |}) (k r.(_result))).
  (** ^^ TODO: this can be simplified *)

End Mlocal.
End Mlocal.

(** [Mglobal] -- normal + exceptions
      = M ((type * ptr) + t)
    [Mexpr] -- (normal + exceptions + break + return + continue) * freetemps
      = M (Result (ReturnType t))
 *)

(** V2 *)

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
  Record Mlocal {t : Type} := mk
    { _wp : (t -> forall free : FreeTemps.t, FreeTemps.IsCanonical free -> mpred) -> mpred
    ; _ok : forall K1 K2, (Forall x free pf, K1 x free pf -* K2 x free pf) |-- _wp K1 -* _wp K2 }.
  #[global] Arguments Mlocal _ : clear implicits.
  #[local] Coercion _wp : Mlocal >-> Funclass.

  (* The global monad used for functions.
     NOTE: this actually does not have [FreeTemps.t]
   *)
  Record Mglobal {t : Type} := mk
    { _wp : (t -> mpred) -> mpred
    ; _ok : forall K1 K2, (Forall x, K1 x -* K2 x) |-- _wp K1 -* _wp K2 }.
  #[global] Arguments Mlocal _ : clear implicits.
  #[local] Coercion _wp : M >-> Funclass.

  Definition Mglobal T := M T.

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
   *)
  #[global] Instance M_Dist {T} : Dist (M T) :=
    fun n (a b : M T) =>
      forall K1 K2, (forall x y z, K1 x y z ≡{n}≡ K2 x y z) -> a K1 ≡{n}≡ b K2.

  (** ** Monad Operators *)

  #[global] Instance ReturnType_fmap : FMap ReturnType :=
    fun _ _ f x => match x with
                | Normal x => Normal (f x)
                | Break => Break
                | Continue => Continue
                | ReturnVoid => ReturnVoid
                | ReturnVal p => ReturnVal p
                end.

  #[global,program]
  Instance Mlocal_ret : UPoly.MRet Mlocal :=
    fun _ v => {| _wp K := K (Normal v) FreeTemps.id _ |}.
  Next Obligation.
    intros; simpl. iIntros "X"; iApply "X".
  Qed.
  #[global,program]
  Instance Mlocal_map : UPoly.FMap Mlocal :=
    fun _ _ f m => {| _wp K := m.(_wp) (fun t => K (f <$> t)) |}.
  Next Obligation.
    intros; simpl.
    iIntros "X"; iApply _ok.
    iIntros (??); iApply "X".
  Qed.
  #[global,program]
  Instance Mlocal_bind : UPoly.MBind Mlocal :=
    fun _ _ k c =>
      {| _wp K := c (fun v f _ => match v with
                               | Normal v => k v (fun v' f' _ => K v' (FreeTemps.canon $ f' >*> f)%free _)
                               | Break => K Break f _
                               | Continue => K Continue f _
                               | ReturnVal p => K (ReturnVal p) f _
                               | ReturnVoid => K ReturnVoid f _
                               end) |}.
  Next Obligation.
    simpl; intros. iIntros "K"; iApply _ok.
    iIntros (???). case_match; try iApply _ok; eauto.
    iIntros (???); iApply "K".
  Qed.

  #[global,program]
  Instance M_ret : UPoly.MRet M :=
    fun _ v => {| _wp K := K v FreeTemps.id _ |}.
  Next Obligation.
    intros; simpl. iIntros "X"; iApply "X".
  Qed.

  #[global,program]
  Instance M_map : UPoly.FMap M :=
    fun _ _ f m => {| _wp K := m.(_wp) (fun t => K (f t)) |}.
  Next Obligation.
    intros; simpl.
    iIntros "X"; iApply _ok.
    iIntros (??); iApply "X".
  Qed.

  (* Question: Should we implement [ap]? *)

  #[global,program]
  Instance M_bind : UPoly.MBind M :=
    fun _ _ k c =>
      {| _wp K := c (fun v f _ => k v (fun v' f' _ => K v' (FreeTemps.canon $ f' >*> f)%free _)) |}.
  Next Obligation.
    simpl; intros. iIntros "K"; iApply _ok.
    iIntros (???). iApply _ok. iIntros (???); iApply "K".
  Qed.
  Notation "'letWP*' v := e 'in' k" := (UPoly.mbind e (fun v => k)) (at level 0, v binder, k at level 200).

  (**  These operations actually form a monad *)
  Lemma mret_mbind {T U} v (k : T -> M U) : mbind k (mret v) ≡ k v.
  Proof.
    red. rewrite /M_equiv/M_bind/M_ret/=. red. simpl; intros.
    split'.
    { iApply _ok; iIntros (???) "?"; iStopProof.
      rewrite H; apply K_entails.
      by rewrite FreeTemps.canon_equiv FreeTemps.seq_id_unitR. }
    { iApply _ok; iIntros (???) "?"; iStopProof.
      rewrite H; apply K_entails.
      by rewrite FreeTemps.canon_equiv FreeTemps.seq_id_unitR. }
  Qed.

  Lemma mbind_mret {T} (m : M T) : mbind mret m ≡ m.
  Proof.
    red; rewrite /M_equiv/M_bind/M_ret; red; simpl; intros.
    split'.
    { iApply _ok; iIntros (???) "?"; iStopProof.
      rewrite H; apply K_entails. rewrite FreeTemps.canon_equiv FreeTemps.seq_left_id; eauto. }
    { iApply _ok; iIntros (???) "?"; iStopProof.
      rewrite H; apply K_entails; rewrite FreeTemps.canon_equiv FreeTemps.seq_left_id; eauto. }
  Qed.

  Lemma mbind_mbind {T U V} (m : M T) (k1 : T -> M U) (k2 : U -> M V) :
    mbind (fun x => mbind k2 (k1 x)) m ≡ mbind k2 (mbind k1 m).
  Proof.
    red; rewrite /M_equiv/M_bind; red; simpl; intros.
    split';
      iApply _ok; iIntros (???); iApply _ok; iIntros (???); iApply _ok; iIntros (???);
      rewrite H; eauto; iIntros; iStopProof; apply K_entails.
    all: rewrite !FreeTemps.canon_equiv FreeTemps.seq_assoc; eauto.
  Qed.

  (** Conversions between the monads *)
  Definition M2local {T} (m : Mglobal T) : Mlocal T :=
    Normal <$> m.

  (** The interpreter for the monad.

      TODO: confirm whether this is necessary, or make it a notation. This is essentially the compatibility constant
            for [_wp], but some of the typeclass search didn't seem to work correctly with the constant

      TODO: it would be nice to hide the canonicity proof because it is an implementation detail of the monad, but
            that break [by_WP].
   *)
  Definition WP {T} (m : M T) := _wp m.
(*
  Definition WP {T} (m : M T) (Q : T -> FreeTemps.t -> mpred) : mpred :=
    m (fun x f _ => Q x f).
 *)

  Definition Knormal {T U} (k : T -> M U) (Q : U -> forall f, FreeTemps.IsCanonical f -> mpred) : T -> forall f, FreeTemps.IsCanonical f -> mpred :=
    fun t free _ => k t (fun u free' _ => Q u (FreeTemps.canon (free' >*> free)) _).

  Lemma WP_Mbind {T U} (m : M T) (k : T -> M U) Q :
    WP m (Knormal k Q) |-- WP (mbind k m) Q.
  Proof.
    rewrite /M_bind/WP/Knormal/=.
    iApply _ok; iIntros (???). eauto.
  Qed.

  Lemma WP_ret {T} (v : T) Q :
    Q v FreeTemps.id _ |-- WP (mret v) Q.
  Proof. by rewrite /WP/M_ret/=. Qed.

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
    P -* Q () FreeTemps.id _ |-- WP (Mproduce P) Q.
  Proof. reflexivity. Qed.
  Lemma WP_consume P Q :
    P ** Q () FreeTemps.id _ |-- WP (Mconsume P) Q.
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
  Definition Munsupported {t : Type} {ERR : Type} (err : ERR) : M t :=
    {| _wp _ := ERROR err |}.
  Next Obligation. simpl; intros. rewrite ERROR_False. iIntros "? []". Qed.

  #[program]
  Definition Mpush_free (f : FreeTemps.t) : Mlocal () :=
    {| _wp K := K (Normal ()) (FreeTemps.canon f) _ |}.
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

  Definition Mas {T U} (inj : T -> U) (v : U) : M T :=
    letM* p := Mangelic _ in
    letM* '() := Mrequire (v = inj p) in
    mret p.

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

  Definition FrameI {T} (a b : M T) : mpred :=
    Forall Q Q', (Forall x y z, Q x y z -* Q' x y z) -* a Q -* b Q'.
  Definition FrameWithI {T} (P : T -> mpred) (a b : M T) : mpred :=
    Forall Q Q', (Forall x y z, P x -* Q x y z -* Q' x y z) -* a Q -* b Q'.

  (*
  Definition Mimpl {T} (a b : M T) : mpred :=
    ∀ Q, a Q -* b Q.

  Lemma WP_impl {T} (a b : M T) Q : Mimpl a b |-- WP a Q -* WP b Q.
  Proof. rewrite /Mimpl. iIntros "X". iApply "X". Qed.
  *)

  Lemma Mmap_frame_strong {T U} c (f : T -> U) :
    FrameI c c
    |-- Forall Q Q', (Forall x y pf, Q (f x) y pf -* Q' (f x) y pf) -* _wp (f <$> c) Q -* _wp (f <$> c) Q'.
  Proof.
    rewrite /FrameI/M_map/fmap/=; iIntros "A" (??) "B".
    iApply "A". iIntros (??); iApply "B".
  Qed.

  Lemma Mmap_frame {T U} c1 c2 (f : T -> U) :
    FrameI c1 c2 |-- FrameI (f <$> c1) (f <$> c2).
  Proof.
    rewrite /FrameI/M_map/fmap/=; iIntros "A" (??) "B".
    iApply "A". iIntros (??); iApply "B".
  Qed.

  Lemma Mframe_refl {T} (m : M T) : proper_Frame m.
  Proof.
    rewrite /Frame. iIntros (??) "X".
    iApply _ok. eauto.
  Qed.

  Lemma Mbind_frame {T U} c1 c2 (k1 k2 : T -> M U) :
    FrameI c1 c2 |-- (Forall x, FrameI (k1 x) (k2 x)) -* FrameI (mbind k1 c1) (mbind k2 c2).
  Proof.
    rewrite /FrameI/M_bind/mbind/=; iIntros "A B" (??) "C".
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
    Mboth (letM* v1 := wp1 in
           letM* v2 := wp2 in
           mret (v1,v2))
          (letM* v2 := wp2 in
           letM* v1 := wp1 in
           mret (v1,v2)).

  Lemma nd_seq_frame {T U} wp1 wp2 :
    FrameI wp1 wp1 |-- FrameI wp2 wp2 -* FrameI (@nd_seq T U wp1 wp2) (nd_seq wp1 wp2).
  Proof.
    iIntros "A B" (??) "C D".
    iSplit; [ iDestruct "D" as "[D _]" | iDestruct "D" as "[_ D]" ]; iRevert "D".
    { rewrite /FrameI/mbind/=. iApply "A". iIntros (???). iApply "B"; iIntros (???). iApply "C". }
    { rewrite /mbind/=. iApply "B". iIntros (???). iApply "A"; iIntros (???). iApply "C". }
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
      |-- ([∗list] m ∈ ls, FrameI m m) -*
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
      ([∗list] m ∈ ls, FrameI m m)
      |-- FrameI (nd_seqs' n ls) (nd_seqs' n ls).
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
      ([∗list] m ∈ ms, FrameI m m) |-- FrameI (nd_seqs ms) (nd_seqs ms).
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
    letM* v := wp1 in
    (fun x => (v,x)) <$> wp2.

  Lemma Mseq_frame {T U} wp1 wp2 :
    FrameI wp1 wp1 |-- FrameI wp2 wp2 -* FrameI (@Mseq T U wp1 wp2) (Mseq wp1 wp2).
  Proof.
    iIntros "A B" (??) "C".
    rewrite /Mseq.
    iApply (Mbind_frame with "A [B]"); last iAssumption.
    iIntros (???) "X". iApply (Mmap_frame with "B"). done.
  Qed.

  (** [seqs es] is sequential evaluation of [es] *)
  Fixpoint seqs {T} (es : list (M T)) : M (list T) :=
    match es with
    | nil => mret []
    | e :: es => (fun '(a,b) => a :: b) <$> (Mseq e (seqs es))
    end.

  Lemma seqs_frame_strong {T} : forall (ls : list (M T)) Q Q',
      ([∗list] m ∈ ls, FrameI m m)%I
      |-- (Forall x y pf, [| length x = length ls |] -* Q x y pf -* Q' x y pf) -*
          (seqs ls Q) -* (seqs ls Q').
  Proof.
    induction ls; simpl; intros.
    - iIntros "_ X"; iApply "X"; eauto.
    - iIntros "[A AS] K".
      rewrite /M_bind. iApply "A".
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
    FrameI wp1 wp1 |-- FrameI wp2 wp2 -* FrameI (@Mpar T U wp1 wp2) (Mpar wp1 wp2).
  Proof.
    iIntros "A B" (??) "C D".
    rewrite /Mpar/FrameI.
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
    | nil => mret nil
    | f :: fs => (fun '(v, vs) => v :: vs) <$> Mpar f (Mpars fs)
    end.

  Lemma Mpars_frame_strong {T} : forall (ls : list (M T)) Q Q',
      |-- (Forall x y pf, [| length x = length ls |] -* Q x y pf -* Q' x y pf) -*
          (Mpars ls Q) -* (Mpars ls Q').
  Proof.
    induction ls; simpl; intros.
    - iIntros "X"; iApply "X"; eauto.
    - iIntros "K".
      rewrite /M_map.
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
    | evaluation_order.rl => (fun '(a,b) => (b,a)) <$> Mseq e2 e1
    end.

  (** [evals eo es] evaluates [es] according to the evaluation scheme [eo] *)
  Definition eval (eo : evaluation_order.t) {T} (es : list (M T)) : M (list T) :=
    match eo with
    | evaluation_order.nd => nd_seqs es
    | evaluation_order.l_nd =>
        match es with
        | e :: es => letM* v := e in (fun vs => v :: vs) <$> (nd_seqs es)
        | [] => mret []
        end
    | evaluation_order.rl => (@rev _) <$> (seqs (rev es))
    end.

  Lemma eval_frame_strong {T} oe : forall (ls : list (M T)) Q Q',
      ([∗list] m ∈ ls, FrameI m m)%I
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

  (** TODO: integrate this *)
  #[global]
  Instance equiv_subseteq_subrelation {T} : @subrelation (M T) (≡) (⊆).
  Proof.
    red. intros. repeat intro.
    do 2 red in H. rewrite H. iApply _ok. 2: reflexivity.
    iIntros (???). iApply H0.
  Qed.

  #[global]
  Instance equiv_subseteq_proper {T} : Proper ((⊆) --> (⊆) ==> Basics.impl) (⊆@{M T}).
  Proof. repeat intro. red in H. Admitted.
  #[global]
  Instance equiv_subseteq_proper_equiv {T} : Proper ((≡) ==> (≡) ==> Basics.impl) (⊆@{M T}).
  Proof. repeat intro. red in H. Admitted.

  #[global]
  Instance equiv_RR {T} : RewriteRelation (≡@{M T}) := {}.
  #[global]
  Instance subseteq_RR {T} : RewriteRelation (⊆@{M T}) := {}.

  #[global] Instance WP_proper {T}
    : Proper ((≡) ==> eq ==> flip (⊢)) (WP (T:=T)).
  Proof.
    repeat intro; simpl; subst. rewrite /WP. red in H. red in H.
    rewrite H. reflexivity.
    simpl; intros. reflexivity.
  Qed.

  #[global]
  Instance Mbind_proper {T U}
    : Proper (pointwise_relation _ (⊆@{M U}) ==> (⊆@{M T}) ==> (⊆)) mbind.
  Proof.
    repeat intro.
    rewrite /M_bind/=. apply H0. intros. apply H. intros. apply H1.
  Qed.
  #[global]
  Instance Mbind_subseteq_proper {T U}
    : Proper (pointwise_relation _ (flip (⊆@{M U})) ==> flip (⊆@{M T}) ==> flip (⊆)) mbind.
  Proof.
    repeat intro.
    rewrite /M_bind/=. apply H0. intros. apply H. intros. apply H1.
  Qed.


  #[global] Instance WP_subseteq_proper {T}
    : Proper ((⊆) ==> eq ==> (⊢)) (WP (T:=T)).
  Proof.
    repeat intro. subst. rewrite /WP. apply H. eauto.
  Qed.
  #[global] Instance WP_subseteq_proper' {T}
    : Proper (flip (⊆) ==> eq ==> flip (⊢)) (WP (T:=T)).
  Proof.
    repeat intro. subst. rewrite /WP. apply H. eauto.
  Qed.

  Definition by_WP {T} (m1 m2 : M T) :
    (forall k, WP m1 k |-- WP m2 k) ->
    m1 ⊆ m2.
  Proof.
    rewrite /WP. repeat intro.
    rewrite H. iApply _ok. iIntros (???). iApply H0.
  Qed.

  #[global] Typeclasses Opaque WP M_bind M_ret M_map.

  #[local] Opaque FreeTemps.canon.
  Instance: forall {T} k K P, FromWand (WP (mbind k (Mproduce P)) K) P (WP (T:=T) (k ()) K).
  Proof.
    intros. red.
    rewrite /M_bind/WP/=.
    f_equiv.
    iApply _ok. iIntros (???).
    iApply K_entails.
    by rewrite FreeTemps.canon_equiv right_id.
  Qed.

  Instance: forall {T} K k P, IntoWand false false (WP (mbind k (Mproduce P)) K) P (WP (T:=T) (k ()) K).
  Proof.
    intros. red.
    rewrite /M_bind/WP/=.
    f_equiv.
    iApply _ok. iIntros (???).
    iApply K_entails.
    by rewrite FreeTemps.canon_equiv right_id.
  Qed.

  Lemma WP_Mbind_Mfupd {T} E1 E2 k K :
    WP (mbind k (Mfupd E1 E2)) K -|- |={E1,E2}=> WP (T:=T) (k ()) K.
  Proof.
    rewrite /WP/Mfupd/=. f_equiv.
    iSplit;
      by iApply _ok; iIntros (???); iApply K_entails; rewrite FreeTemps.canon_equiv right_id.
  Qed.
  Lemma WP_mret {T} (v : T) K :
    WP (mret v) K -|- K v FreeTemps.id _.
  Proof. rewrite /WP/M_ret/=. done. Qed.
  Lemma WP_Mbind_mret {T U} (v : T) (k : T -> M U) K :
    WP (mbind k (mret v)) K -|- WP (k v) K.
  Proof.
    rewrite /WP/M_bind/M_ret/=.
    iSplit;
      by iApply _ok; iIntros (???); iApply K_entails; rewrite FreeTemps.canon_equiv right_id.
  Qed.
  Lemma WP_Mbind_Mproduce {T} P k K :
    WP (mbind k (Mproduce P)) K -|- P -* WP (T:=T) (k ()) K.
  Proof.
    rewrite /WP/Mproduce/=. f_equiv.
    iSplit;
      by iApply _ok; iIntros (???); iApply K_entails; rewrite FreeTemps.canon_equiv right_id.
  Qed.

  (*
  Instance Mbind_params : Params (@bind) 4 := {}.
  Instance bi_entails_params : Params (@bi_entails) 1 := {}.
  *)

  Definition Kfree {T} (free : FreeTemps.t) (K : T -> forall free, FreeTemps.IsCanonical free -> mpred) : T -> forall free, FreeTemps.IsCanonical free -> mpred :=
    fun x f _ => K x (FreeTemps.canon (f >*> free)) _.
  Lemma WP_Mbind_frame {T U} (m : M T) (k1 k2 : T -> M U) K1 K2 :
    (Forall x free, WP (k1 x) (Kfree free K1) -* WP (k2 x) (Kfree free K2))
      |-- WP (mbind k1 m) K1 -* WP (mbind k2 m) K2.
  Proof.
    rewrite /WP/M_bind/=.
    iIntros "k"; iApply _ok; iIntros (???). iApply "k".
  Qed.
  Hint Opaque Kfree : typeclass_instances.
  Lemma WP_Mbind_Mbind {T U V} m1 (m2 : T -> M U) (m3 : U -> M V) K :
    WP (mbind m3 (mbind m2 m1)) K -|- WP (mbind (fun x => mbind m3 (m2 x)) m1) K.
  Proof.
    rewrite /M_bind/WP/=.
    iSplit;
      iApply _ok; iIntros (???); iApply _ok; iIntros (???); iApply _ok; iIntros (???);
      iApply K_entails; by rewrite !FreeTemps.canon_equiv assoc.
  Qed.

  Fixpoint tuple (ts : list Type) : Type :=
    match ts return Type with
    | nil => unit
    | t :: ts => t * tuple ts
    end.

  (* TODO: this is the heterogeneous extension of [eval] *)
  Parameter heval : forall (eo : evaluation_order.t) {ts} (x : tuple (M <$> ts)), M (tuple ts).
End with_cpp.

*)

Notation "'letWP*' v := e 'in' k" := (UPoly.mbind (fun v => k) e) (at level 0, v binder, k at level 200, only parsing).
