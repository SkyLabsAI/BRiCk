(*
 * Copyright (c) 2020-22 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(** Theory of representation predicates [Rep].
For an introduction see
[fmdeps/cpp2v-core/theories/noimport/doc/cpp/howto_sequential.v]. *)

Require Import bluerock.iris.extra.proofmode.proofmode.
Require Import bluerock.iris.extra.bi.fractional.

Require Import bluerock.iris.extra.bi.prelude.
Require Import bluerock.iris.extra.bi.only_provable.
Require Import bluerock.iris.extra.bi.observe.
Require Import bluerock.iris.extra.bi.laterable.
Require Export bluerock.iris.extra.bi.monpred.
(** ^^ Delicate; export canonical structure (CS) for [monPred].
Export order can affect CS inference. *)

Require Import bluerock.lang.cpp.semantics.values.
Require Import bluerock.lang.cpp.logic.mpred.
Require Import bluerock.lang.cpp.bi.cfractional.
Require Export bluerock.lang.cpp.logic.rep_defs.
(** ^^ Delicate; export canonical structure (CS) for [Rep].
Export order can affect CS inference. *)

Import ChargeNotation.
Implicit Types (σ resolve : genv) (p : ptr) (o : offset).

Section with_cpp.
  Context `{!cpp_logic thread_info Σ}.

  Implicit Type (R : Rep).

  (* Keeps proofs simple with recent Iris. *)
  #[local] Existing Instance as_fractional_fractional.
  #[local] Hint Mode AsFractional - - - - : typeclass_instances.

  #[global] Instance as_Rep_ne n :
    Proper (pointwise_relation _ (dist n) ==> dist n) as_Rep.
  Proof. intros R1 R2 HR. constructor=>p. apply HR. Qed.
  #[global] Instance as_Rep_proper :
    Proper (pointwise_relation _ (≡) ==> (≡)) as_Rep.
  Proof. intros R1 R2 HR. constructor=>p. apply HR. Qed.

  #[global] Instance as_Rep_mono :
    Proper (pointwise_relation _ (⊢) ==> (⊢)) as_Rep.
  Proof. by constructor. Qed.
  #[global] Instance as_Rep_flip_mono :
    Proper (pointwise_relation _ (flip (⊢)) ==> flip (⊢)) as_Rep.
  Proof. by constructor. Qed.

  #[global] Instance as_Rep_persistent P :
    (∀ p, Persistent (P p)) → Persistent (as_Rep P).
  Proof.
    intros HP. constructor=>p. by rewrite monPred_at_persistently -HP.
  Qed.
  #[global] Instance as_Rep_affine P :
    (∀ p, Affine (P p)) → Affine (as_Rep P) := _.
  #[global] Instance as_Rep_timeless P :
    (∀ p, Timeless (P p)) → Timeless (as_Rep P).
  Proof.
    intros HP. constructor=>p.
    by rewrite monPred_at_later monPred_at_except_0 HP.
  Qed.
  #[global] Instance as_Rep_fractional P :
    (∀ p, Fractional (λ q, P q p)) → Fractional (λ q, as_Rep (P q)).
  Proof.
    intros HP q1 q2. constructor=>p. by rewrite monPred_at_sep /= HP.
  Qed.
  #[global] Instance as_Rep_as_fractional P q :
    (∀ p, AsFractional (P q p) (λ q, P q p) q) →
    AsFractional (as_Rep (P q)) (λ q, as_Rep (P q)) q.
  Proof. constructor. done. apply _. Qed.

  #[global] Instance as_Rep_cfractional {P : cQp.t -> ptr -> mpred} :
    CFractional1 P ->
    CFractional (fun q => as_Rep (P q)).
  Proof. intros HP q1 q2. constructor =>p. by rewrite monPred_at_sep /= HP. Qed.
  #[global] Instance as_Rep_as_cfractional (P : cQp.t -> ptr -> mpred) q :
    AsCFractional1 P ->
    AsCFractional (as_Rep (P q)) (λ q, as_Rep (P q)) q.
  Proof. solve_as_cfrac. Qed.

  #[global] Instance as_Rep_laterable (R : ptr -> mpred) :
    (∀ p, Laterable (R p)) -> Laterable (as_Rep R).
  Proof.
    rewrite/Laterable=>HR. constructor=>p/=.
    iIntros "R". iDestruct (HR with "R") as (R') "[R #close]".
    rewrite monPred_at_exist. iExists (pureR R').
    rewrite monPred_at_sep monPred_at_later/=. iFrame "R".
    rewrite monPred_at_intuitionistically monPred_at_wand.
    iIntros "!>" (p' ->%ptr_rel_elim).
    by rewrite monPred_at_later monPred_at_except_0/=.
  Qed.

  Lemma as_Rep_embed P : as_Rep (λ _, P) -|- embed P.
  Proof. constructor=>p /=. by rewrite monPred_at_embed. Qed.

  Lemma as_Rep_emp : as_Rep (λ p, emp) -|- emp.
  Proof. constructor => p. by rewrite monPred_at_emp. Qed.
  Lemma as_Rep_sep P Q : as_Rep (λ p, P p ** Q p) -|- as_Rep P ** as_Rep Q.
  Proof. constructor=>p. by rewrite monPred_at_sep. Qed.

  (* NOTE this is not exposed as a hint *)
  Lemma as_Rep_observe P Q (o : forall p, Observe (P p) (Q p)) : Observe (as_Rep P) (as_Rep Q).
  Proof. apply: monPred_observe=>p. Qed.
  Lemma as_Rep_observe_2 P Q R (o : forall p, Observe2 (P p) (Q p) (R p)) :
    Observe2 (as_Rep P) (as_Rep Q) (as_Rep R).
  Proof. apply: monPred_observe_2=>p. Qed.

  #[global] Instance as_Rep_only_provable_observe Q (P : ptr → mpred) :
    (∀ p, Observe [| Q |] (P p)) → Observe [| Q |] (as_Rep P).
  Proof.
    intros. apply monPred_observe=>p. by rewrite monPred_at_only_provable.
  Qed.
  #[global] Instance as_Rep_only_provable_observe_2 Q (P1 P2 : ptr → mpred) :
    (∀ p, Observe2 [| Q |] (P1 p) (P2 p)) →
    Observe2 [| Q |] (as_Rep P1) (as_Rep P2).
  Proof.
    intros. apply monPred_observe_2=>p. by rewrite monPred_at_only_provable.
  Qed.

  Lemma as_Rep_obs f P :
    (∀ p, f p |-- f p ** [| P |]) →
    as_Rep f |-- as_Rep f ** [| P |].
  Proof.
    intros. apply observe_elim, as_Rep_only_provable_observe =>p. exact: observe_intro.
  Qed.

  Lemma as_Rep_and P Q : as_Rep (λ p, P p //\\ Q p) -|- as_Rep P //\\ as_Rep Q.
  Proof. constructor=>p. by rewrite monPred_at_and. Qed.

  Lemma as_Rep_or P Q : as_Rep (λ p, P p \\// Q p) -|- as_Rep P \\// as_Rep Q.
  Proof. constructor=>p. by rewrite monPred_at_or. Qed.

  Lemma as_Rep_wand P Q : as_Rep (λ p, P p -* Q p) -|- as_Rep P -* as_Rep Q.
  Proof.
    constructor=>p /=. split'.
    - rewrite monPred_at_wand. iIntros "H" (p' ->%ptr_rel_elim) "/= P".
      iApply ("H" with "P").
    - apply monPred_wand_force.
  Qed.

  Lemma as_Rep_pure (P : Prop) : as_Rep (fun _ => bi_pure P) -|- bi_pure P.
  Proof.
    rewrite /as_Rep.
    split; intro; rewrite /=. by rewrite monPred_at_pure /=.
  Qed.

  Lemma as_Rep_exist {T} (P : T -> ptr -> mpred) :
    as_Rep (λ p, Exists x, P x p) -|- Exists x, as_Rep (P x).
  Proof. constructor=>p /=. by rewrite monPred_at_exist. Qed.

  Lemma as_Rep_forall {T} (P : T -> ptr -> mpred) :
    as_Rep (λ p, Forall x, P x p) -|- Forall x, as_Rep (P x).
  Proof. constructor=>p /=. by rewrite monPred_at_forall. Qed.

  Lemma as_Rep_pers P : as_Rep (λ p, <pers> P p) -|- <pers> (as_Rep P).
  Proof. constructor=>p /=. by rewrite monPred_at_persistently. Qed.

  Lemma as_Rep_bupd P : as_Rep (λ p, |==> P p) -|- |==> as_Rep P.
  Proof. constructor=>p /=. by rewrite monPred_at_bupd. Qed.

  Lemma as_Rep_fupd P E1 E2 : as_Rep (λ p, |={E1,E2}=> P p) -|- |={E1,E2}=> as_Rep P.
  Proof. constructor=>p /=. by rewrite monPred_at_fupd. Qed.

  Lemma as_Rep_intuitionistically P : as_Rep (λ p, □ P p) -|- □ as_Rep P.
  Proof. constructor=>p /=. by rewrite monPred_at_intuitionistically. Qed.

  Lemma as_Rep_intuitionistically_if b P : as_Rep (λ p, □?b P p) -|- □?b as_Rep P.
  Proof. constructor=>p /=. by rewrite monPred_at_intuitionistically_if. Qed.

  Lemma as_Rep_except_0 P : as_Rep (λ p, bi_except_0 (P p)) -|- bi_except_0 (as_Rep P).
  Proof. constructor=>p /=. by rewrite monPred_at_except_0. Qed.

  Lemma as_Rep_affinely P : as_Rep (λ p, <affine> P p) -|- <affine> (as_Rep P).
  Proof. constructor=>p /=. by rewrite monPred_at_affinely. Qed.

  Lemma as_Rep_affinely_if b P : as_Rep (λ p, <affine>?b P p) -|- <affine>?b (as_Rep P).
  Proof. constructor=>p /=. by rewrite monPred_at_affinely_if. Qed.

  Lemma as_Rep_big_sepL {T} (l : list T) (F : nat -> T -> ptr -> mpred) :
    as_Rep (λ p, [∗list] i ↦ x ∈ l, F i x p) -|- [∗list] i ↦ x ∈ l, as_Rep (F i x).
  Proof. constructor=>p /=. by rewrite monPred_at_big_sepL. Qed.

  Lemma as_Rep_later P : as_Rep (λ p, |> P p) -|- |> as_Rep P.
  Proof. constructor=>p /=. by rewrite monPred_at_later. Qed.

  Lemma as_Rep_internal_eq (P Q : mpred) : as_Rep (λ _, P ≡ Q) -|- P ≡ Q.
  Proof. constructor=>p /=. by rewrite monPred_at_internal_eq. Qed.

  Lemma Rep_wand_force (R1 R2 : Rep) p : (R1 -* R2) p -|- R1 p -* R2 p.
  Proof. split'. apply monPred_wand_force. by iIntros "a" (? <-%ptr_rel_elim). Qed.
  Lemma Rep_impl_force (R1 R2 : Rep) p : (R1 -->> R2) p -|- R1 p -->> R2 p.
  Proof. split'. apply monPred_impl_force. by iIntros "a" (? <-%ptr_rel_elim). Qed.
  Lemma Rep_at_wand_iff (P Q : Rep) p :
    (P ∗-∗ Q) p ⊣⊢ (P p ∗-∗ Q p).
  Proof. by rewrite /bi_wand_iff monPred_at_and !Rep_wand_force. Qed.

  Lemma as_Rep_only_provable (P : Prop) : as_Rep (fun _ => [| P |]) -|- [| P |].
  Proof.
    rewrite only_provable.unlock as_Rep_affinely /as_Rep.
    split; intro; rewrite /=. by rewrite !monPred_at_affinely monPred_at_pure /=.
  Qed.

  Import rep_defs.INTERNAL.

  #[global] Instance _offsetR_ne o n : Proper (dist n ==> dist n) (_offsetR o).
  Proof. unfold_at. solve_proper. Qed.
  #[global] Instance _offsetR_proper o : Proper ((≡) ==> (≡)) (_offsetR o).
  Proof. unfold_at. solve_proper. Qed.
  #[global] Instance _offsetR_mono o : Proper ((⊢) ==> (⊢)) (_offsetR o).
  Proof. unfold_at. solve_proper. Qed.
  #[global] Instance _offsetR_flip_mono o : Proper (flip (⊢) ==> flip (⊢)) (_offsetR o).
  Proof. unfold_at. solve_proper. Qed.

  #[global] Instance _offsetR_persistent o (r : Rep) : Persistent r -> Persistent (o |-> r).
  Proof. rewrite _offsetR_eq. apply _. Qed.
  #[global] Instance _offsetR_affine o (r : Rep) : Affine r -> Affine (o |-> r).
  Proof. rewrite _offsetR_eq. apply _. Qed.
  #[global] Instance _offsetR_timeless o (r : Rep) : Timeless r → Timeless (o |-> r).
  Proof. rewrite _offsetR_eq. apply _. Qed.
  #[global] Instance _offsetR_laterable o (r : Rep) : Laterable r → Laterable (o |-> r).
  Proof. rewrite _offsetR_eq. apply _. Qed.

  Lemma _offsetR_offsetR (o1 o2 : offset) R : o1 |-> (o2 |-> R) -|- o1 ,, o2 |-> R.
  Proof.
    rewrite !_offsetR_eq/=.
    f_equiv. by intro; rewrite offset_ptr_dot.
  Qed.

  Lemma _offsetR_emp o : o |-> emp ⊣⊢ emp.
  Proof.
    rewrite _offsetR_eq.
    constructor=> p /=. by rewrite !monPred_at_emp.
  Qed.
  Lemma _offsetR_sep o r1 r2 :
    o |-> (r1 ** r2) -|- o |-> r1 ** o |-> r2.
  Proof.
    rewrite !_offsetR_eq -as_Rep_sep.
    constructor=> p /=. by rewrite monPred_at_sep.
  Qed.
  Lemma _offsetR_pure (o : offset) (P : Prop) :
    o |-> (bi_pure P) -|- bi_pure P.
  Proof.
    rewrite _offsetR_eq/=.
    by constructor=> p/=; rewrite !monPred_at_pure.
  Qed.

  Lemma _offsetR_only_provable (o : offset) (P : Prop) :
    o |-> [| P |] -|- [| P |].
  Proof.
    rewrite _offsetR_eq/=.
    by constructor=> p/=; rewrite !monPred_at_only_provable.
  Qed.

  Lemma _offsetR_and (o : offset) P Q :
    o |-> (P //\\ Q) -|- o |-> P //\\ o |-> Q.
  Proof.
    rewrite !_offsetR_eq/=.
    by constructor=> p/=; rewrite !monPred_at_and.
  Qed.

  Lemma _offsetR_or (o : offset) P Q :
    o |-> (P \\// Q) -|- o |-> P \\// o |-> Q.
  Proof.
    rewrite !_offsetR_eq/=.
    by constructor=> p/=; rewrite !monPred_at_or.
  Qed.

  Lemma _offsetR_wand o (P Q : Rep) :
      o |-> (P -* Q) -|- o |-> P -* o |-> Q.
  Proof.
    rewrite /= !_offsetR_eq /=.
    constructor=> p/=. by rewrite !Rep_wand_force.
  Qed.

  Lemma _offsetR_exists o {T} (P : T -> Rep) :
      o |-> (Exists v : T, P v) -|- Exists v, o |-> (P v).
  Proof.
    rewrite _offsetR_eq /as_Rep/=.
    constructor =>p; rewrite /= !monPred_at_exist.
    f_equiv=>x. by rewrite _offsetR_eq.
  Qed.

  Lemma _offsetR_forall o T (P : T -> Rep) :
    o |-> (Forall x, P x) -|- Forall x, o |-> (P x).
  Proof.
    rewrite _offsetR_eq /as_Rep/=.
    constructor =>p; rewrite /= !monPred_at_forall.
    f_equiv=>x. by rewrite _offsetR_eq.
  Qed.

  Lemma _offsetR_pers o R : o |-> (<pers> R) -|- <pers> o |-> R.
  Proof. rewrite !_offsetR_eq. by constructor=> p/=; rewrite !monPred_at_persistently. Qed.

  Lemma _offsetR_bupd o R : o |-> (|==> R) -|- |==> o |-> R.
  Proof. by rewrite !_offsetR_eq /as_Rep; constructor => p /=; rewrite !monPred_at_bupd. Qed.

  Lemma _offsetR_fupd o R E1 E2 : o |-> (|={E1,E2}=> R) -|- |={E1,E2}=> o |-> R.
  Proof. by rewrite !_offsetR_eq /as_Rep; constructor => p /=; rewrite !monPred_at_fupd. Qed.

  Lemma _offsetR_intuitionistically o (R : Rep) : o |-> (□ R) ⊣⊢ □ (o |-> R).
  Proof. by rewrite !_offsetR_eq; constructor => p /=; rewrite !monPred_at_intuitionistically. Qed.

  Lemma _offsetR_intuitionistically_if o b R : o |-> (□?b R) -|- □?b (o |-> R).
  Proof. by destruct b => //=; rewrite /= _offsetR_intuitionistically. Qed.

  Lemma _offsetR_except_0 o R : o |-> (bi_except_0 R) -|- bi_except_0 (o |-> R).
  Proof. by rewrite !_offsetR_eq; constructor => p /=; rewrite !monPred_at_except_0. Qed.

  Lemma _offsetR_affinely (o : offset) R : o |-> (<affine> R) -|- <affine> o |-> R.
  Proof. by rewrite !_offsetR_eq /as_Rep; constructor => p/=; rewrite !monPred_at_affinely. Qed.

  Lemma _offsetR_affinely_if b (o : offset) R : o |-> (<affine>?b R) -|- <affine>?b o |-> R.
  Proof. by destruct b => //; rewrite _offsetR_affinely. Qed.

  Lemma _offsetR_big_sepL (o : offset) {T} (Rs : list T) : forall F,
    o |-> ([∗list] i ↦ x ∈ Rs , F i x) -|- [∗list] i ↦ x ∈ Rs , o |-> (F i x).
  Proof.
    induction Rs; simpl; intros.
    - by rewrite _offsetR_emp.
    - by rewrite _offsetR_sep IHRs.
  Qed.

  Lemma _offsetR_later o R : o |-> (|> R) -|- |> o |-> R.
  Proof.
    rewrite !_offsetR_eq. constructor=>p/=. by rewrite !monPred_at_later.
  Qed.

  #[global] Instance _offsetR_fractional o (r : Qp → Rep) :
    Fractional r → Fractional (λ q, o |-> r q).
  Proof. by move => H q1 q2; rewrite fractional _offsetR_sep. Qed.
  #[global] Instance _offsetR_as_fractional o (R : Rep) (r : Qp → Rep) q
      `{!AsFractional R r q} :
    AsFractional (o |-> R) (λ q, o |-> r q) q.
  Proof. constructor; [by erewrite as_fractional | apply _]. Qed.

  #[global] Instance _offsetR_cfractional {R : cQp.t -> Rep} o :
    CFractional R ->
    CFractional (fun q => _offsetR o (R q)).
  Proof. intros HR q1 q2. constructor =>p. by rewrite cfractional _offsetR_sep. Qed.
  #[global] Instance _offsetR_as_cfractional o (P : Rep) (R : cQp.t -> Rep) q :
    AsCFractional P R q ->
    AsCFractional (_offsetR o P) (λ q, _offsetR o (R q)) q.
  Proof. constructor. by rewrite -as_cfractional. apply _. Qed.

  #[global] Instance _offsetR_observe {o} {Q R : Rep} :
    Observe Q R ->
    Observe (o |-> Q) (o |-> R).
  Proof. move->. by rewrite /Observe -_offsetR_pers. Qed.

  #[global] Instance _offsetR_observe_2 {o} {Q R1 R2 : Rep} :
    Observe2 Q R1 R2 ->
    Observe2 (o |-> Q) (o |-> R1) (o |-> R2).
  Proof.
    rewrite /Observe2.
    move->. by rewrite /Observe2 _offsetR_wand _offsetR_pers. Qed.

  #[global] Instance _offsetR_observe_only_provable Q o (R : Rep) :
    Observe [| Q |] R → Observe [| Q |] (o |-> R).
  Proof. rewrite -{2}_offsetR_only_provable. apply _. Qed.
  #[global] Instance _offsetR_observe_2_only_provable Q o (R1 R2 : Rep) :
    Observe2 [| Q |] R1 R2 → Observe2 [| Q |] (o |-> R1) (o |-> R2).
  Proof. rewrite -{2}_offsetR_only_provable. apply _. Qed.

  #[global] Instance _offsetR_observe_pure Q o (R : Rep) :
    Observe [! Q !] R → Observe [! Q !] (o |-> R).
  Proof. rewrite -{2}_offsetR_pure. apply _. Qed.
  #[global] Instance _offsetR_observe_2_pure Q o (R1 R2 : Rep) :
    Observe2 [! Q !] R1 R2 → Observe2 [! Q !] (o |-> R1) (o |-> R2).
  Proof. rewrite -{2}_offsetR_pure. apply _. Qed.

  Lemma _offsetR_obs o r P :
    r |-- r ** [| P |] →
    o |-> r |-- o |-> r ** [| P |].
  Proof.
    intros. apply observe_elim, _offsetR_observe_only_provable. exact: observe_intro.
  Qed.
  (* Pulled in from plogic. *)
  Lemma _offsetR_id (R : Rep) :
    _offsetR o_id R -|- R.
  Proof.
    rewrite _offsetR_eq.
    constructor=>/= p.
    by rewrite offset_ptr_id.
  Qed.

  Lemma _offsetR_dot (o1 o2 : offset) (R : Rep) :
    _offsetR o1 (_offsetR o2 R) -|- _offsetR (o1 ,, o2) R.
  Proof.
    constructor =>p/=.
    by rewrite !_offsetR_eq/= offset_ptr_dot.
  Qed.

  #[global] Instance _at_ne p {n} : Proper (dist n ==> dist n) (_at p).
  Proof. unfold_at. solve_proper. Qed.
  #[global] Instance _at_proper {p} : Proper ((≡) ==> (≡)) (_at p).
  Proof. unfold_at. solve_proper. Qed.
  #[global] Instance _at_mono {p} : Proper ((⊢) ==> (⊢)) (_at p).
  Proof. unfold_at. solve_proper. Qed.
  #[global] Instance _at_flip_mono {p} : Proper (flip (⊢) ==> flip (⊢)) (_at p).
  Proof. unfold_at; move => r1 r2 HR/=. solve_proper. Qed.

  #[global] Instance _at_persistent {P base} : Persistent P -> Persistent (_at base P).
  Proof. rewrite _at_eq. apply _. Qed.
  #[global] Instance _at_affine {P base} : Affine P -> Affine (_at base P).
  Proof. rewrite _at_eq. apply _. Qed.
  #[global] Instance _at_timeless {P base} : Timeless P -> Timeless (_at base P).
  Proof. rewrite _at_eq. apply _. Qed.
  #[global] Instance _at_laterable p (P : Rep) : Laterable P → Laterable (p |-> P).
  Proof. rewrite _at_eq. apply _. Qed.

  Lemma _at_as_Rep p (Q : ptr → mpred) : p |-> (as_Rep Q) ⊣⊢ Q p.
  Proof. by rewrite _at_eq. Qed.

  (* Prefer [_at_as_Rep] *)
  Lemma _at_loc p (R : Rep) : p |-> R -|- R p.
  Proof. by rewrite _at_eq. Qed.

  Lemma _at_emp p : p |-> emp -|- emp.
  Proof. by rewrite _at_loc monPred_at_emp. Qed.

  Lemma _at_exists p {T} (P : T -> Rep) :
      p |-> (Exists v : T, P v) -|- Exists v, p |-> (P v).
  Proof. by rewrite _at_loc monPred_at_exist; setoid_rewrite _at_loc. Qed.

  Lemma _at_forall p T (P : T -> Rep) :
    p |-> (Forall x, P x) -|- Forall x, p |-> (P x).
  Proof. by rewrite _at_loc monPred_at_forall; setoid_rewrite _at_loc. Qed.

  Lemma _at_only_provable p P :
      p |-> [| P |] -|- [| P |].
  Proof. by rewrite _at_loc monPred_at_only_provable. Qed.

  Lemma _at_pure p (P : Prop) :
      p |-> [! P !] -|- [! P !].
  Proof. by rewrite _at_loc monPred_at_pure. Qed.

  Lemma _at_sep p (P Q : Rep) :
      p |-> (P ** Q) -|- p |-> P ** p |-> Q.
  Proof. by rewrite !_at_loc monPred_at_sep. Qed.

  Lemma _at_and p (P Q : Rep) :
      p |-> (P //\\ Q) -|- p |-> P //\\ p |-> Q.
  Proof. by rewrite !_at_loc monPred_at_and. Qed.

  Lemma _at_or p (P Q : Rep) :
      p |-> (P \\// Q) -|- p |-> P \\// p |-> Q.
  Proof. by rewrite !_at_loc monPred_at_or. Qed.

  Lemma _at_wand p (P Q : Rep) :
      p |-> (P -* Q) -|- p |-> P -* p |-> Q.
  Proof. by rewrite !_at_loc Rep_wand_force. Qed.

  Lemma _at_impl p R1 R2 : p |-> (R1 -->> R2) -|- p |-> R1 -->> p |-> R2.
  Proof. by rewrite !_at_loc Rep_impl_force. Qed.

  Lemma _at_pers p R : p |-> (<pers> R) -|- <pers> p |-> R.
  Proof. by rewrite !_at_loc monPred_at_persistently. Qed.

  Lemma _at_bupd p R : p |-> (|==> R) -|- |==> p |-> R.
  Proof. by rewrite !_at_loc monPred_at_bupd. Qed.

  Lemma _at_fupd p R E1 E2 : p |-> (|={E1,E2}=> R) -|- |={E1,E2}=> p |-> R.
  Proof. by rewrite !_at_loc monPred_at_fupd. Qed.

  Lemma _at_intuitionistically p (R : Rep) : p |-> □ R ⊣⊢ □ (p |-> R).
  Proof. by rewrite !_at_eq; rewrite monPred_at_intuitionistically. Qed.
  Lemma _at_intuitionistically_if (p : ptr) b R : p |-> (□?b R) -|- □?b (p |-> R).
  Proof. destruct b => //=. by rewrite _at_intuitionistically. Qed.

  Lemma _at_except_0 (p : ptr) R : p |-> bi_except_0 R -|- bi_except_0 (p |-> R).
  Proof. by rewrite !_at_eq monPred_at_except_0. Qed.

  Lemma _at_affinely (p : ptr) R : p |-> <affine> R -|- <affine> p |-> R.
  Proof. by rewrite !_at_eq monPred_at_affinely. Qed.

  Lemma _at_affinely_if b (p : ptr) R : p |-> <affine>?b R -|- <affine>?b p |-> R.
  Proof. by destruct b => //; rewrite !_at_eq monPred_at_affinely. Qed.

  Lemma _at_later p R : p |-> |> R -|- |> p |-> R.
  Proof. by rewrite !_at_eq; rewrite monPred_at_later. Qed.

  Lemma _at_internal_eq p {A : ofe} x y : p |-> (x ≡@{A} y) -|- x ≡ y.
  Proof. by rewrite _at_loc monPred_at_internal_eq. Qed.

  Lemma _at_offsetR p (o : offset) (r : Rep) :
      _at p (_offsetR o r) -|- _at (p ,, o) r.
  Proof. rewrite !_at_loc /flip. by unfold_at. Qed.

  (** Big ops *)
  Lemma _at_big_sepL A p : forall (xs : list A) (Φ : nat -> A -> Rep),
      p |-> ([∗ list] i↦x∈xs, Φ i x) -|- ([∗ list] i↦x∈xs, p |-> (Φ i x)).
  Proof.
    elim => /=.
    - move => ?; by rewrite _at_emp.
    - move => x xs IH ?. by rewrite _at_sep IH.
  Qed.

  Lemma _at_sepSPs p (xs : list Rep) : p |-> ([∗] xs) -|- [∗] map (_at p) xs.
  Proof. by rewrite _at_big_sepL big_sepL_fmap. Qed.

  Lemma _at_big_sepS `{Countable A} p (X : gset A) (Φ : A -> Rep) :
    p |-> ([∗ set] x ∈ X, Φ x) -|- [∗ set] x ∈ X, p |-> Φ x.
  Proof.
    rewrite _at_eq monPred_at_big_sepS.
    by apply big_opS_proper => x _; rewrite _at_eq. (*TODO: AUTO(gs) missing proper instance*)
  Qed.

  Lemma _at_big_sepM `{Countable K} {A} p (m : gmap K A) (Φ : K → A → Rep) :
    p |-> ([∗ map] k↦x ∈ m, Φ k x) -|- [∗ map] k↦x ∈ m, p |-> Φ k x.
  Proof.
    rewrite _at_eq monPred_at_big_sepM.
    by apply big_opM_proper => k x _; rewrite _at_eq.
  Qed.

  Lemma _at_big_sepMS `{Countable A} p (X : gmultiset A) (Φ : A → Rep) :
    p |-> ([∗ mset] x ∈ X, Φ x) -|- [∗ mset] x ∈ X, p |-> Φ x.
  Proof.
    rewrite _at_eq monPred_at_big_sepMS.
    by apply big_opMS_proper => x _; rewrite _at_eq.
  Qed.

  #[global] Instance _at_fractional (r : Qp → Rep) p `{!Fractional r} :
    Fractional (λ q, p |-> (r q)).
  Proof.
    intros q1 q2; by rewrite fractional _at_sep.
  Qed.
  #[global] Instance _at_as_fractional R (r : Qp → Rep) q p
      `{!AsFractional R r q} :
    AsFractional (p |-> R) (λ q, p |-> r q) q.
  Proof. constructor; [by erewrite as_fractional | apply _]. Qed.

  #[global] Instance _at_cfractional {R : cQp.t -> Rep} p :
    CFractional R ->
    CFractional (fun q => _at p (R q)).
  Proof. intros HR q1 q2. by rewrite cfractional _at_sep. Qed.
  #[global] Instance _at_as_cfractional p (P : Rep) (R : cQp.t -> Rep) q :
    AsCFractional P R q ->
    AsCFractional (_at p P) (λ q, _at p (R q)) q.
  Proof. constructor. by rewrite -as_cfractional. apply _. Qed.

  #[global] Instance _at_observe {p} {Q R : Rep} :
    Observe Q R ->
    Observe (p |-> Q) (p |-> R).
  Proof. move->. by rewrite /Observe _at_pers. Qed.

  #[global] Instance _at_observe_2 {p} {Q R1 R2 : Rep} :
    Observe2 Q R1 R2 ->
    Observe2 (p |-> Q) (p |-> R1) (p |-> R2).
  Proof. move->. by rewrite /Observe2 _at_wand _at_pers. Qed.

  #[global] Instance _at_observe_only_provable Q p (R : Rep) :
    Observe [| Q |] R → Observe [| Q |] (p |-> R).
  Proof. rewrite -_at_only_provable. apply _. Qed.
  #[global] Instance _at_observe_2_only_provable Q p (R1 R2 : Rep) :
    Observe2 [| Q |] R1 R2 → Observe2 [| Q |] (p |-> R1) (p |-> R2).
  Proof. rewrite -_at_only_provable. apply _. Qed.

  #[global] Instance _at_observe_pure Q p (R : Rep) :
    Observe [! Q !] R → Observe [! Q !] (p |-> R).
  Proof. rewrite -_at_pure. apply _. Qed.
  #[global] Instance _at_observe_2_pure Q p (R1 R2 : Rep) :
    Observe2 [! Q !] R1 R2 → Observe2 [! Q !] (p |-> R1) (p |-> R2).
  Proof. rewrite -_at_pure. apply _. Qed.

  #[global] Instance observe_2_internal_eq_at {A : ofe} x y R1 R2 p :
    Observe2 (x ≡@{A} y) R1 R2 -> Observe2 (x ≡ y) (p |-> R1) (p |-> R2).
  Proof. rewrite !_at_loc. apply _. Qed.
  #[global] Instance observe_2_later_internal_eq_at {A : ofe} x y R1 R2 p :
    Observe2 (|> (x ≡@{A} y)) R1 R2 ->
    Observe2 (|> (x ≡ y)) (p |-> R1) (p |-> R2).
  Proof. rewrite !_at_loc. apply _. Qed.

  Lemma Rep_equiv_at {P Q : Rep} :
    (forall p : ptr, p |-> P -|- p |-> Q) <->
    P -|- Q.
  Proof.
    setoid_rewrite _at_loc; split; first by constructor.
    by move => /[swap] ? <-.
  Qed.

  Lemma Rep_entails_at {P Q : Rep} :
    (forall p : ptr, p |-> P |-- p |-> Q) <->
    P |-- Q.
  Proof.
    setoid_rewrite _at_loc; split; first by constructor.
    by move => /[swap] ? <-.
  Qed.

  Lemma Rep_emp_valid {P : Rep} :
    (forall p : ptr, |-- p |-> P) <->
    |-- P.
  Proof.
    rewrite /bi_emp_valid -Rep_entails_at.
    by setoid_rewrite _at_emp.
  Qed.

  Lemma _at_cfractional_list_div (R : cQp.t -> Rep) `{_ : CFractional _ R} q n (p : ptr) :
    (0 < n)%N ->
    p |-> R (cQp.m q) |-- [** list] _ ∈ replicateN n (), p |-> R (cQp.m (q / N_to_Qp n)).
  Proof. by move=>?; rewrite cfractional_list_div // _at_big_sepL. Qed.

  Lemma _at_obs p (r : Rep) P :
    r |-- r ** [| P |] →
    p |-> r |-- p |-> r ** [| P |].
  Proof. intros. apply observe_elim, _at_observe_only_provable. exact: observe_intro. Qed.

  #[global] Instance pureR_ne : NonExpansive pureR.
  Proof. solve_proper. Qed.
  #[global] Instance pureR_proper : Proper ((≡) ==> (≡)) pureR.
  Proof. solve_proper. Qed.
  #[global] Instance pureR_mono : Proper ((⊢) ==> (⊢)) pureR.
  Proof. by constructor. Qed.
  #[global] Instance pureR_flip_momo : Proper (flip (⊢) ==> flip (⊢)) pureR.
  Proof. by constructor. Qed.

  #[global] Instance pureR_persistent (P : mpred) :
    Persistent P -> Persistent (pureR P).
  Proof. apply _. Qed.
  #[global] Instance pureR_affine (P : mpred) :
    Affine P -> Affine (pureR P).
  Proof. apply _. Qed.
  #[global] Instance pureR_timeless (P : mpred) :
    Timeless P → Timeless (pureR P).
  Proof. apply _. Qed.
  #[global] Instance pureR_fractional (P : Qp → mpred) :
    Fractional P → Fractional (λ q, pureR (P q)).
  Proof. apply _. Qed.
  #[global] Instance pureR_as_fractional P Φ q :
    AsFractional P Φ q →
    AsFractional (pureR P) (λ q, pureR (Φ q)) q.
  Proof. intros [??]. constructor. done. apply _. Qed.
  #[global] Instance pureR_cfractional (P : cQp.t → mpred) :
    CFractional P -> CFractional (fun q => pureR (P q)).
  Proof. apply _. Qed.
  #[global] Instance pureR_as_cfractional (P : mpred) (F : cQp.t -> mpred) q :
    AsCFractional P F q →
    AsCFractional (pureR P) (fun q => pureR (F q)) q.
  Proof. intros [??]. constructor. done. apply _. Qed.

  #[global] Instance pureR_objective P : Objective (pureR P).
  Proof. done. Qed.

  #[global] Instance pureR_laterable P : Laterable P → Laterable (pureR P).
  Proof. intros. exact: as_Rep_laterable. Qed.

  Lemma pureR_persistently P : pureR (<pers> P) -|- <pers> pureR P.
  Proof. constructor=>p /=. by rewrite monPred_at_persistently. Qed.

  Lemma pureR_only_provable P : pureR [| P |] ⊣⊢ [| P |].
  Proof.
    split'.
    - rewrite (objective_objectively (pureR _)).
      rewrite monPred_objectively_unfold embed_forall.
      by rewrite (bi.forall_elim inhabitant) embed_only_provable.
    - constructor=>p. by rewrite monPred_at_only_provable.
  Qed.

  Lemma pureR_embed P : pureR P -|- embed P.
  Proof. exact: as_Rep_embed. Qed.

  Lemma pureR_emp : pureR emp -|- emp.
  Proof. exact: as_Rep_emp. Qed.
  Lemma pureR_sep (P Q : mpred) : pureR (P ** Q) -|- pureR P ** pureR Q.
  Proof. exact: as_Rep_sep. Qed.

  Lemma pureR_and (P Q : mpred) : pureR (P //\\ Q) -|- pureR P //\\ pureR Q.
  Proof. exact: as_Rep_and. Qed.

  Lemma pureR_or (P Q : mpred) : pureR (P \\// Q) -|- pureR P \\// pureR Q.
  Proof. exact: as_Rep_or. Qed.

  Lemma pureR_wand (P Q : mpred) : pureR (P -* Q) -|- pureR P -* pureR Q.
  Proof. exact: as_Rep_wand. Qed.

  Lemma pureR_exist {T} (P : T -> mpred) :
    pureR (Exists x, P x) -|- Exists x, pureR (P x).
  Proof. exact: as_Rep_exist. Qed.

  Lemma pureR_forall {T} (P : T -> mpred) :
    pureR (Forall x, P x) -|- Forall x, pureR (P x).
  Proof. exact: as_Rep_forall. Qed.

  Lemma pureR_pers (P : mpred) : pureR (<pers> P) -|- <pers> pureR P.
  Proof. exact: as_Rep_pers. Qed.

  Lemma pureR_bupd (P : mpred) : pureR (|==> P) -|- |==> pureR P.
  Proof. exact: as_Rep_bupd. Qed.

  Lemma pureR_fupd (P : mpred) E1 E2 : pureR (|={E1,E2}=> P) -|- |={E1,E2}=> pureR P.
  Proof. exact: as_Rep_fupd. Qed.

  Lemma pureR_intuitionistically (P : mpred) : pureR (□ P) -|- □ pureR P.
  Proof. exact: as_Rep_intuitionistically. Qed.

  Lemma pureR_intuitionistically_if b (P : mpred) : pureR (□?b P) -|- □?b pureR P.
  Proof. exact: as_Rep_intuitionistically_if. Qed.

  Lemma pureR_except_0 (P : mpred) : pureR (bi_except_0 P) -|- bi_except_0 (pureR P).
  Proof. exact: as_Rep_except_0. Qed.

  Lemma pureR_affinely (P : mpred) : pureR (<affine> P) -|- <affine> pureR P.
  Proof. exact: as_Rep_affinely. Qed.

  Lemma pureR_affinely_if b (P : mpred) : pureR (<affine>?b P) -|- <affine>?b pureR P.
  Proof. exact: as_Rep_affinely_if. Qed.

  Lemma pureR_big_sepL {T} (l : list T) F :
    pureR ([∗list] i ↦ x ∈ l , F i x) -|- [∗list] i ↦ x ∈ l , pureR (F i x).
  Proof. exact: as_Rep_big_sepL. Qed.

  Lemma pureR_later (P : mpred) : pureR (|> P) -|- |> pureR P.
  Proof. exact: as_Rep_later. Qed.

  Lemma pureR_internal_eq (P1 P2 : mpred) : pureR (P1 ≡ P2) -|- P1 ≡ P2.
  Proof. exact: as_Rep_internal_eq. Qed.

  #[global] Instance pureR_observe Q (P : mpred) :
    Observe [| Q |] P → Observe [| Q |] (pureR P).
  Proof. apply _. Qed.
  #[global] Instance pureR_observe_2 Q (P1 P2 : mpred) :
    Observe2 [| Q |] P1 P2 → Observe2 [| Q |] (pureR P1) (pureR P2).
  Proof. apply _. Qed.
  #[global] Instance pureR_observe_pure Q (P : mpred) :
    Observe [! Q !] P → Observe [! Q !] (pureR P).
  Proof.
    intros. apply monPred_observe=>p. by rewrite monPred_at_pure.
  Qed.
  #[global] Instance pureR_observe_2_pure Q (P1 P2 : mpred) :
    Observe2 [! Q !] P1 P2 → Observe2 [! Q !] (pureR P1) (pureR P2).
  Proof.
    intros. apply monPred_observe_2=>p. by rewrite monPred_at_pure.
  Qed.

  Lemma pureR_obs P Q :
    P |-- P ** [| Q |] →
    pureR P |-- pureR P ** [| Q |].
  Proof. intros. apply observe_elim, pureR_observe. exact: observe_intro. Qed.

  Lemma pureR_pure P : pureR ⌜P⌝ ⊣⊢ ⌜P⌝.
  Proof.
    split'.
    - rewrite (objective_objectively (pureR _)).
      rewrite monPred_objectively_unfold embed_forall.
      by rewrite (bi.forall_elim inhabitant) embed_pure.
    - constructor=>p. by rewrite monPred_at_pure.
  Qed.
  Definition pureR_True : pureR True ⊣⊢ True := pureR_pure _.
  Definition pureR_False : pureR False ⊣⊢ False := pureR_pure _.

  Lemma _at_pureR x (P : mpred) : _at x (pureR P) -|- P.
  Proof. by rewrite !_at_loc /pureR. Qed.

  Lemma _offsetR_pureR o P : o |-> (pureR P) -|- pureR P.
  Proof. by apply Rep_equiv_at => p; rewrite _at_offsetR !_at_pureR. Qed.

  (** As this isn't syntax-directed, we conservatively avoid
      registering it as an instance (which could slow down
      observations). It's handy under [#[local] Existing Instance
      _at_observe_pureR] to project a [pureR Q] conjunct out of
      representation predicates. *)
  Lemma _at_observe_pureR Q p (R : Rep) :
    Observe (pureR Q) R → Observe Q (p |-> R).
  Proof.
    rewrite /Observe=>->. rewrite -pureR_persistently _at_pureR. done.
  Qed.

  (** Introduce Observations at [Rep] by proving them more easily at [mpred] *)
  Lemma observe_at (Q P : Rep) :
    (∀ p : ptr, Observe (p |-> Q) (p |-> P)) ↔
    Observe Q P.
  Proof.
    split; intros; last exact: _at_observe.
    apply monPred_observe=> p. by rewrite -!_at_loc.
  Qed.

  Lemma observe_only_provable_at Q (P : Rep) :
    (∀ p : ptr, Observe [| Q |] (p |-> P)) ↔
    Observe [| Q |] P.
  Proof.
    rewrite -observe_at.
    apply iff_forall => p. by rewrite _at_only_provable.
  Qed.

  Lemma observe_2_at (Q P1 P2 : Rep) :
    (∀ p : ptr, Observe2 (p |-> Q) (p |-> P1) (p |-> P2)) ↔
    Observe2 Q P1 P2.
  Proof.
    split; intros; last exact: _at_observe_2.
    apply monPred_observe_2=> p. by rewrite -!_at_loc.
  Qed.

  Lemma observe_2_only_provable_at Q (P1 P2 : Rep) :
    (∀ p : ptr, Observe2 [| Q |] (p |-> P1) (p |-> P2)) ↔
    Observe2 [| Q |] P1 P2.
  Proof.
    rewrite -observe_2_at.
    apply iff_forall => p. by rewrite _at_only_provable.
  Qed.

  Section o_sub.
    Context {σ : genv}.

    Lemma _offsetR_sub_0 ty R
      (Hsz : is_Some (size_of σ ty)) :
      _offsetR (.[ ty ! 0 ]) R -|- R.
    Proof. by rewrite o_sub_0 // _offsetR_id. Qed.

    Lemma _offsetR_sub_sub ty a b R :
      .[ ty ! a ] |-> (.[ ty ! b ] |-> R) ⊣⊢
      .[ ty ! a + b ] |-> R.
    Proof. by rewrite _offsetR_dot o_dot_sub. Qed.

    Lemma _offsetR_succ_sub ty z R :
      .[ ty ! 1 ] |-> (.[ ty ! z ] |-> R) ⊣⊢
      .[ ty ! Z.succ z] |-> R.
    Proof. by rewrite _offsetR_sub_sub Z.add_1_l. Qed.

    Lemma _offsetR_sub_succ ty z R :
      .[ ty ! z ] |-> (.[ ty ! 1 ] |-> R) ⊣⊢
      .[ ty ! Z.succ z] |-> R.
    Proof. by rewrite _offsetR_sub_sub Z.add_1_r. Qed.

    Lemma _at_sub_0 p ty R
      (Hsz : is_Some (size_of σ ty)) :
      p .[ ty ! 0 ] |-> R -|- p |-> R.
    Proof. by rewrite offset_ptr_sub_0. Qed.

    Lemma _at_sub_sub p ty a b R :
      p .[ ty ! a ] |-> (.[ ty ! b ] |-> R) ⊣⊢
      p .[ ty ! a + b ] |-> R.
    Proof. by rewrite -!_at_offsetR _offsetR_sub_sub. Qed.

    Lemma _at_succ_sub p ty z R :
      p .[ ty ! 1 ] |-> (.[ ty ! z ] |-> R) ⊣⊢
      p .[ ty ! Z.succ z] |-> R.
    Proof. by rewrite -!_at_offsetR _offsetR_succ_sub. Qed.

    Lemma _at_sub_succ p ty z R :
      p .[ ty ! z ] |-> .[ ty ! 1 ] |-> R ⊣⊢
      p .[ ty ! Z.succ z] |-> R.
    Proof. by rewrite -!_at_offsetR _offsetR_sub_succ. Qed.
  End o_sub.
End with_cpp.

#[global] Typeclasses Opaque pureR as_Rep.
