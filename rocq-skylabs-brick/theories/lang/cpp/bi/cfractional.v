(*
 * Copyright (c) 2022-2023 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Export bluerock.lang.cpp.algebra.cfrac.

Require Import bluerock.iris.extra.bi.prelude.
Require Import bluerock.iris.extra.bi.observe.
Require Import bluerock.iris.extra.bi.split_frac.
Require Import bluerock.lang.cpp.bi.split_cfrac.
Require Import bluerock.iris.extra.proofmode.proofmode.
Import ChargeNotation.

#[local] Set Printing Coercions.
#[local] Set Primitive Projections.

(** * Fractional predicates at type [cQp.t] *)
(**
Overview:

- [CFractional], [AsCFractional] enable one to declare predicates that
are fractional at type [cQp.t]

- Tactic [solve_as_cfrac] for solving [AsCFractional]

- [CFractionalN], [AsCFractionalN], [AgreeCF1] notation to save typing

- [CFracValidN] classes enabling observations about validity

- Tactic [solve_cfrac_valid] for solving [CFracValidN]

- [IntoSep], [FromSep] instances teaching the IPM to split and combine
[CFractional] predicates
*)

(** Proof obligation for const/mutable fractional things. *)
Class CFractional {PROP : bi} (P : cQp.t -> PROP) : Prop :=
  cfractional q1 q2 : P (q1 + q2)%cQp -|- P q1 ** P q2.
#[global] Hint Mode CFractional + ! : typeclass_instances.
#[global] Arguments CFractional {_} _%_I : simpl never, assert.
#[global] Hint Extern 100 (CFractional (fun a => match ?x with _ => _ end)) =>
  destruct x : typeclass_instances.

(**
[CFractionalN] states that predicate [P] taking a const/mutable
fraction and then [N] arguments is [CFractional]
*)
Notation CFractional0 := CFractional (only parsing).
Notation CFractional1 P := (∀ a, CFractional (fun q => P q a)) (only parsing).
Notation CFractional2 P := (∀ a b, CFractional (fun q => P q a b)) (only parsing).
Notation CFractional3 P := (∀ a b c, CFractional (fun q => P q a b c)) (only parsing).
Notation CFractional4 P := (∀ a b c d, CFractional (fun q => P q a b c d)) (only parsing).
Notation CFractional5 P := (∀ a b c d e, CFractional (fun q => P q a b c d e)) (only parsing).

(** [CFractional] wrapper suited to avoiding HO unification. *)
Class AsCFractional {PROP : bi} (P : PROP) (Q : cQp.t -> PROP) (q : cQp.t) : Prop := {
  as_cfractional : P -|- Q q;
  #[global] as_cfractional_cfractional :: CFractional Q;
}.
#[global] Hint Mode AsCFractional + ! - - : typeclass_instances.
#[global] Hint Mode AsCFractional + - + - : typeclass_instances.
#[global] Arguments AsCFractional {_} (_ _)%_I _%_Qp : assert.

Ltac solve_as_cfrac := solve [intros; exact: Build_AsCFractional].

(** [AsCFractionalN] informs the IPM about predicate [P] satisfying [CFractionalN P] *)
Notation AsCFractional0 P := (∀ q, AsCFractional (P q) P q) (only parsing).
Notation AsCFractional1 P := (∀ q a, AsCFractional (P q a) (fun q => P%I q a) q) (only parsing).
Notation AsCFractional2 P := (∀ q a b, AsCFractional (P q a b) (fun q => P%I q a b) q) (only parsing).
Notation AsCFractional3 P := (∀ q a b c, AsCFractional (P q a b c) (fun q => P%I q a b c) q) (only parsing).
Notation AsCFractional4 P := (∀ q a b c d, AsCFractional (P q a b c d) (fun q => P%I q a b c d) q) (only parsing).
Notation AsCFractional5 P := (∀ q a b c d e, AsCFractional (P q a b c d e) (fun q => P%I q a b c d e) q) (only parsing).

(**
[AgreeCF1 P] states that [P q a] only holds for one possible [a],
regardless of const/mutable fraction [q].
*)
Notation AgreeCF1 P := (∀ (q1 q2 : cQp.t) a1 a2, Observe2 [| a1 = a2 |] (P q1 a1) (P q2 a2)) (only parsing).

(**
[CFracValidN P] encapsulates the observation [cQp.frac q ≤ 1] from [P]
applied to const/mutable fraction [q] and then [N] arguments. The
[CFracValidN] enable easier to use observations about validity.
*)
Class CFracValid0 {PROP : bi} (P : cQp.t -> PROP) : Prop :=
  { cfrac_valid_0 q : Observe [| cQp.frac q ≤ 1 |]%Qp (P q) }.
#[global] Hint Mode CFracValid0 - + : typeclass_instances.
#[global] Arguments CFracValid0 {_} _%_I : assert.

Class CFracValid1 {A} {PROP : bi} (P : cQp.t -> A -> PROP) : Prop :=
  { cfrac_valid_1 q a : Observe [| cQp.frac q ≤ 1 |]%Qp (P q a) }.
#[global] Hint Mode CFracValid1 - - + : typeclass_instances.
#[global] Arguments CFracValid1 {_ _} _%_I : assert.

Class CFracValid2 {A B} {PROP : bi} (P : cQp.t -> A -> B -> PROP) : Prop :=
  { cfrac_valid_2 q a b : Observe [| cQp.frac q ≤ 1 |]%Qp (P q a b) }.
#[global] Hint Mode CFracValid2 - - - + : typeclass_instances.
#[global] Arguments CFracValid2 {_ _ _} _%_I : assert.

Class CFracValid3 {A B C} {PROP : bi} (P : cQp.t -> A -> B -> C -> PROP) : Prop :=
  { cfrac_valid_3 q a b c : Observe [| cQp.frac q ≤ 1 |]%Qp (P q a b c) }.
#[global] Hint Mode CFracValid3 - - - - + : typeclass_instances.
#[global] Arguments CFracValid3 {_ _ _ _} _%_I : assert.

Class CFracValid4 {A B C D} {PROP : bi} (P : cQp.t -> A -> B -> C -> D -> PROP) : Prop :=
  { cfrac_valid_4 q a b c d : Observe [| cQp.frac q ≤ 1 |]%Qp (P q a b c d) }.
#[global] Hint Mode CFracValid4 - - - - - + : typeclass_instances.
#[global] Arguments CFracValid4 {_ _ _ _ _} _%_I : assert.

Class CFracValid5 {A B C D E} {PROP : bi} (P : cQp.t -> A -> B -> C -> D -> E -> PROP) : Prop :=
  { cfrac_valid_5 q a b c d e : Observe [| cQp.frac q ≤ 1 |]%Qp (P q a b c d e) }.
#[global] Hint Mode CFracValid5 - - - - - - + : typeclass_instances.
#[global] Arguments CFracValid5 {_ _ _ _ _ _} _%_I : assert.

Ltac solve_cfrac_valid := solve [intros; constructor; apply _].

(** ** Properties of [CFractional] *)
Section cfractional.
  Context {PROP : bi}.
  Implicit Types (P Q : PROP).

  #[global] Instance: Params (@CFractional) 1 := {}.
  #[global] Instance CFractional_proper :
    Proper (pointwise_relation _ (equiv (A:=PROP)) ==> iff) CFractional.
  Proof.
    intros P1 P2 EQ. split=>Frac q1 q2.
    by rewrite -EQ Frac. by rewrite EQ Frac.
  Qed.

  (** *** Compatibility for [CFractional] *)

  (** This follows by unfolding, but that was surprising. *)
  Lemma cfractional_dup P :
    (P -|- P ** P) ->
    CFractional (λ _, P).
  Proof. by rewrite /CFractional. Qed.

  #[global] Instance persistent_cfractional `{!Persistent P, !TCOr (Affine P) (Absorbing P)} :
    CFractional (fun _ => P).
  Proof. apply /cfractional_dup /bi.persistent_sep_dup. Qed.

  #[global] Instance cfractional_sep (F G : cQp.t -> PROP) :
    CFractional F -> CFractional G ->
    CFractional (fun q => F q ** G q).
  Proof.
    rewrite /CFractional=>HF HG q1 q2. rewrite {}HF {}HG.
    split'; iIntros "([$ $] & $ & $)".
  Qed.

  #[global] Instance cfractional_exist {A} (P : A -> cQp.t -> PROP) :
    (∀ oa, CFractional (P oa)) ->
    (∀ a1 a2 q1 q2, Observe2 [| a1 = a2 |] (P a1 q1) (P a2 q2)) ->
    CFractional (fun q => Exists a : A, P a q).
  Proof.
    intros ?? q1 q2.
    rewrite -bi.exist_sep; last by intros; exact: observe_2_elim_pure.
    f_equiv=>oa. apply: cfractional.
  Qed.

  #[global] Instance cfractional_embed `{!BiEmbed PROP PROP'} F :
    CFractional F -> CFractional (fun q => embed (F q) : PROP').
  Proof. intros ???. by rewrite cfractional embed_sep. Qed.

  #[global] Instance as_cfractional_embed `{!BiEmbed PROP PROP'} P F q :
    AsCFractional P F q -> AsCFractional (embed P) (fun q => embed (F q)) q.
  Proof. split; [by rewrite ->!as_cfractional | apply _]. Qed.

  #[global] Instance cfractional_big_sepL {A} (l : list A) F :
    (∀ k x, CFractional (F k x)) ->
    CFractional (PROP:=PROP) (funI q => [** list] k |-> x ∈ l, F k x q).
  Proof. intros ? q q'. rewrite -big_sepL_sep. by setoid_rewrite cfractional. Qed.

  #[global] Instance cfractional_big_sepL2 {A B} (l1 : list A) (l2 : list B) F :
    (∀ k x1 x2, CFractional (F k x1 x2)) ->
    CFractional (PROP:=PROP) (funI q => [∗ list] k↦x1; x2 ∈ l1; l2, F k x1 x2 q).
  Proof. intros ? q q'. rewrite -big_sepL2_sep. by setoid_rewrite cfractional. Qed.

  #[global] Instance cfractional_big_sepM `{Countable K} {A} (m : gmap K A) F :
    (∀ k x, CFractional (F k x)) ->
    CFractional (PROP:=PROP) (funI q => [** map] k |-> x ∈ m, F k x q).
  Proof. intros ? q q'. rewrite -big_sepM_sep. by setoid_rewrite cfractional. Qed.

  #[global] Instance cfractional_big_sepS `{Countable A} (X : gset A) F :
    (∀ x, CFractional (F x)) ->
    CFractional (PROP:=PROP) (funI q => [** set] x ∈ X, F x q).
  Proof. intros ? q q'. rewrite -big_sepS_sep. by setoid_rewrite cfractional. Qed.

  #[global] Instance cfractional_big_sepMS `{Countable A} (X : gmultiset A) F :
    (∀ x, CFractional (F x)) ->
    CFractional (PROP:=PROP) (funI q => [** mset] x ∈ X, F x q).
  Proof. intros ? q q'. rewrite -big_sepMS_sep. by setoid_rewrite cfractional. Qed.

  (** *** Lifting [Fractional] things via [cQp.frac]. *)

  #[global] Instance fractional_cfractional_0 (P : Qp -> PROP) :
    Fractional P -> CFractional (fun q => P (cQp.frac q)).
  Proof. intros HP ??. apply HP. Qed.
  #[global] Instance fractional_cfractional_1 {A} (P : Qp -> A -> PROP) :
    Fractional1 P -> CFractional1 (fun q a => P (cQp.frac q) a).
  Proof. intros HP ???. apply HP. Qed.
  #[global] Instance fractional_cfractional_2 {A B} (P : Qp -> A -> B -> PROP) :
    Fractional2 P -> CFractional2 (fun q a b => P (cQp.frac q) a b).
  Proof. intros HP ????. apply HP. Qed.
  #[global] Instance fractional_cfractional_3 {A B C} (P : Qp -> A -> B -> C -> PROP) :
    Fractional3 P -> CFractional3 (fun q a b c => P (cQp.frac q) a b c).
  Proof. intros HP ?????. apply HP. Qed.
  #[global] Instance fractional_cfractional_4 {A B C D} (P : Qp -> A -> B -> C -> D -> PROP) :
    Fractional4 P -> CFractional4 (fun q a b c d => P (cQp.frac q) a b c d).
  Proof. intros HP ??????. apply HP. Qed.
  #[global] Instance fractional_cfractional_5 {A B C D E} (P : Qp -> A -> B -> C -> D -> E ->PROP) :
    Fractional5 P -> CFractional5 (fun q a b c d e => P (cQp.frac q) a b c d e).
  Proof. intros HP ???????. apply HP. Qed.

  (** *** Lifting [CFractional] things when using [cQp.mk]. *)

  #[global] Instance cfractional_cfractional_mk_0 (P : cQp.t -> PROP) c :
    CFractional P -> CFractional (fun q => P (cQp.mk c (cQp.frac q))).
  Proof. intros HP ??. rewrite cQp.mk_add'. apply HP. Qed.

  #[global] Instance cfractional_cfractional_mk_1 {A} (P : cQp.t -> A -> PROP) c :
    CFractional1 P -> ∀ a, CFractional (fun q => P (cQp.mk c (cQp.frac q)) a).
  Proof. intros HP ???. rewrite cQp.mk_add'. apply HP. Qed.

  #[global] Instance cfractional_cfractional_mk_2 {A B} (P : cQp.t -> A -> B -> PROP) cm :
    CFractional2 P -> ∀ a b, CFractional (fun q => P (cQp.mk cm (cQp.frac q)) a b).
  Proof. intros HP ????. rewrite cQp.mk_add'. apply HP. Qed.

  #[global] Instance cfractional_cfractional_mk_3 {A B C} (P : cQp.t -> A -> B -> C -> PROP) cm :
    CFractional3 P -> ∀ a b c, CFractional (fun q => P (cQp.mk cm (cQp.frac q)) a b c).
  Proof. intros HP ?????. rewrite cQp.mk_add'. apply HP. Qed.

  #[global] Instance cfractional_cfractional_mk_4 {A B C D} (P : cQp.t -> A -> B -> C -> D -> PROP) cm :
    CFractional4 P -> ∀ a b c d, CFractional (fun q => P (cQp.mk cm (cQp.frac q)) a b c d).
  Proof. intros HP ??????. rewrite cQp.mk_add'. apply HP. Qed.

  #[global] Instance cfractional_cfractional_mk_5 {A B C D E} (P : cQp.t -> A -> B -> C -> D -> E -> PROP) cm :
    CFractional5 P -> ∀ a b c d e, CFractional (fun q => P (cQp.mk cm (cQp.frac q)) a b c d e).
  Proof. intros HP ???????. rewrite cQp.mk_add'. apply HP. Qed.
End cfractional.

(** ** Backwards compatibility *)

(**
Temporary support for the [cQp._mut] coercion.
*)
Module cQp_compat.
  Export cfrac.cQp_compat.

  Section cfractional.
    Context {PROP : bi}.
    Implicit Types (P Q : PROP).

    (** *** Lifting [CFractional] things into [Fractional] when using [cQp._mut] *)

    #[export] Instance cfractional_fractional_mut_0 (P : cQp.t -> PROP) :
      CFractional P -> Fractional P.
    Proof. intros HP ??. cbn. rewrite cQp.mk_add'. apply HP. Qed.

    #[export] Instance cfractional_fractional_mut_1 {A} (P : cQp.t -> A -> PROP) :
      CFractional1 P -> Fractional1 P.
    Proof. intros HP ???. cbn. rewrite cQp.mk_add'. apply HP. Qed.

    #[export] Instance cfractional_fractional_mut_2 {A B} (P : cQp.t -> A -> B -> PROP) :
      CFractional2 P -> Fractional2 P.
    Proof. intros HP ????. cbn. rewrite cQp.mk_add'. apply HP. Qed.

    #[export] Instance cfractional_fractional_mut_3 {A B C} (P : cQp.t -> A -> B -> C -> PROP) :
      CFractional3 P -> Fractional3 P.
    Proof. intros HP ?????. cbn. rewrite cQp.mk_add'. apply HP. Qed.

    #[export] Instance cfractional_fractional_mut_4 {A B C D} (P : cQp.t -> A -> B -> C -> D -> PROP) :
      CFractional4 P -> Fractional4 P.
    Proof. intros HP ??????. cbn. rewrite cQp.mk_add'. apply HP. Qed.

    #[export] Instance cfractional_fractional_mut_5 {A B C D E} (P : cQp.t -> A -> B -> C -> D -> E -> PROP) :
      CFractional5 P -> Fractional5 P.
    Proof. intros HP ???????. cbn. rewrite cQp.mk_add'. apply HP. Qed.

  End cfractional.

End cQp_compat.

Section fractional.
  Context {PROP : bi}.
  Implicit Types (P Q : PROP).

  (** *** Multiplication *)
  (**
  Note: These instances do not fire automatically. They're useful when
  proving [CFractional R] for things like [R (q : cQp.t) := R1 q ** R2
  (cQp.frac q * p)] where [p : Qp, R1 : cQp.t -> PROP, R2 : Qp ->
  PROP].
  *)
  #[global] Instance fractional_cfractional_mul_r (F G : Qp -> PROP) (p : Qp) :
    (∀ q, AsFractional (F q) G (q * p)) ->
    CFractional (fun q => F (cQp.frac q)).
  Proof.
    intros HF q1 q2. do !rewrite [F _]as_fractional.
    rewrite Qp.mul_add_distr_r.
    move: (HF 1%Qp) => [] _ //.
  Qed.

  #[global] Instance fractional_cfractional_mul_l (F G : Qp -> PROP) (p : Qp) :
    (∀ q, AsFractional (F q) G (p * q)) ->
    CFractional (fun q => F (cQp.frac q)).
  Proof.
    intros HF q1 q2. do !rewrite [F _]as_fractional.
    rewrite Qp.mul_add_distr_l.
    move: (HF 1%Qp) => [] _ //.
  Qed.

  Lemma cfractional_list_div (P : cQp.t -> PROP) `{_ : CFractional _ P} q n :
    (0 < n)%N ->
    P (cQp.m q) |-- [** list] _ ∈ replicateN n (), P (cQp.m (q / N_to_Qp n)).
  Proof.
    move=>/N.succ_pred_pos<-; set n' := (N.pred _).
    move: {n}n' q; apply: N.peano_ind=>[|n]; first
      by move=>q; rewrite /= Qp.div_1 bi.sep_emp.
    move=>HIP q; rewrite N_to_Qp_succ; last lia.
    set p := (N_to_Qp _).
    rewrite (replicateN_S _ ((N.succ _))) big_opL_cons.

    have{1}->: (q$m = (q * p / (p + 1))$m + (q / (p + 1))$m)%cQp.
    {
      rewrite /cQp.add/=; f_equal.
      by rewrite -Qp.div_add_distr -{3}[q]Qp.mul_1_r -Qp.mul_add_distr_l
         -{2}[(p + 1)%Qp]Qp.mul_1_l Qp.div_mul_cancel_r Qp.div_1.
    }

    iIntros "H"; iDestruct (cfractional with "H") as "[H $]".
    iDestruct (HIP (q * p / (p + 1))%Qp with "H") as "?".
    by rewrite Qp.div_div Qp.div_mul_cancel_r.
  Qed.

  (** *** Lifting [CFractional] things into [Fractional] when using [cQp.mk] *)

  #[global] Instance cfractional_fractional_mk_0 (P : cQp.t -> PROP) is_const :
    CFractional P -> Fractional (fun q => P (cQp.mk is_const q)).
  Proof. intros HP ??. by rewrite cQp.mk_add' HP. Qed.

  #[global] Instance cfractional_fractional_mk_1 {A} (P : cQp.t -> A -> PROP) is_const :
    CFractional1 P -> Fractional1 (fun q a => P (cQp.mk is_const q) a).
  Proof. intros HP ???. by rewrite cQp.mk_add' HP. Qed.

  #[global] Instance cfractional_fractional_mk_2 {A B} (P : cQp.t -> A -> B -> PROP) is_const :
    CFractional2 P -> Fractional2 (fun q a b => P (cQp.mk is_const q) a b).
  Proof. intros HP ????. by rewrite cQp.mk_add' HP. Qed.

  #[global] Instance cfractional_fractional_mk_3 {A B C} (P : cQp.t -> A -> B -> C -> PROP) is_const :
    CFractional3 P -> Fractional3 (fun q a b c => P (cQp.mk is_const q) a b c).
  Proof. intros HP ?????. by rewrite cQp.mk_add' HP. Qed.

  #[global] Instance cfractional_fractional_mk_4 {A B C D} (P : cQp.t -> A -> B -> C -> D -> PROP) is_const :
    CFractional4 P -> Fractional4 (fun q a b c d => P (cQp.mk is_const q) a b c d).
  Proof. intros HP ??????. by rewrite cQp.mk_add' HP. Qed.

  #[global] Instance cfractional_fractional_mk_5 {A B C D E} (P : cQp.t -> A -> B -> C -> D -> E -> PROP) is_const :
    CFractional5 P -> Fractional5 (fun q a b c d e => P (cQp.mk is_const q) a b c d e).
  Proof. intros HP ???????. by rewrite cQp.mk_add' HP. Qed.

End fractional.

(** ** IPM instances *)
Section proofmode.
  Context {PROP : bi}.
  Implicit Types (P Q : PROP) (F G : cQp.t -> PROP).

  #[local] Lemma as_cfractional_split P P1 P2 F q q1 q2 :
    AsCFractional P F q -> SplitCFrac q q1 q2 ->
    AsCFractional P1 F q1 -> AsCFractional P2 F q2 ->
    P -|- P1 ** P2.
  Proof.
    intros [->?] ? [->_] [->_]. by rewrite (split_cfrac q) cfractional.
  Qed.

  #[local] Lemma as_cfractional_combine P1 P2 P F q1 q2 q :
    AsCFractional P1 F q1 -> AsCFractional P2 F q2 ->
    CombineCFrac q1 q2 q -> AsCFractional P F q ->
    P -|- P1 ** P2.
  Proof.
    intros [->?] [->_] ? [->_]. by rewrite -cfractional combine_cfrac.
  Qed.

  (**
  Support the IPM's [P1 P2] intro pattern: [P] an input; [P1], [P2]
  outputs.
  *)

  #[global] Instance into_sep_cfractional P P1 P2 F q q1 q2 :
    AsCFractional P F q -> SplitCFrac q q1 q2 ->
    AsCFractional P1 F q1 -> AsCFractional P2 F q2 ->
    IntoSep P P1 P2.
  Proof.
    intros. rewrite/IntoSep. by rewrite (as_cfractional_split P).
  Qed.

  (**
  Support the IPM's [iSplitL], [iSplitR] tactics: [P] an input; [P1],
  [P2] outputs.
  *)
  #[global] Instance from_sep_cfractional_split P P1 P2 F q q1 q2 :
    AsCFractional P F q -> SplitCFrac q q1 q2 ->
    AsCFractional P1 F q1 -> AsCFractional P2 F q2 ->
    FromSep P P1 P2.
  Proof.
    intros. rewrite/FromSep. by rewrite -(as_cfractional_split P).
  Qed.

  (**
  Support the IPM's [iCombine] tactic: [P1], [P2] inputs, [P] an
  output.
  *)
  #[global] Instance combine_sep_as_cfractional_bwd P1 P2 P F q1 q2 q :
    AsCFractional P1 F q1 -> AsCFractional P2 F q2 ->
    CombineCFrac q1 q2 q -> AsCFractional P F q ->
    CombineSepAs P1 P2 P | 100.
  Proof.
    intros. rewrite /CombineSepAs. by rewrite -as_cfractional_combine.
  Qed.
End proofmode.

(** Useful in rare cases. Here because the proof reuses IPM. *)
#[global] Instance cfractional_ignore_exist {PROP : bi} (P : cQp.t -> PROP)
  `{HcfP : CFractional0 P} :
  CFractional (λI _, ∃ q, P q).
Proof.
  have ? : AsCFractional0 P by solve_as_cfrac.
  apply cfractional_dup. iSplit.
  { by iIntros "[% [$ $]]". }
  iIntros "[[% A] [% B]]". iCombine "A B" as "$".
Qed.

(** ** Observations from validity *)
(**
The [CFracValidN] enable several related, but easier to apply,
observations.
*)

Notation CFrac0Valid P := (∀ q p,
  cQpTC.FRAC q p -> Observe [| p ≤ 1 |]%Qp (P q)) (only parsing).
Notation CFrac0Valid2 P := (∀ q1 q2 p1 p2 q,
  cQpTC.FRAC q1 p1 -> cQpTC.FRAC q2 p2 -> QpTC.ADD p1 p2 q ->
  Observe2 [| q ≤ 1 |]%Qp (P q1) (P q2)) (only parsing).
Notation CFrac0Exclusive P := (∀ q1,
  cQpTC.FRAC q1 1 -> ∀ q2, Observe2 False (P q1) (P q2)) (only parsing).
Section valid_0.
  #[local] Set Default Proof Using "Type*".
  Context {PROP : bi} (P : cQp.t -> PROP) `{!CFracValid0 P}.

  #[global] Instance cfrac_0_valid : CFrac0Valid P.
  Proof. intros ?? [<-]. apply cfrac_valid_0. Qed.

  Section examples.
    Lemma mut q : Observe [| q ≤ 1 |]%Qp (P q$m).
    Proof. apply _. Abort.

    Lemma scale_mut p q :
      Observe [| p * q ≤ 1 |]%Qp (P (cQp.scale p q$m)).
    Proof. apply _. Abort.

    Lemma scale_mut p1 p2 q :
      Observe [| p1 * (p2 * q) ≤ 1 |]%Qp
        (P (cQp.scale p1 (cQp.scale p2 q$m))).
    Proof. apply _. Abort.
  End examples.

  #[global] Instance cfrac_0_valid_2 : CFractional0 P -> CFrac0Valid2 P.
  Proof.
    intros Hfrac ????? [Hq1] [Hq2] [Hq]. rewrite -{}Hq -{}Hq1 -{}Hq2.
    apply observe_uncurry. rewrite -{}Hfrac. apply: cfrac_0_valid.
  Qed.

  #[global] Instance cfrac_0_exclusive : CFractional0 P -> CFrac0Exclusive P.
  Proof.
    intros. iIntros "P1 P2".
    by iDestruct (cfrac_0_valid_2 with "P1 P2") as %?%Qp.not_add_le_l.
  Qed.
End valid_0.

Notation CFrac1Valid P := (∀ q p,
  cQpTC.FRAC q p -> ∀ a, Observe [| p ≤ 1 |]%Qp (P q a)) (only parsing).
Notation CFrac1Valid2 P := (∀ q1 q2 p1 p2 q,
  cQpTC.FRAC q1 p1 -> cQpTC.FRAC q2 p2 -> QpTC.ADD p1 p2 q ->
  ∀ a1 a2, Observe2 [| q ≤ 1 |]%Qp (P q1 a1) (P q2 a2)) (only parsing).
Notation CFrac1Exclusive P := (∀ q1,
  cQpTC.FRAC q1 1 -> ∀ q2 a1 a2, Observe2 False (P q1 a1) (P q2 a2)) (only parsing).
Section valid_1.
  #[local] Set Default Proof Using "Type*".
  Context {A} {PROP : bi} (P : cQp.t -> A -> PROP) `{!CFracValid1 P}.

  #[global] Instance cfrac_1_valid : CFrac1Valid P.
  Proof. intros ?? [<-] *. apply cfrac_valid_1. Qed.

  #[global] Instance cfrac_1_valid_2 : CFractional1 P -> AgreeCF1 P -> CFrac1Valid2 P.
  Proof.
    intros Hfrac Hagree ????? [Hq1] [Hq2] [Hq] *. rewrite -{}Hq -{}Hq1 -{}Hq2.
    iIntros "P1 P2". iDestruct (Hagree with "P1 P2") as %<-.
    iCombine "P1 P2" as "P". rewrite -Hfrac. iApply (cfrac_1_valid with "P").
  Qed.

  #[global] Instance cfrac_1_exclusive : CFractional1 P -> AgreeCF1 P -> CFrac1Exclusive P.
  Proof.
    intros. iIntros "P1 P2".
    by iDestruct (cfrac_1_valid_2 with "P1 P2") as %?%Qp.not_add_le_l.
  Qed.
End valid_1.

Notation CFrac2Valid P := (∀ q p,
  cQpTC.FRAC q p -> ∀ a b, Observe [| p ≤ 1 |]%Qp (P q a b)) (only parsing).
Section valid_2.
  #[local] Set Default Proof Using "Type*".
  Context {A B} {PROP : bi} (P : cQp.t -> A -> B -> PROP) `{!CFracValid2 P}.

  #[global] Instance cfrac_2_valid : CFrac2Valid P.
  Proof. intros ?? [<-] *. apply cfrac_valid_2. Qed.
End valid_2.

Notation CFrac3Valid P := (∀ q p,
  cQpTC.FRAC q p -> ∀ a b c, Observe [| p ≤ 1 |]%Qp (P q a b c)) (only parsing).
Section valid_3.
  #[local] Set Default Proof Using "Type*".
  Context {A B C} {PROP : bi} (P : cQp.t -> A -> B -> C -> PROP) `{!CFracValid3 P}.

  #[global] Instance cfrac_3_valid : CFrac3Valid P.
  Proof. intros ?? [<-] *. apply cfrac_valid_3. Qed.
End valid_3.

Notation CFrac4Valid P := (∀ q p,
  cQpTC.FRAC q p -> ∀ a b c d, Observe [| p ≤ 1 |]%Qp (P q a b c d)) (only parsing).
Section valid_4.
  #[local] Set Default Proof Using "Type*".
  Context {A B C D} {PROP : bi} (P : cQp.t -> A -> B -> C -> D -> PROP) `{!CFracValid4 P}.

  #[global] Instance cfrac_4_valid : CFrac4Valid P.
  Proof. intros ?? [<-] *. apply cfrac_valid_4. Qed.
End valid_4.

Notation CFrac5Valid P := (∀ q p,
  cQpTC.FRAC q p -> ∀ a b c d e, Observe [| p ≤ 1 |]%Qp (P q a b c d e)) (only parsing).
Section valid_5.
  #[local] Set Default Proof Using "Type*".
  Context {A B C D E} {PROP : bi} (P : cQp.t -> A -> B -> C -> D -> E -> PROP) `{!CFracValid5 P}.

  #[global] Instance cfrac_5_valid : CFrac5Valid P.
  Proof. intros ?? [<-] *. apply cfrac_valid_5. Qed.
End valid_5.
