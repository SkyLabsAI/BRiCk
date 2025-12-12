(*
 * Copyright (c) 2020 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import iris.bi.bi.
Require Import bluerock.iris.extra.proofmode.proofmode.
Require Import bluerock.iris.extra.bi.prelude.
Import ChargeNotation.

(* TODO: move used lemmas that aren't trivial Iris wrappers into derived_laws with new names. *)
Section with_PROP.
  Context {PROP : bi}.

  (* Original charge lemmas. *)
  Lemma ltrueR (C : PROP) : C |-- True.
  Proof. apply bi.True_intro. Qed.
  Lemma lfalseL (C : PROP) : False |-- C.
  Proof. apply bi.False_elim. Qed.
  Lemma lexistsL {T : Type} (P: T -> PROP) C : (forall x, P x |-- C) -> Exists y, P y |-- C.
  Proof. exact: bi.exist_elim. Qed.
  Lemma lexistsR {T : Type} (x : T) (P: T -> PROP) C : C |-- P x -> C |-- Exists y, P y.
  Proof. exact: bi.exist_intro'. Qed.
  Lemma lforallL {T : Type} x (P: T -> PROP) C : P x |-- C -> Forall y, P y |-- C.
  Proof. rewrite -bi.forall_elim. apply. Qed.
  Lemma lforallR {T : Type} (P: T -> PROP) C : (forall x, C |-- P x) -> C |-- Forall y, P y.
  Proof. apply bi.forall_intro. Qed.
  Lemma landL1 (P Q C : PROP) : P |-- C -> P //\\ Q |-- C.
  Proof. apply bi.and_elim_l'. Qed.
  Lemma landL2 (P Q C : PROP) : Q |-- C -> P //\\ Q |-- C.
  Proof. apply bi.and_elim_r'. Qed.
  Lemma lorR1 (P Q C : PROP) :  C |-- P -> C |-- P \\// Q.
  Proof. apply bi.or_intro_l'. Qed.
  Lemma lorR2 (P Q C : PROP) :  C |-- Q -> C |-- P \\// Q.
  Proof. apply bi.or_intro_r'. Qed.
  Lemma landR (P Q C : PROP) :  C |-- P -> C |-- Q -> C |-- P //\\ Q.
  Proof. apply bi.and_intro. Qed.
  Lemma lorL (P Q C : PROP) :  P |-- C -> Q |-- C -> P \\// Q |-- C.
  Proof. apply bi.or_elim. Qed.
  Lemma landAdj (P Q C : PROP) : C |-- (P -->> Q) -> C //\\ P |-- Q.
  Proof. apply bi.impl_elim_l'. Qed.
  Lemma limplAdj (P Q C : PROP) : C //\\ P |-- Q -> C |-- (P -->> Q).
  Proof. apply bi.impl_intro_r. Qed.

  (* Charge derivations *)
  Lemma embedPropR (p : Prop) (P : PROP) (H : p) : P |-- [! p !].
  Proof. exact: bi.pure_intro. Qed.

  Lemma wandSPI (P Q R : PROP) (HQ : P ** Q |-- R) : P |-- Q -* R.
  Proof. exact: bi.wand_intro_r. Qed.

  Lemma sepSPC (P Q : PROP) : P ** Q |-- Q ** P.
  Proof. by rewrite (comm bi_sep). Qed.

  Lemma scME (P Q R S : PROP) (HPR : P |-- R) (HQS : Q |-- S) :
    P ** Q |-- R ** S.
  Proof. by rewrite HPR HQS. Qed.

  Lemma sepSPAdj (P Q C : PROP) (HWand: C |-- P -* Q) : C ** P |-- Q.
  Proof. exact: bi.wand_elim_l'. Qed.

  Lemma embedPropExists (p : Prop) : [! p !] ⊢@{PROP} Exists x : p, ltrue.
  Proof. by rewrite -bi.pure_alt. Qed.
  Lemma embedPropExistsL (p : Prop) (P : PROP) : Exists x : p, P |-- [! p !].
  Proof. rewrite bi.pure_alt. f_equiv=>x. by apply bi.True_intro. Qed.
  (* TODO rename embedPropExists to embedPropExistsR *)
  Lemma embedPropExists' (p : Prop) : Exists x : p, True ⊣⊢@{PROP} [! p !].
  Proof. split'; [ apply embedPropExistsL | apply embedPropExists ]. Qed.

  Lemma landtrueL (a : PROP) : ltrue //\\ a -|- a.
  Proof. apply: left_id. Qed.

  Lemma bilexistssc {T} (P : PROP) (Q : T -> PROP) :
    Exists x : T, P ** Q x -|- P ** Exists y, Q y.
  Proof. apply symmetry, bi.sep_exist_l. Qed.
  Lemma wandSPAdj' (P Q C : PROP) (HSep: P ** C |-- Q) : C |-- P -* Q.
  Proof. exact: bi.wand_intro_l. Qed.

  Lemma sepSP_falseL (P : PROP) : lfalse ** P -|- lfalse.
  Proof. apply: left_absorb. Qed.

  Lemma wandSP_cancel (P Q R F : PROP) :
      R |-- P ** F ->
      (P -* Q) ** R |-- Q ** F.
  Proof. intros ->. rewrite assoc. f_equiv. apply bi.wand_elim_l. Qed.

  Lemma bilforallscR {T} (P : PROP) (Q : T -> PROP) :
    P ** (Forall y, Q y) |-- Forall x : T, P ** Q x.
  Proof. by rewrite bi.sep_forall_l. Qed.

  Lemma wandSepSPAdj (P Q R : PROP) : P ** Q |-- R <-> P |-- Q -* R.
  Proof.
    split.
    { apply bi.wand_intro_r. }
    apply bi.wand_elim_l'.
  Qed.

  Lemma wandSPAdj (P Q C : PROP) : C ** P |-- Q -> C |-- P -* Q.
  Proof. apply bi.wand_intro_r. Qed.

  Lemma bilexistsscR2 {T} (P : PROP) (f : T -> PROP):
    Exists x : T, f x ** P |-- (Exists y, f y) ** P.
  Proof. by rewrite bi.sep_exist_r. Qed.

  Lemma bilexistsscL2 {T} (P : PROP) (f : T -> PROP) :
    (Exists x, f x) ** P |-- Exists x : T, f x ** P.
  Proof. by rewrite bi.sep_exist_r. Qed.

  Lemma bilexistsscL1 {T} (P : PROP) (f : T -> PROP) :
    P ** bi_exist f |-- Exists x : T, P ** f x.
  Proof. by rewrite bi.sep_exist_l. Qed.

  Lemma wandSPL (P Q : PROP) CL CR (HP: CL |-- P) (HR: Q |-- CR) :
    (P -* Q) ** CL |-- CR.
  Proof. rewrite -HR -HP. exact: bi.wand_elim_l'. Qed.

  Lemma sepSPA1 (P Q R : PROP) : (P ** Q) ** R |-- P ** (Q ** R).
  Proof. by rewrite assoc. Qed.
  Lemma sepSPA2 (P Q R : PROP) : P ** (Q ** R) |-- (P ** Q) ** R.
  Proof. by rewrite assoc. Qed.
  Lemma sepSPA (P Q R : PROP) : (P ** Q) ** R -|- P ** (Q ** R).
  Proof. by rewrite assoc. Qed.

  Lemma wandSPE (P Q R S : PROP) (HQR: Q |-- S -* R) (HP : P |-- Q ** S) : P |-- R.
  Proof. rewrite HP. exact: bi.wand_elim_l'. Qed.

  Lemma empSPR : forall (P : PROP), P ** emp -|- P.
  Proof. apply: right_id. Qed.

  Lemma lexists_known : forall t a (P : t -> PROP),
    Exists x : t, [| x = a |] ** P x -|- P a.
  Proof.
    intros. iSplit.
    - iIntros "H". iDestruct "H" as (x) "[-> H]". subst; eauto.
    - iIntros "HP". iExists a. eauto.
  Qed.

  Lemma bilsep (P Q R : PROP) : P |-- Q -> P ** R |-- Q ** R.
  Proof. apply bi.sep_mono_l. Qed.

  Lemma bilorscDL (P Q R : PROP) : (P \\// Q) ** R -|- (P ** R) \\// (Q ** R).
  Proof.
    split'.
    + apply bi.wand_elim_l', bi.or_elim; apply bi.wand_intro_r;
      [ apply bi.or_intro_l' | apply bi.or_intro_r']; reflexivity.
    + apply bi.or_elim; apply bi.sep_mono_l;
      [ apply bi.or_intro_l' | apply bi.or_intro_r']; reflexivity.
  Qed.

  Lemma lforall_specialize {T} (x : T) (P : T -> PROP) :
    bi_forall P |-- P x.
  Proof. apply bi.forall_elim. Qed.

  Lemma sepSPAdj' (P Q C : PROP) (HWand: C |-- P -* Q) : P ** C |-- Q.
  Proof. exact: bi.wand_elim_r'. Qed.

  Lemma later_sep (P Q R : PROP) :
      (|> P) ** Q |-- R ->
      P ** Q |-- R.
  Proof. intros <-. f_equiv. apply bi.later_intro. Qed.
End with_PROP.
