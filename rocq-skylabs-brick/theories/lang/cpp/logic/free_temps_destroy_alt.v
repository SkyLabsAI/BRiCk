(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(** * Alternative [FreeTemps] / [interp]: abstract type, propositional laws.

    SKETCH. Never compiled. All proofs are [Admitted] with candidate scripts
    in comments.

    The idea:

    - [FreeTemps.t] is ABSTRACT and its laws are LEIBNIZ EQUALITIES ([=]),
      not a setoid ([≡]).  Consequently every function out of [t] respects
      them automatically, [with_temps.Result] can compare [_free] by [=],
      and there is no need for [canon] / [IsCanonical] / [K_ext] anywhere.

    - The quotient is built ONCE, inside the implementation of the module.
      The canonical order on pointers lives there and appears in no
      specification.

    - [interp] is the semantic eliminator.  Automation gets a second,
      concrete view [nf] to recurse on, since [interp_seq] cannot be
      defined by recursion on the quotient (it violates [par_comm]).

    This file is deliberately standalone: rather than [Require]-ing
    [destroy.v] (which would pull in the real [FreeTemps]), it takes the
    destruction primitives as a module parameter [DESTROY].  That also
    documents exactly what [interp] needs from [destroy.v].
 *)

Require Import skylabs.prelude.base.
Require Import stdpp.coPset.
Require Import stdpp.list.
Require Import skylabs.iris.extra.proofmode.proofmode.

Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.semantics.
Require Import skylabs.lang.cpp.logic.pred.
Require Import skylabs.lang.cpp.logic.heap_pred.
Require Import skylabs.lang.cpp.logic.translation_unit.

#[local] Set Primitive Projections.
#[local] Infix "|--" := bi_entails.

(** [epred] normally comes from [wp.v] / [monad.v]; inlined to keep this
    file standalone. *)
#[local] Notation epred := mpred (only parsing).

Declare Scope free_scope.
Delimit Scope free_scope with free.
Reserved Infix "|*|" (at level 31, left associativity).
Reserved Infix ">*>" (at level 30, right associativity).


(** ** Atoms *)

Module free_temp.
  Variant t : Set :=
  | delete (ty : decltype) (p : ptr)
  | delete_va (va : list (type * ptr)) (p : ptr).

  #[global] Instance t_eq_dec : EqDecision t.
  Proof.
    (*
    solve_decision.
    Defined.
    *)
  Admitted.
End free_temp.


(** ** The abstract type *)

Module Type FREE_TEMPS.
  Parameter t : Set.
  #[global] Declare Instance t_eq_dec : EqDecision t.

  Parameter id        : t.
  Parameter delete    : decltype -> ptr -> t.
  Parameter delete_va : list (type * ptr) -> ptr -> t.
  Parameter seq       : t -> t -> t.
  Parameter par       : t -> t -> t.

  (** All laws are LEIBNIZ equalities.  This is the whole point: every
      function out of [t] respects them, so nothing downstream needs to be
      [Proper] and nothing needs to carry a canonicity proof. *)
  #[global] Declare Instance seq_assoc : Assoc   (=) seq.
  #[global] Declare Instance seq_id_l  : LeftId  (=) id seq.
  #[global] Declare Instance seq_id_r  : RightId (=) id seq.
  #[global] Declare Instance par_assoc : Assoc   (=) par.
  #[global] Declare Instance par_comm  : Comm    (=) par.
  #[global] Declare Instance par_id_l  : LeftId  (=) id par.

  Axiom delete_ref : forall ty p, delete (Tref ty) p = delete (Trv_ref ty) p.
End FREE_TEMPS.

Declare Module FreeTemps : FREE_TEMPS.

Module free_temps_notations.
  Infix ">*>" := FreeTemps.seq : free_scope.
  Infix "|*|" := FreeTemps.par : free_scope.
End free_temps_notations.
Export free_temps_notations.

#[global] Notation FreeTemps := FreeTemps.t.

(** Derived, hence outside the module type. *)
#[global] Instance FreeTemps_par_id_r : RightId (=) FreeTemps.id FreeTemps.par.
Proof.
  (*
  intros a. by rewrite (comm _ a) left_id.
  Qed.
  *)
Admitted.

(** The atom embedding. *)
Definition of_atom (a : free_temp.t) : FreeTemps.t :=
  match a with
  | free_temp.delete ty p => FreeTemps.delete ty p
  | free_temp.delete_va va p => FreeTemps.delete_va va p
  end.


(** ** A concrete normal form, for automation only *)

(** [nf] is what automation recurses on.  It is NOT the definition of
    [FreeTemps.t]; [view] below picks a representative. *)
Inductive nf : Set :=
| nf_atom (a : free_temp.t)
| nf_seq  (xs : list nf)     (** run left to right *)
| nf_par  (xs : list nf)     (** any order *)
.

(** The generated [nf_ind] is too weak because of the nesting through
    [list]. *)
Lemma nf_ind' (P : nf -> Prop) :
  (forall a, P (nf_atom a)) ->
  (forall xs, List.Forall P xs -> P (nf_seq xs)) ->
  (forall xs, List.Forall P xs -> P (nf_par xs)) ->
  forall n, P n.
Proof.
  intros Ha Hs Hp. fix REC 1. intros [a|xs|xs].
  - apply Ha.
  - apply Hs. induction xs; constructor; [ apply REC | assumption ].
  - apply Hp. induction xs; constructor; [ apply REC | assumption ].
Qed.

Definition nf_children (n : nf) : list nf :=
  match n with
  | nf_seq xs => xs
  | _ => [n]
  end.

(** Children of a PARALLEL group.  Note the [nf_seq []] case: the unit is
    represented as [nf_seq []], not [nf_par []], so without it
    [nf_par_children] of the unit would be a singleton and [view_par]
    below would be false at [a = b = FreeTemps.id]. *)
Definition nf_par_children (n : nf) : list nf :=
  match n with
  | nf_par xs => xs
  | nf_seq [] => []
  | _ => [n]
  end.

Definition nf_seq' (xs : list nf) : nf :=
  match xs with
  | [x] => x
  | _ => nf_seq xs
  end.

(** Sequential composition of normal forms.  Collapses singletons so that
    [nf_seq []] is a unit on the nose. *)
Definition nf_app (a b : nf) : nf := nf_seq' (nf_children a ++ nf_children b).

(** Right inverse of [view].  Concrete, client-side; used only to STATE
    lemmas.  Note the inner [fix]: [nf] and [list nf] are not mutually
    inductive, so a top-level mutual [Fixpoint] would be rejected. *)
Fixpoint unview (n : nf) : FreeTemps.t :=
  let go := fix go (op : FreeTemps.t -> FreeTemps.t -> FreeTemps.t)
                   (xs : list nf) {struct xs} : FreeTemps.t :=
    match xs with
    | [] => FreeTemps.id
    | x :: xs => op (unview x) (go op xs)
    end in
  match n with
  | nf_atom a => of_atom a
  | nf_seq xs => go FreeTemps.seq xs
  | nf_par xs => go FreeTemps.par xs
  end.


(** ** Choosing representatives *)

Module Type FREE_TEMPS_NF.
  Parameter view : FreeTemps.t -> nf.

  (** The only law with content: [t] is a retract of [nf].  It holds
      BECAUSE the laws on [t] are Leibniz: reassociating an [nf_seq] and
      reordering an [nf_par] are equalities in [t]. *)
  Axiom view_unview : forall f, unview (view f) = f.

  Axiom view_id : view FreeTemps.id = nf_seq [].
  Axiom view_atom : forall a, view (of_atom a) = nf_atom a.
  Axiom view_seq : forall a b,
    view (FreeTemps.seq a b) = nf_app (view a) (view b).

  (** [par] is exposed only UP TO PERMUTATION: [view] returns some list
      that is a permutation of the flattening.  The canonical order the
      implementation uses to pick that list appears nowhere.

      Stated via [nf_par_children] rather than as [view (a |*| b) =
      nf_par xs], because the latter is false at [a = b = FreeTemps.id]:
      [par id id = id] and [view id = nf_seq []], which is not an
      [nf_par] node.

      This is enough for the semantic theory ([interp_par_eq] below).  It
      is NOT enough for automation, which needs to reduce [view (a |*|
      b)] to a concrete list -- see the closing notes. *)
  Axiom view_par : forall a b,
    nf_par_children (view (FreeTemps.par a b))
    ≡ₚ nf_par_children (view a) ++ nf_par_children (view b).
End FREE_TEMPS_NF.

Declare Module FreeTempsNF : FREE_TEMPS_NF.
Export FreeTempsNF.


(** ** What [interp] needs from [destroy.v] *)

Module Type DESTROY.
  Parameter destroy_val : forall `{Σ : cpp_logic} {σ : genv},
    translation_unit -> type -> ptr -> epred -> mpred.
  Parameter wp_destroy_val : forall `{Σ : cpp_logic} {σ : genv},
    translation_unit -> type_qualifiers -> type -> ptr -> epred -> mpred.

  Section axioms.
    Context `{Σ : cpp_logic} {σ : genv}.
    Implicit Types (tu : translation_unit) (Q : epred).

    Axiom destroy_val_frame : forall tu ty p Q Q',
      (Q -* Q') |-- destroy_val tu ty p Q -* destroy_val tu ty p Q'.
    Axiom destroy_val_shift : forall tu ty p Q,
      (|={top}=> destroy_val tu ty p (|={top}=> Q)) |-- destroy_val tu ty p Q.
    Axiom destroy_val_ref : forall tu ty p Q,
      destroy_val tu (Tref ty) p Q ⊣⊢ destroy_val tu (Trv_ref ty) p Q.
    Axiom destroy_val_wp_destroy_val : forall tu ty p Q,
      wp_destroy_val tu QM ty p Q |-- destroy_val tu ty p Q.
  End axioms.
End DESTROY.

Declare Module Destroy : DESTROY.
Export Destroy.


(** ** The semantic eliminator *)
Implicit Types (tu : translation_unit).

Section interp_nf.
  Context `{Σ : cpp_logic} {σ : genv}.
  Implicit Types (Q : epred).

  Definition bi_par K1 K2 Q : mpred :=
    |={top}=> Exists Q1 Q2,
      K1 Q1 ** K2 Q2 ** (Q1 ** Q2 -* |={top}=> Q).

  (** NOTE on the fancy updates.  They are FORCED, not decorative: see
      [Shift] below.  [Shift] fails for the identity function, so the
      [nf_seq []] leaf must be [|={top}=> Q] rather than [Q].  Likewise the
      [nf_par] clause needs a [fupd] at each end.

      NOTE the parallel case is the binary clause iterated over the list,
      rather than a [big_sepL2], because the guard checker cannot see
      through [big_opL] to know that [x] is a subterm of [xs]. *)
  Fixpoint interp_nf tu (n : nf) (Q : epred) {struct n} : mpred :=
    let seqs := fix seqs (xs : list nf) (Q : epred) {struct xs} : mpred :=
      match xs with
      | [] => |={top}=> Q
      | x :: xs => interp_nf tu x (seqs xs Q)
      end%I in
    let pars := fix pars (xs : list nf) (Q : epred) {struct xs} : mpred :=
      match xs with
      | [] => |={top}=> Q
      | x :: xs =>
        bi_par (interp_nf tu x) (pars xs) Q
        (* |={top}=> Exists Qx Qr, *)
        (*     interp_nf tu x Qx ** pars xs Qr ** (Qx -* Qr -* |={top}=> Q) *)
      end%I in
    match n with
    | nf_atom (free_temp.delete ty p) => destroy_val tu ty p Q
    | nf_atom (free_temp.delete_va va p) => |={top}=> p |-> varargsR va ** Q
    | nf_seq xs => seqs xs Q
    | nf_par xs => pars xs Q
    end%I.

  Definition interp tu (f : FreeTemps.t) (Q : epred) : mpred :=
    interp_nf tu (view f) Q.

  Lemma interp_seqs_nil tu Q :
    interp_nf tu (nf_seq []) Q = (|={top}=> Q)%I.
  Proof. done. Qed.

  Lemma interp_seqs_cons tu Q x xs :
    interp_nf tu (nf_seq (x :: xs)) Q =
    interp_nf tu x (interp_nf tu (nf_seq xs) Q).
  Proof. done. Qed.

  Lemma interp_pars_nil tu :
    interp_nf tu (nf_par []) = fupd top top.
  Proof. done. Qed.

  Lemma interp_pars_cons tu x xs :
    interp_nf tu (nf_par (x :: xs)) =
      bi_par (interp_nf tu x) (interp_nf tu (nf_par xs)).
  Proof. done. Qed.
End interp_nf.

#[global] Arguments interp {_ _ _ _} _ _ _ : assert.

(** Convenient handles for the two inner fixpoints. *)
Notation interp_seqs tu xs :=
  (interp_nf tu (nf_seq xs)).

Notation interp_pars tu xs :=
  (interp_nf tu (nf_par xs)).


(** ** [Shift] *)

Section shift.
  Context `{Σ : cpp_logic}.

  Definition Shift (F : epred -> mpred) : Prop :=
    forall Q, (|={top}=> F (|={top}=> Q)%I) |-- F Q.
  Definition Mono (F : epred -> mpred) : Prop :=
    forall Q Q', (Q -* Q') |-- F Q -* F Q'.

  (** Given [Mono F], [Shift F] is equivalent to absorbing the fupd on
      either side, so one axiom suffices downstream. *)
  Lemma shift_absorb_inner F : Mono F -> Shift F ->
    forall Q, F (|={top}=> Q)%I |-- F Q.
  Proof.
    iIntros (_ HS Q) "H".
    Fail rewrite -HS.
    rewrite -(HS Q).
    (* iApply HS. *)
    by iModIntro.
  Qed.

  Lemma shift_absorb_outer F : Mono F -> Shift F ->
    forall Q, (|={top}=> F Q) |-- F Q.
  Proof.
    intros HM HS Q.
    Fail rewrite -HS.
    Fail rewrite -(HS Q).
    rewrite -{2}(HS Q).
    apply fupd_mono.
    iIntros "H". iApply (HM with "[] H"). iIntros "HQ". by iModIntro.
  Qed.

  Lemma shift_bientails F : Mono F -> Shift F ->
    forall Q, F Q ⊣⊢ |={top}=> F (|={top}=> Q).
  Proof.
    intros HM HS Q. iSplit.
    - iIntros "H !>". iApply (HM with "[] H"). iIntros "HQ". by iModIntro.
    - iApply HS.
  Qed.

  (** [Shift] is closed under composition.  This is where idempotence of
      [fupd] does the work. *)
  Lemma shift_comp F G : Mono F -> Shift F -> Mono G -> Shift G ->
    Shift (fun Q => F (G Q)).
  Proof.
    intros HMF HSF HMG HSG Q.
    (* (dagger): G absorbs the inner fupd *)
    assert (G (|={top}=> Q) |-- G Q)%I as Hdag by by apply shift_absorb_inner.
    etrans; last by apply (shift_absorb_outer F HMF HSF).
    apply fupd_mono. iIntros "H". iApply (HMF with "[] H"). iIntros "HG".
    by iApply Hdag.
  Qed.

  Implicit Type (Q : mpred).

  (** ... but NOT for the identity, which is why [nf_seq []] must carry a
      fupd: [Shift (fun Q => Q)] unfolds to [|={top}=> Q |-- Q]. *)
  Lemma shift_id_fails : Shift (fun Q => Q) -> forall Q, (|={top}=> Q) |-- Q.
  Proof.
    intros HS Q. specialize (HS Q). by rewrite fupd_idemp in HS.
  Qed.

  Lemma shift_fupd_id : Shift (fun Q => |={top}=> Q)%I.
  Proof.
    intros Q. by rewrite !fupd_idemp.
  Qed.
End shift.


(** ** Structural theory of [interp_nf] *)

Section interp_theory.
  Context `{Σ : cpp_logic} {σ : genv} (tu : translation_unit).
  Implicit Types (Q : epred) (n : nf) (xs ys : list nf) (f g : FreeTemps.t).

  Lemma interp_nf_frame n : Mono (interp_nf tu n).
  Proof.
    elim /nf_ind': n => [a|xs IH|xs IH] Q Q'.
    - destruct a; simpl.
      + by apply destroy_val_frame.
      + iIntros "HQ >[$ H]". iModIntro. by iApply "HQ".
    - induction xs as [|x xs]; rewrite !(interp_seqs_nil, interp_seqs_cons).
      { iIntros "W >Q !>". by iApply "W". }
      inv IH as [|?? Hx Hxs]; iIntros "W X".
      iApply (Hx with "[-X] X").
      iApply (IHxs Hxs with "W").
    - induction xs as [|x xs]; rewrite !(interp_pars_nil, interp_pars_cons) /bi_par.
      { iIntros "W >Q !>". by iApply "W". }
      inv IH as [|?? Hx Hxs]; iIntros "W >(%Q1 & %Q2 & xQ1 & xsQ2 & W') !>".
      iExists Q1, Q2; iFrame; iIntros.
      iApply ("W" with "(W' [$])").
  Qed.

  Lemma interp_nf_shift n : Shift (interp_nf tu n).
  Proof.
    rewrite /Shift; induction n using nf_ind'; intros Q.
    - destruct a; simpl.
      + by apply destroy_val_shift.
      + rewrite !fupd_idemp.
        by iIntros ">[? >?]"; iFrame.
    - elim: xs H Q => [|x xs IHxs] H Q; rewrite !(interp_seqs_nil, interp_seqs_cons).
      { by rewrite shift_fupd_id. }
      inv H as [|?? Hx Hxs].
      iApply shift_comp.
      all: try apply: interp_nf_frame.
      { exact: Hx. }
      intro. apply (IHxs Hxs).
    - elim: xs H Q => [|x xs IHxs] H Q; rewrite !(interp_pars_nil, interp_pars_cons) /bi_par.
      { by rewrite shift_fupd_id. }
      rewrite !fupd_idemp. by setoid_rewrite fupd_idemp.
  Qed.

  (** *** Binary parallel composition, abstracted

<<<<<<< HEAD
      Factoring this out reduces all the fiddly existential/wand
      reassociation to three lemmas about [pars_bin], after which the
      n-ary theory is bookkeeping. *)
=======
      [view (a |*| b)] MERGES the two children lists in canonical order
      rather than nesting them, so relating the binary [interp_par]
      equation to the n-ary definition needs exactly these.  Note the
      canonical order appears here only as a permutation: its actual
      content is never inspected. *)
  (* About bi_par. *)
  Lemma bi_par_comm_1 (K1 K2 K3 : mpred -> mpred) (Q : mpred) :
    bi_par K1 (bi_par K2 K3) Q |-- bi_par K2 (bi_par K1 K3) Q.
  Proof.
    rewrite /bi_par.
    iIntros ">(%Q1 & %Q2 & K1 & >(%Q0 & %Q3 & K2 & K3 & W1) & W2) !>".
    iExists Q0; iFrame "K2".
    iExists (Q1 ** Q3).
    iSplitR "W1 W2". {
      iIntros "!>".
      iExists Q1, Q3; iFrame. by iIntros; iFrame.
    }
    iIntros "(? & Q1 & ?)".
    iApply ("W2" with "[>- $Q1]").
    iApply "W1"; iFrame.
  Qed.

  Lemma bi_par_comm (K1 K2 K3 : mpred -> mpred) (Q : mpred) :
    bi_par K1 (bi_par K2 K3) Q -|- bi_par K2 (bi_par K1 K3) Q.
  Proof.
    iSplit; iApply bi_par_comm_1.
  Qed.

  Lemma bi_par_assoc K1 K2 K3 Q :
    bi_par K1 (bi_par K2 K3) Q -|- bi_par (bi_par K1 K2) K3 Q.
  Proof.
    rewrite /bi_par; split'. {
      iIntros ">(%Q1 & %Q4 & K1 & >(%Q2 & %Q3 & K2 & K3 & W4) & W) !>".
      iExists (Q1 ** Q2), Q3; iFrame "K3".
      iSplitL "K1 K2". { iIntros "!>". iFrame. by iIntros "$". }
      iIntros "((Q1 & Q2) & Q3)". iApply ("W" with "[>- $Q1]").
      iApply "W4"; iFrame.
    }
    iIntros ">(%Q4 & %Q3 & >(%Q1 & %Q2 & K1 & K2 & W4) & K3 & W) !>".
    iExists Q1, (Q2 ** Q3); iFrame "K1".
    iSplitL "K2 K3". { iIntros "!>". iFrame. by iIntros "$". }
    iIntros "(Q1 & Q2 & Q3)". iApply ("W" with "[>- $Q3]").
    iApply "W4"; iFrame.
  Qed.
>>>>>>> b42623301 (First pass on agent sketch)

  Definition pars_bin (F G : epred -> mpred) (Q : epred) : mpred :=
    (|={top}=> Exists Qx Qy, F Qx ** G Qy ** (Qx -* Qy -* |={top}=> Q))%I.

  #[global] Instance pars_bin_proper :
    Proper (pointwise_relation _ (⊣⊢) ==> pointwise_relation _ (⊣⊢) ==> eq ==> (⊣⊢)) pars_bin.
  Proof.
<<<<<<< HEAD
    (*
    intros F F' HF G G' HG Q ? <-. rewrite /pars_bin. by repeat f_equiv.
    Qed.
    *)
  Admitted.

  Lemma pars_bin_comm F G Q : pars_bin F G Q ⊣⊢ pars_bin G F Q.
  Proof.
    (*
    rewrite /pars_bin. iSplit; iIntros ">H"; iDestruct "H" as (Qx Qy) "(HF & HG & Hw)";
      iModIntro; iExists Qy, Qx; iFrame "HF HG"; iIntros "H1 H2";
      by iApply ("Hw" with "H2 H1").
    Qed.
    *)
  Admitted.

  (** The unit is [fun Q => |={top}=> Q], NOT the identity -- see [Shift].
      This generalises [par_id_obligation]; [Mono]/[Shift] are what make
      the [⊣] direction go through, and NO affinity is needed because the
      [⊢] direction PRODUCES [emp] rather than discarding a resource. *)
  Lemma pars_bin_unit_r F : Mono F -> Shift F ->
    forall Q, pars_bin F (fun Q => |={top}=> Q)%I Q ⊣⊢ F Q.
  Proof.
    (*
    intros HM HS Q. rewrite /pars_bin. iSplit.
    - iIntros ">H". iDestruct "H" as (Qx Qy) "(HF & HQy & Hw)".
      iApply HS. iModIntro. iApply (HM with "[HQy Hw] HF").
      iIntros "HQx". iMod "HQy". by iApply ("Hw" with "HQx HQy").
    - iIntros "H !>". iExists Q, emp%I. iFrame "H". iSplitR.
      + by iModIntro.
      + iIntros "HQ _". by iModIntro.
    Qed.
    *)
  Admitted.

  Lemma pars_bin_unit_l F : Mono F -> Shift F ->
    forall Q, pars_bin (fun Q => |={top}=> Q)%I F Q ⊣⊢ F Q.
  Proof.
    (*
    intros HM HS Q. by rewrite pars_bin_comm pars_bin_unit_r.
    Qed.
    *)
  Admitted.

  Lemma pars_bin_assoc F G H Q :
    pars_bin (pars_bin F G) H Q ⊣⊢ pars_bin F (pars_bin G H) Q.
  Proof.
    (*
    rewrite /pars_bin. iSplit.
    - iIntros ">H". iDestruct "H" as (Qxy Qz) "(>HFG & HH & Hw)".
      iDestruct "HFG" as (Qx Qy) "(HF & HG & Hw')".
      iModIntro. iExists Qx, (Qy ** Qz)%I. iFrame "HF". iSplitL "HG HH".
      + iModIntro. iExists Qy, Qz. iFrame "HG HH". iIntros "H1 H2 !>". iFrame.
      + iIntros "HQx [HQy HQz]". iMod ("Hw'" with "HQx HQy") as "HQxy".
        by iApply ("Hw" with "HQxy HQz").
    - (* symmetric *) admit.
    Qed.
    *)
  Admitted.

  (** *** The n-ary theory *)

  (** Both hold by [simpl] on the inner fixpoint. *)
  Lemma interp_pars_nil Q : interp_pars tu [] Q = (|={top}=> Q)%I.
  Proof. (* reflexivity. Qed. *) Admitted.

  Lemma interp_pars_cons x xs Q :
    interp_pars tu (x :: xs) Q = pars_bin (interp_nf tu x) (interp_pars tu xs) Q.
  Proof. (* reflexivity. Qed. *) Admitted.

  Lemma interp_pars_singleton n Q : interp_pars tu [n] Q ⊣⊢ interp_nf tu n Q.
  Proof.
    (*
    rewrite interp_pars_cons interp_pars_nil.
    apply pars_bin_unit_r; [ apply interp_nf_frame | apply interp_nf_shift ].
    Qed.
    *)
  Admitted.

  Lemma interp_pars_app xs ys Q :
    interp_pars tu (xs ++ ys) Q
    ⊣⊢ pars_bin (interp_pars tu xs) (interp_pars tu ys) Q.
  Proof.
    (*
    revert Q. induction xs as [|x xs IH]; intros Q.
    - rewrite /= interp_pars_nil.
      symmetry. apply pars_bin_unit_l;
        [ apply interp_nf_frame | apply interp_nf_shift ].
    - rewrite -app_comm_cons !interp_pars_cons.
      setoid_rewrite IH. by rewrite pars_bin_assoc.
    Qed.
    *)
  Admitted.

  (** The canonical order enters ONLY here, and only as a permutation:
      its content is never inspected. *)
  Lemma interp_pars_perm xs ys Q :
    xs ≡ₚ ys -> interp_pars tu xs Q ⊣⊢ interp_pars tu ys Q.
  Proof.
    (*
    intros Hp. revert Q. induction Hp as [|x l l' _ IH|x y l|l l' l'' _ IH1 _ IH2];
      intros Q.
    - done.
    - rewrite !interp_pars_cons. by setoid_rewrite IH.
    - rewrite !interp_pars_cons.
      rewrite -!pars_bin_assoc. by rewrite (pars_bin_comm (interp_nf tu x)).
    - by rewrite IH1 IH2.
    Qed.
    *)
  Admitted.

  (** Bridge: any [nf] is its own singleton parallel group.  Needed
      because [view (a |*| b)] is not necessarily an [nf_par] node (it
      collapses when a side is the unit). *)
  Lemma interp_nf_pars n Q :
    interp_nf tu n Q ⊣⊢ interp_pars tu (nf_par_children n) Q.
  Proof.
    (*
    destruct n as [a|xs|xs]; simpl.
    - by rewrite interp_pars_singleton.
    - destruct xs as [|x xs].
      + by rewrite interp_pars_nil.
      + by rewrite interp_pars_singleton.
    - done.
    Qed.
    *)
  Admitted.
=======
    move: Q => /[swap].
    elim => [//|x {}xs xs' _ IH|x y {}xs|{}xs {}ys zs _ IH1 _ IH2] Q; rewrite ?(interp_pars_nil, interp_pars_cons).
    - rewrite /bi_par. by setoid_rewrite IH.
    - by rewrite bi_par_comm.
    - by rewrite IH1 IH2.
  Qed.

  Lemma bi_par_fupd K Q : Mono K -> Shift K ->
    bi_par (fupd top top) K Q -|- K Q.
  Proof.
    rewrite /Mono /Shift /bi_par. intros M S. iSplit.
    - iIntros "H". iApply S. iMod "H" as (Qi Qg) "(HQi & Hg & Hw)".
      iModIntro. iApply (M with "[HQi Hw] Hg").
      iIntros "HQg". iMod "HQi". iApply ("Hw" with "[$]").
    - iIntros "H !>". iExists emp, Q. iFrame "H". iSplitR.
      + by iModIntro.
      + by iIntros "[_ $]".
  Qed.

  Lemma bi_par_fupd_interp_nf Q n :
    bi_par (fupd top top) (interp_nf tu n) Q -|- interp_nf tu n Q.
  Proof.
    apply bi_par_fupd. { apply interp_nf_frame. }
    apply interp_nf_shift.
  Qed.

  (** *** [par_id_l], spelled out

      There is no obligation from the law itself. The obligation is
      [interp_par_eq] instantiated at [f := FreeTemps.id], where the LHS
      collapses to [interp tu g Q].  Both directions go through with NO
      affinity assumption: the [⊢] direction picks [Qi := emp] and
      PRODUCES [emp] rather than discarding a resource. *)
  Lemma par_id_obligation g Q :
    interp tu g Q ⊣⊢
    |={top}=> Exists (Qi Qg : mpred),
      (|={top}=> Qi) ** interp tu g Qg ** (Qi ** Qg -* |={top}=> Q).
  Proof.
    by rewrite /interp -{1}bi_par_fupd_interp_nf /bi_par.
  Qed.

  Lemma interp_pars_app xs ys Q :
    interp_pars tu (xs ++ ys) Q ⊣⊢ bi_par (interp_pars tu xs) (interp_pars tu ys) Q.
  Proof.
    elim: xs Q => [|x xs IH] Q.
    { by rewrite left_id_L interp_pars_nil bi_par_fupd_interp_nf. }
    rewrite -app_comm_cons !interp_pars_cons -bi_par_assoc.
    by rewrite /bi_par; setoid_rewrite IH.
  Qed.
>>>>>>> b42623301 (First pass on agent sketch)
End interp_theory.


(** ** The [INTERP] interface, as lemmas about the candidate definition *)

Section interp_equations.
  Context `{Σ : cpp_logic} {σ : genv} (tu : translation_unit).
  Implicit Types (Q : epred) (f g : FreeTemps.t).

  Lemma interp_id Q : interp tu FreeTemps.id Q ⊣⊢ |={top}=> Q.
  Proof. by rewrite /interp view_id. Qed.

  (** NOTE: no obligation corresponds to [seq_assoc] / [seq_id_l] /
      [seq_id_r] / [par_assoc] / [par_comm] / [par_id_l].  Those are
      Leibniz equalities on [t], so e.g. [FreeTemps.seq FreeTemps.id a]
      and [a] are the SAME element and [interp] applied to them is the
      SAME term.  The only obligations with content are the two
      equations below plus [interp_delete] / [interp_delete_va]. *)

  Lemma interp_seq_eq f g Q :
    interp tu (FreeTemps.seq f g) Q ⊣⊢ interp tu f (interp tu g Q).
  Proof.
    rewrite /interp view_seq.
    (* [nf_app] appends children and collapses singletons; then a list
       induction on [nf_children (view f)] against the [seqs] clause. *)
    admit.
  Admitted.

  (** The equation is literally [pars_bin (interp tu f) (interp tu g) Q];
      spelled out here to match the shape [destroy.v] uses today. *)
  Lemma interp_par_eq f g Q :
    interp tu (FreeTemps.par f g) Q ⊣⊢
      bi_par (interp tu f) (interp tu g) Q.
  Proof.
<<<<<<< HEAD
    (*
    (* Chain:
         interp (f |*| g) Q
       = interp_nf (view (f |*| g)) Q
      -|- interp_pars (nf_par_children (view (f |*| g))) Q     [interp_nf_pars]
      -|- interp_pars (nf_par_children (view f)
                       ++ nf_par_children (view g)) Q          [view_par, perm]
      -|- pars_bin (interp_pars (nf_par_children (view f)))
                   (interp_pars (nf_par_children (view g))) Q  [interp_pars_app]
      -|- pars_bin (interp tu f) (interp tu g) Q               [interp_nf_pars, back]
       = the RHS, by definition of pars_bin.
       The canonical order is touched once, as [view_par]'s permutation. *)
    rewrite /interp.
    rewrite interp_nf_pars.
    rewrite (interp_pars_perm _ _ _ (view_par f g)).
    rewrite interp_pars_app.
    rewrite -(interp_nf_pars (view f)) -(interp_nf_pars (view g)).
    (* [pars_bin] is now definitionally the RHS; if [rewrite] leaves it
       folded, finish with: *)
    by rewrite /pars_bin.
    Qed.
    *)
=======
    rewrite /interp.
    (* view (f |*| g) = nf_par (merge (children (view f)) (children (view g)))
       for whatever canonical [merge] the implementation uses, and
       [merge l1 l2 ≡ₚ l1 ++ l2]. *)
    (* erewrite (interp_pars_perm _ [view _] _). last by apply merge_Permutation. *)
    (* interp_pars *)
    (* rewrite view_par. *)
    (* rewrite (interp_pars_perm _ _ (nf_par_children (view f) ++ nf_par_children (view g))); last by apply merge_Permutation. *)
    (* rewrite interp_pars_app. admit. *)
    (* Qed. *)
>>>>>>> b42623301 (First pass on agent sketch)
  Admitted.

  Lemma interp_delete ty p Q :
    interp tu (FreeTemps.delete ty p) Q ⊣⊢ destroy_val tu ty p Q.
  Proof. by rewrite /interp (view_atom (free_temp.delete ty p)). Qed.

  Lemma interp_delete_va va p Q :
    interp tu (FreeTemps.delete_va va p) Q ⊣⊢ |={top}=> p |-> varargsR va ** Q.
  Proof. by rewrite /interp (view_atom (free_temp.delete_va va p)). Qed.

  (** [delete_ref] on [t] forces this; it is exactly [destroy_val_ref]. *)
  Lemma interp_delete_ref ty p Q :
    interp tu (FreeTemps.delete (Tref ty) p) Q
    ⊣⊢ interp tu (FreeTemps.delete (Trv_ref ty) p) Q.
  Proof. by rewrite FreeTemps.delete_ref. Qed.

  Lemma interp_frame f Q Q' :
    (Q -* Q') |-- interp tu f Q -* interp tu f Q'.
  Proof. apply interp_nf_frame. Qed.

  Lemma interp_shift f Q :
    (|={top}=> interp tu f (|={top}=> Q)) |-- interp tu f Q.
  Proof. apply interp_nf_shift. Qed.
End interp_equations.


(** ** The automation eliminator

    A DIFFERENT function on the same [nf], matching today's
    [auto.cpp.hints.interp.interp_seq]: it sequentialises [nf_par].

    This is why [nf] has to exist at all.  As a fold on [t] with carrier
    [epred -> mpred], [a_seq F G := F ∘ G] and [a_par F G := G ∘ F], the
    algebra satisfies [seq_assoc], both [seq] units, [par_assoc] and both
    [par] units definitionally -- but NOT [par_comm], since reverse
    composition is not commutative.  Sequentialising [par] is choosing a
    representative, and a choice function cannot be defined by recursion
    on the quotient. *)

Section interp_seq_nf.
  Context `{Σ : cpp_logic} {σ : genv}.
  Implicit Types (Q : epred).

  Fixpoint interp_seq_nf tu (n : nf) (Q : epred) {struct n} : mpred :=
    let go := fix go (xs : list nf) (Q : epred) {struct xs} : mpred :=
      match xs with
      | [] => Q
      | x :: xs => interp_seq_nf tu x (go xs Q)
      end in
    match n with
    | nf_atom (free_temp.delete ty p) => wp_destroy_val tu QM ty p Q
    | nf_atom (free_temp.delete_va va p) => p |-> varargsR va ** Q
    | nf_seq xs => go xs Q
    | nf_par xs => go xs Q     (** the heuristic *)
    end%I.

  Definition interp_seq tu (f : FreeTemps.t) (Q : epred) : mpred :=
    interp_seq_nf tu (view f) Q.
End interp_seq_nf.

Section interp_seq_theory.
  Context `{Σ : cpp_logic} {σ : genv} (tu : translation_unit).
  Implicit Types (Q : epred).

  (** n-ary form of [interp_intro_par_UNSOUND].  Derivable from the binary
      one by induction; still unsound, but now that is the ONLY place the
      unsoundness enters. *)
  Axiom interp_intro_par_UNSOUND : forall f g Q,
    interp tu g (interp tu f Q) |-- interp tu (FreeTemps.par f g) Q.

  Lemma interp_intro_pars_UNSOUND xs Q :
    interp_seq_nf tu (nf_par xs) Q |-- interp_nf tu (nf_par xs) Q.
  Proof.
    revert Q. induction xs as [|x xs IH]; intros Q; simpl.
    - by rewrite -fupd_intro.
    - (* IH + interp_nf_frame gives
           interp_seq_nf x (go xs Q)
             |-- interp (unview x) (interp (unview_par xs) Q);
         then interp_intro_par_UNSOUND with f := unview_par xs,
         g := unview x, then FreeTemps.par_comm. *)
      admit.
  Admitted.

  Lemma interp_seq_nf_interp n Q :
    interp_seq_nf tu n Q |-- interp_nf tu n Q.
  Proof.
    (*
    revert Q. induction n using nf_ind'; intros Q.
    - destruct a; simpl.
      + by apply destroy_val_wp_destroy_val.
      + iIntros "[$ $]".
    - (* nf_seq: list induction + interp_nf_frame *) admit.
    - by apply interp_intro_pars_UNSOUND.
    Qed.
    *)
  Admitted.

  Lemma interp_seq_interp f Q : interp_seq tu f Q |-- interp tu f Q.
  Proof.
    (*
    apply interp_seq_nf_interp.
    Qed.
    *)
  Admitted.
End interp_seq_theory.


(** ** Open questions / known gaps

    1. [view_par] exposes the parallel group only up to permutation,
       which is exactly enough for [interp_par_eq] and keeps the
       canonical order out of every specification.  But it is NOT enough
       for automation: [interp_seq tu (f |*| g) Q] still cannot be
       REDUCED, because [view (f |*| g)] is only characterised up to
       [≡ₚ].  Today's [interp_seq] recurses on concrete syntax, so
       either [auto.cpp.hints.interp] is rebuilt around the [interp]
       equations plus hints, or [t] cannot be fully abstract.  This is
       the open question that decides whether the whole approach is
       viable.

    2. All the existential/wand reassociation is concentrated in
       [pars_bin_assoc] and [pars_bin_comm].  [pars_bin_assoc]'s second
       direction is left [admit]ted (it is symmetric to the first).
       Everything n-ary is then bookkeeping.

    3. [pars_bin]'s unit is [fun Q => |={top}=> Q], not the identity.
       This is forced: [Shift] fails for the identity, so [nf_seq []] has
       to carry a fupd.  Every fupd in today's [interp_body] is forced
       the same way.

    4. Realisability: an implementation is [t := ] canonical [nf]s, [view
       := id], [seq]/[par] as smart constructors.  [view_unview] then
       holds definitionally.  The canonical order (for sorting [par]
       groups) lives only there.
 *)
