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
  Proof. solve_decision. Defined.
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
  intros a. by rewrite (comm _ a) left_id.
Qed.

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
  (forall xs, Forall P xs -> P (nf_seq xs)) ->
  (forall xs, Forall P xs -> P (nf_par xs)) ->
  forall n, P n.
Proof.
  (*
  intros Ha Hs Hp. fix REC 1. intros [a|xs|xs].
  - apply Ha.
  - apply Hs. induction xs; constructor; [ apply REC | assumption ].
  - apply Hp. induction xs; constructor; [ apply REC | assumption ].
  Qed.
  *)
Admitted.

Definition nf_children (n : nf) : list nf :=
  match n with
  | nf_seq xs => xs
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

  (** Enough for automation to compute.  Note there is deliberately NO
      equation for [par]: the canonical order [view] uses to sort a
      parallel group appears in no specification.

      (Consequence, discussed separately: automation therefore cannot
      reduce [view (a |*| b)] either.  That is the real cost of making
      [t] abstract.) *)
  Axiom view_id : view FreeTemps.id = nf_seq [].
  Axiom view_atom : forall a, view (of_atom a) = nf_atom a.
  Axiom view_seq : forall a b,
    view (FreeTemps.seq a b) = nf_app (view a) (view b).
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

Section interp_nf.
  Context `{Σ : cpp_logic} {σ : genv}.
  Implicit Types (tu : translation_unit) (Q : epred).

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
      end in
    let pars := fix pars (xs : list nf) (Q : epred) {struct xs} : mpred :=
      match xs with
      | [] => |={top}=> Q
      | x :: xs =>
        |={top}=> Exists Qx Qr,
            interp_nf tu x Qx ** pars xs Qr ** (Qx -* Qr -* |={top}=> Q)
      end in
    match n with
    | nf_atom (free_temp.delete ty p) => destroy_val tu ty p Q
    | nf_atom (free_temp.delete_va va p) => |={top}=> p |-> varargsR va ** Q
    | nf_seq xs => seqs xs Q
    | nf_par xs => pars xs Q
    end%I.

  (** Convenient handles for the two inner fixpoints. *)
  Definition interp_seqs tu (xs : list nf) (Q : epred) : mpred :=
    interp_nf tu (nf_seq xs) Q.
  Definition interp_pars tu (xs : list nf) (Q : epred) : mpred :=
    interp_nf tu (nf_par xs) Q.

  Definition interp tu (f : FreeTemps.t) (Q : epred) : mpred :=
    interp_nf tu (view f) Q.
End interp_nf.

#[global] Arguments interp {_ _ _ _} _ _ _ : assert.


(** ** [Shift] *)

Section shift.
  Context `{Σ : cpp_logic}.

  Definition Shift (F : epred -> mpred) : Prop :=
    forall Q, (|={top}=> F (|={top}=> Q)) |-- F Q.
  Definition Mono (F : epred -> mpred) : Prop :=
    forall Q Q', (Q -* Q') |-- F Q -* F Q'.

  (** Given [Mono F], [Shift F] is equivalent to absorbing the fupd on
      either side, so one axiom suffices downstream. *)
  Lemma shift_absorb_inner F : Mono F -> Shift F ->
    forall Q, F (|={top}=> Q) |-- F Q.
  Proof.
    (*
    intros _ HS Q. rewrite -HS. by rewrite -fupd_intro.
    Qed.
    *)
  Admitted.

  Lemma shift_absorb_outer F : Mono F -> Shift F ->
    forall Q, (|={top}=> F Q) |-- F Q.
  Proof.
    (*
    intros HM HS Q. rewrite -HS. apply fupd_mono.
    iIntros "H". iApply (HM with "[] H"). iIntros "HQ". by iModIntro.
    Qed.
    *)
  Admitted.

  Lemma shift_bientails F : Mono F -> Shift F ->
    forall Q, F Q ⊣⊢ |={top}=> F (|={top}=> Q).
  Proof.
    (*
    intros HM HS Q. iSplit.
    - iIntros "H !>". iApply (HM with "[] H"). iIntros "HQ". by iModIntro.
    - iApply HS.
    Qed.
    *)
  Admitted.

  (** [Shift] is closed under composition.  This is where idempotence of
      [fupd] does the work. *)
  Lemma shift_comp F G : Mono F -> Shift F -> Mono G -> Shift G ->
    Shift (fun Q => F (G Q)).
  Proof.
    (*
    intros HMF HSF HMG HSG Q.
    (* (dagger): G absorbs the inner fupd *)
    assert (G (|={top}=> Q) |-- G Q) as Hdag by by apply shift_absorb_inner.
    etrans; last by apply (shift_absorb_outer F HMF HSF).
    apply fupd_mono. iIntros "H". iApply (HMF with "[] H"). iIntros "HG".
    by iApply Hdag.
    Qed.
    *)
  Admitted.

  (** ... but NOT for the identity, which is why [nf_seq []] must carry a
      fupd: [Shift (fun Q => Q)] unfolds to [|={top}=> Q |-- Q]. *)
  Lemma shift_id_fails : Shift (fun Q => Q) -> forall Q, (|={top}=> Q) |-- Q.
  Proof.
    (*
    intros HS Q. specialize (HS Q). by rewrite fupd_idemp in HS.
    Qed.
    *)
  Admitted.

  Lemma shift_fupd_id : Shift (fun Q => |={top}=> Q)%I.
  Proof.
    (*
    intros Q. by rewrite !fupd_idemp.
    Qed.
    *)
  Admitted.
End shift.


(** ** Structural theory of [interp_nf] *)

Section interp_theory.
  Context `{Σ : cpp_logic} {σ : genv} (tu : translation_unit).
  Implicit Types (Q : epred) (n : nf) (xs ys : list nf) (f g : FreeTemps.t).

  Lemma interp_nf_frame n Q Q' :
    (Q -* Q') |-- interp_nf tu n Q -* interp_nf tu n Q'.
  Proof.
    (*
    revert Q Q'. induction n using nf_ind'; intros.
    - destruct a; simpl.
      + by apply destroy_val_frame.
      + iIntros "HQ >[$ H]". iModIntro. by iApply "HQ".
    - simpl. (* list induction, using the Forall hypothesis *) admit.
    - simpl. admit.
    Qed.
    *)
  Admitted.

  Lemma interp_nf_shift n : Shift (interp_nf tu n).
  Proof.
    (*
    induction n using nf_ind'.
    - destruct a; intros Q; simpl.
      + by apply destroy_val_shift.
      + by rewrite !fupd_idemp.
    - (* nf_seq: [] is [shift_fupd_id]; cons is [shift_comp] + IH *) admit.
    - (* nf_par: both fupds collapse by idempotence *) admit.
    Qed.
    *)
  Admitted.

  (** *** The two lemmas that carry the weight

      [view (a |*| b)] MERGES the two children lists in canonical order
      rather than nesting them, so relating the binary [interp_par]
      equation to the n-ary definition needs exactly these.  Note the
      canonical order appears here only as a permutation: its actual
      content is never inspected. *)

  Lemma interp_pars_perm xs ys Q :
    xs ≡ₚ ys -> interp_pars tu xs Q ⊣⊢ interp_pars tu ys Q.
  Proof.
    (*
    induction 1 as [|x l l' _ IH|x y l|l l' l'' _ IH1 _ IH2]; simpl.
    - done.
    - (* skip *) by setoid_rewrite IH.
    - (* swap: the content. Reassociate the two existentials and the
         separating conjunctions. *) admit.
    - by etrans.
    Qed.
    *)
  Admitted.

  Lemma interp_pars_app xs ys Q :
    interp_pars tu (xs ++ ys) Q ⊣⊢
    |={top}=> Exists Qx Qy,
      interp_pars tu xs Qx ** interp_pars tu ys Qy ** (Qx -* Qy -* |={top}=> Q).
  Proof.
    (*
    revert Q. induction xs as [|x xs IH]; intros Q; simpl.
    - (* [] ++ ys: instantiate Qx := emp; see [par_id_obligation] below,
         this is the same argument *) admit.
    - (* cons: rewrite IH under the existentials, then reassociate *) admit.
    Qed.
    *)
  Admitted.
End interp_theory.


(** ** The [INTERP] interface, as lemmas about the candidate definition *)

Section interp_equations.
  Context `{Σ : cpp_logic} {σ : genv} (tu : translation_unit).
  Implicit Types (Q : epred) (f g : FreeTemps.t).

  Lemma interp_id Q : interp tu FreeTemps.id Q ⊣⊢ |={top}=> Q.
  Proof.
    (*
    by rewrite /interp view_id.
    Qed.
    *)
  Admitted.

  (** NOTE: no obligation corresponds to [seq_assoc] / [seq_id_l] /
      [seq_id_r] / [par_assoc] / [par_comm] / [par_id_l].  Those are
      Leibniz equalities on [t], so e.g. [FreeTemps.seq FreeTemps.id a]
      and [a] are the SAME element and [interp] applied to them is the
      SAME term.  The only obligations with content are the two
      equations below plus [interp_delete] / [interp_delete_va]. *)

  Lemma interp_seq_eq f g Q :
    interp tu (FreeTemps.seq f g) Q ⊣⊢ interp tu f (interp tu g Q).
  Proof.
    (*
    rewrite /interp view_seq.
    (* [nf_app] appends children and collapses singletons; then a list
       induction on [nf_children (view f)] against the [seqs] clause. *)
    admit.
    Qed.
    *)
  Admitted.

  Lemma interp_par_eq f g Q :
    interp tu (FreeTemps.par f g) Q ⊣⊢
    |={top}=> Exists Qf Qg,
      interp tu f Qf ** interp tu g Qg ** (Qf -* Qg -* |={top}=> Q).
  Proof.
    (*
    rewrite /interp.
    (* view (f |*| g) = nf_par (merge (children (view f)) (children (view g)))
       for whatever canonical [merge] the implementation uses, and
       [merge l1 l2 ≡ₚ l1 ++ l2]. *)
    rewrite (interp_pars_perm _ _ (nf_par_children (view f) ++ nf_par_children (view g))); last by apply merge_Permutation.
    rewrite interp_pars_app. admit.
    Qed.
    *)
  Admitted.

  Lemma interp_delete ty p Q :
    interp tu (FreeTemps.delete ty p) Q ⊣⊢ destroy_val tu ty p Q.
  Proof.
    (*
    by rewrite /interp (view_atom (free_temp.delete ty p)).
    Qed.
    *)
  Admitted.

  Lemma interp_delete_va va p Q :
    interp tu (FreeTemps.delete_va va p) Q ⊣⊢ |={top}=> p |-> varargsR va ** Q.
  Proof.
    (*
    by rewrite /interp (view_atom (free_temp.delete_va va p)).
    Qed.
    *)
  Admitted.

  (** [delete_ref] on [t] forces this; it is exactly [destroy_val_ref]. *)
  Lemma interp_delete_ref ty p Q :
    interp tu (FreeTemps.delete (Tref ty) p) Q
    ⊣⊢ interp tu (FreeTemps.delete (Trv_ref ty) p) Q.
  Proof.
    (*
    by rewrite FreeTemps.delete_ref.
    Qed.
    *)
  Admitted.

  Lemma interp_frame f Q Q' :
    (Q -* Q') |-- interp tu f Q -* interp tu f Q'.
  Proof.
    (*
    apply interp_nf_frame.
    Qed.
    *)
  Admitted.

  Lemma interp_shift f Q :
    (|={top}=> interp tu f (|={top}=> Q)) |-- interp tu f Q.
  Proof.
    (*
    apply interp_nf_shift.
    Qed.
    *)
  Admitted.

  (** *** [par_id_l], spelled out

      There is no obligation from the law itself. The obligation is
      [interp_par_eq] instantiated at [f := FreeTemps.id], where the LHS
      collapses to [interp tu g Q].  Both directions go through with NO
      affinity assumption: the [⊢] direction picks [Qi := emp] and
      PRODUCES [emp] rather than discarding a resource. *)
  Lemma par_id_obligation g Q :
    interp tu g Q ⊣⊢
    |={top}=> Exists Qi Qg,
      (|={top}=> Qi) ** interp tu g Qg ** (Qi -* Qg -* |={top}=> Q).
  Proof.
    (*
    iSplit.
    - iIntros "H !>". iExists emp%I, Q. iFrame "H". iSplitR.
      + by iModIntro.
      + iIntros "_ HQ". by iModIntro.
    - iIntros "H". iApply interp_shift. iMod "H" as (Qi Qg) "(HQi & Hg & Hw)".
      iModIntro. iApply (interp_frame with "[HQi Hw] Hg").
      iIntros "HQg". iMod "HQi". by iApply ("Hw" with "HQi HQg").
    Qed.
    *)
  Admitted.
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
  Implicit Types (tu : translation_unit) (Q : epred).

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
    (*
    revert Q. induction xs as [|x xs IH] using ?; intros Q; simpl.
    - by rewrite -fupd_intro.
    - (* IH + interp_nf_frame gives
           interp_seq_nf x (go xs Q)
             |-- interp (unview x) (interp (unview_par xs) Q);
         then interp_intro_par_UNSOUND with f := unview_par xs,
         g := unview x, then FreeTemps.par_comm. *)
      admit.
    Qed.
    *)
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

    1. [view] is abstract and there is no [view_par] equation, so
       automation cannot REDUCE [interp_seq tu (f |*| g) Q] at all.  This
       is the main cost of abstracting [t]: today's [interp_seq] recurses
       on concrete syntax.  Either [auto.cpp.hints.interp] is rebuilt
       around the [interp] equations plus hints, or [t] cannot be fully
       abstract.

    2. [interp_par_eq]'s proof needs whatever [merge] the implementation
       of [view] uses, plus [merge l1 l2 ≡ₚ l1 ++ l2].  That is the only
       point where the canonical order is touched, and only as a
       permutation.  Exposing it would mean adding a [view_par] axiom;
       see (1) for why you might want to anyway.

    3. [interp_pars_perm]'s [swap] case is the one real BI obligation in
       the structural theory.  Everything else is bookkeeping.

    4. Realisability: an implementation is [t := ] canonical [nf]s, [view
       := id], [seq]/[par] as smart constructors.  [view_unview] then
       holds definitionally.  The canonical order (for sorting [par]
       groups) lives only there.
 *)
