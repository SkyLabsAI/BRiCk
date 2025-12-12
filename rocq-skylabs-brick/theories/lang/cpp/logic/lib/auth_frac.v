(**
 * Copyright (C) 2022-2025 BlueRock Security, Inc.
 * All rights reserved.
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)

Require Import iris.algebra.agree.
Require Import bluerock.iris.extra.proofmode.proofmode.
Require Import bluerock.iris.extra.bi.spec.frac_splittable.
Require Import bluerock.lang.cpp.logic.
Require Import bluerock.iris.extra.algebra.frac_auth.
Require Import bluerock.iris.extra.base_logic.own_instances.
Require Import bluerock.iris.extra.proofmode.own_obs.

Set Printing Coercions.

(**
Well-typed ghost resources:

- [afrac.auth (g : afrac.gname A) (q : Qp) (x : A) : mpred]
represents fractional ownership of ghost cell [g] currently containing
the authoritative state [x]

- [afrac.frag (g : afrac.gname A) (q : Qp) (x : A) : mpred]
represents fractional ownership of ghost cell [g] currently containing
the fragmentative state [x]
*)

(**
TODO: unify with [bluerock.algebra.frac_auth_agree].
*)
Module afrac.

  (** CMRA *)

  #[local] Notation RA A := (frac_authR (agreeR (leibnizO A))).
  Class G (A : Type) (Σ : gFunctors) : Set := G_inG : inG Σ (RA A).
  #[global] Existing Instance G_inG.
  Definition Σ (A : Type) : gFunctors := #[ GFunctor (RA A) ].
  Lemma subG {A Σ} : subG (afrac.Σ A) Σ -> G A Σ.
  Proof. solve_inG. Qed.

  (* Common usage *)
  #[global] Instance cpp_N_G `{!cpp_logic ti _Σ} : afrac.G N _Σ
    := br.ghost.frac_auth_agree_N_inG.

  (** Ghosts *)

  Definition gname (A : Type) : Set := iprop.gname.
  #[global] Instance gname_inhabited A : Inhabited (gname A) := _.
  #[global] Instance gname_eq_dec A : EqDecision (gname A) := _.
  #[global] Instance gname_countable A : Countable (gname A) := _.

  (** Predicates *)
  mlock
  Definition auth {A} {thread_info : biIndex} {Σ} `{!afrac.G A Σ}
      (g : gname A) (q : Qp) (x : A) : mpred :=
    own g (●F{q} (to_agree (A:=leibnizO A) x)).

  mlock
  Definition frag {A} {thread_info : biIndex} {Σ} `{!afrac.G A Σ}
      (g : gname A) (q : Qp) (x : A) : mpred :=
    own g (◯F{q} (to_agree (A:=leibnizO A) x)).

  Section defs.
    Context {A} {thread_info : biIndex} {Σ} `{!afrac.G A Σ}.

    #[local] Notation to_agree := (to_agree (A:=leibnizO A)).

    #[global] Instance auth_objective : Objective3 auth.
    Proof. rewrite auth.unlock. apply _. Qed.
    #[global] Instance auth_frac g : FracSplittable_1 (auth g).
    Proof. rewrite auth.unlock. solve_frac. Qed.
    #[global] Instance auth_agree g : AgreeF1 (auth g).
    Proof.
      (**
      TODO (PDS): Shouldn't need to expose [to_agree].
      *)
      rewrite auth.unlock.
      intros. rewrite -(inj_iff to_agree). apply _.
    Qed.

    #[global] Instance frag_objective : Objective3 frag.
    Proof. rewrite frag.unlock. apply _. Qed.
    #[global] Instance frag_frac g : FracSplittable_1 (frag g).
    Proof. rewrite frag.unlock. solve_frac. Qed.
    #[global] Instance frag_agree g : AgreeF1 (frag g).
    Proof.
      (**
      TODO (PDS): own_frac_auth_frag_frac_agree_L missing in
      bluerock.iris.extra.proofmode.own_obs
      *)
      rewrite frag.unlock.
      intros. iIntros "F1 F2".
      iDestruct (own_valid_2 with "F1 F2") as %Hv. iModIntro. iPureIntro.
      move: Hv. rewrite -frac_auth_frag_op frac_auth_frag_valid=>-[] _.
      by rewrite to_agree_op_valid_L.
    Qed.

    #[global] Instance auth_frag_agree g q1 q2 x1 x2 :
      Observe2 [| x1 = x2 |] (auth g q1 x1) (frag g q2 x2).
    Proof.
      (**
      TODO (PDS): Problem with [own_frac_auth_agree_L]
      *)
      rewrite auth.unlock frag.unlock.
      intros. iIntros "A F".
      iDestruct (observe_2 [| _ ≼ _ |] with "A F") as %Hinc.
      iModIntro. iPureIntro. move: Hinc.
      move/to_agree_included. by fold_leibniz.
    Qed.

    #[local] Notation OWN g x := (auth g 1 x ** frag g 1 x) (only parsing).

(*  (* Stronger allocation rules may not be needed for now. *)
    Axiom alloc_strong_dep : ∀ (f : gname A -> A) (P : gname A -> Prop),
      pred_infinite P ->
      |-- |==> Exists g, [| P g |] ** OWN g (f g).

    Axiom alloc_cofinite_dep : ∀ (f : gname A -> A) (G : gset (gname A)),
      |-- |==> Exists g, [| g ∉ G |] ** OWN g (f g).

    Axiom alloc_dep : ∀ (f : gname A -> A),
      |-- |==> Exists g, OWN g (f g).

    Axiom alloc_strong : ∀ (P : gname A -> Prop) x,
      pred_infinite P ->
      |-- |==> Exists g, [| P g |] ** OWN g x.

    Axiom alloc_cofinite : ∀ (G : gset (gname A)) x,
      |-- |==> Exists g, [| g ∉ G |] ** OWN g x.
*)

    Lemma alloc x : |-- |==> Exists g, OWN g x.
    Proof.
      rewrite auth.unlock frag.unlock.
      iMod (own_alloc (●F{1} (to_agree x) ⋅ ◯F{1} (to_agree x))) as (g) "[A F]".
      { by apply frac_auth_valid. }
      iExists g. by iFrame "A F".
    Qed.

    Lemma update g x y :
      |-- auth g 1 x -* frag g 1 x -* |==> OWN g y.
    Proof.
      rewrite auth.unlock frag.unlock.
      iIntros "A F". iMod (own_update_2 with "A F") as "[$$]"; last done.
      by apply frac_auth_update_1.
    Qed.
  End defs.

  #[global] Opaque gname.
  #[global] Hint Opaque gname auth frag : br_opacity typeclass_instances.
End afrac.
