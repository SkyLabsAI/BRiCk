(*
 * Copyright (c) 2023 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import iris.proofmode.tactics.

Require Import bluerock.iris.extra.wp_io.iris.weakestpre.
Require Import bluerock.iris.extra.wp_io.iris.adequacy.
Require Import bluerock.iris.extra.wp_io.lang.

(** * Demonstrating adequacy for a trace property.
- The trace property is [stateI : state Λ → iProp Σ] where
  [state Λ := C.(Trace) * C.(State)].
- The statement is as follows:
  + Assume we have an execution (es,σ1) →* (t2,σ2) where
    [es] and [σ1] are the initial threadpool and state, and
    [t2] and [σ2] are the resulting threadpool and state.
  + We assume [stateI] holds for [σ1], and we have proven [WP]s for [es]
  + Then we have
    * [stateI] holds for [σ2]
    * the post-condition of every thread in the resulting threadpool [t2]
      that has evaluated to a value.
    * all other threads are not stuck if we care about stuckness.
  + We can use all of that resources as well as all invariants
    (thanks to |={⊤,∅}=>) to extract a meta property [φ].


More graphically as a Hoare triple:

{ stateI σ1 ∗ [∗ list] e;Φ ∈ es;Φs, WP e @ s; ⊤ {{ Φ }} }     // pre-cond

  (es,σ1) →* (t2,σ2)

{ ∃ es' t2', ⌜ t2 = es' ++ t2' ⌝ ∗ ⌜ length es' = length es ⌝ ∗
  ⌜ ∀ e2, s = NotStuck → e2 ∈ t2 → not_stuck e2 σ2 ⌝ ∗
  stateI σ2 ∗
  ([∗ list] e;Φ ∈ es';Φs, from_option Φ True (to_val e)) ∗
  ([∗ list] v ∈ omap to_val t2', fork_post v) }               // post-cond

{ |={⊤,∅}=> ⌜ φ ⌝ }                                           // consequence


Note that the instantiation
[IrisG (λ σ _ _ _, stateI σ) fork_post (λ _, 0) (λ _ _ _ _, fupd_intro _ _)]
means that [WP] has to show that every step maintains [stateI],
and all newly forked threads have the post-condition [fork_post].
*)
Lemma wp_trace_invariance (C : Component.t) Σ `{!invGpreS Σ} s es σ1 t2 σ2 φ :
  let Λ := Component.lts_lang C in
  (∀ `{Hinv : !invGS_gen HasNoLc Σ},    (* HasNoLc : no later credits *)
    ⊢ |={⊤}=> ∃
        (stateI : state Λ → iProp Σ)
        (Φs : list (val Λ → iProp Σ))
        (fork_post : val Λ → iProp Σ),
      let _ : irisGS_gen Λ (iProp Σ) :=
          IrisG (λ σ _ _ _, stateI σ) fork_post (λ _, 0) (λ _ _ _ _, fupd_intro _ _) in
      stateI σ1 ∗
      (* WPs of all threads in the initial threadpool [es] *)
      ([∗ list] e;Φ ∈ es;Φs, WP e @ s; ⊤ {{ Φ }}) ∗
      (∀ es' t2',
        (* es' is the final state of the initial threads, t2' the rest *)
        ⌜ t2 = es' ++ t2' ⌝ -∗
        (* es' corresponds to the initial threads *)
        ⌜ length es' = length es ⌝ -∗
        (* If this is a stuck-free triple (i.e. [s = NotStuck]), then all
        threads in [t2] are not stuck *)
        ⌜ ∀ e2, s = NotStuck → e2 ∈ t2 → not_stuck e2 σ2 ⌝ -∗
        (* The state interpretation holds for [σ2] *)
        stateI σ2 -∗
        (* If the initial threads are done, their post-condition [Φ] holds *)
        ([∗ list] e;Φ ∈ es';Φs, from_option Φ True (to_val e)) -∗
        (* For all forked-off threads that are done, their postcondition
            [fork_post] holds. *)
        ([∗ list] v ∈ omap to_val t2', fork_post v) -∗
        (* Under all these assumptions, and while opening all invariants, we
        can conclude [φ] in the logic. After opening all required invariants,
        one can use [fupd_mask_subseteq] to introduce the fancy update. *)
        |={⊤,∅}=> ⌜ φ ⌝)) →
  rtc erased_step (es, σ1) (t2, σ2) →
  φ.
Proof.
  intros Λ Hwp [n [κs ?]]%erased_steps_nsteps.
  eapply (wp_strong_adequacy_gen Σ); [done| |done]=> ?.
  iMod (Hwp _) as (stateI Φs fork_post) "(Hσ & Hwp & Hφ)".
  iExists (λ σ _ _ _, stateI σ), Φs, fork_post, _ => /=.
  iIntros "{$Hσ $Hwp} !>" (e2 t2' -> ??) "Hσ Hes Ht2 /=".
  by iMod ("Hφ" with "[%//] [%//] [%//] Hσ Hes Ht2") as "$".
Qed.
