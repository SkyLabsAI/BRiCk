(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.iris.extra.proofmode.proofmode.
Require Import skylabs.lang.cpp.logic.

(** * <<goto>> through [Goto], [Kblock] and [Klabels]

Derived consequences of [wp_goto], [wp_labeled] and [wp_block]: where a
<<goto>> resumes, and which variables are destroyed on the way. Forward
jumps come first; backward jumps, which the continuation of the block
resolves ([Klabels]), are at the end. *)

Section with_cpp.
  Context `{Σ : cpp_logic} {σ : genv} (tu : translation_unit).

  #[local] Notation wp := (wp tu).
  #[local] Notation wp_block := (wp_block tu).
  #[local] Notation wp_block_head := (wp_block_head tu).

  Lemma wp_block_frame_fupd ρ ss Q :
    wp_block ρ ss Q |-- wp_block ρ ss (|={top}=> Q).
  Proof.
    iApply wp_block_frame. iIntros (rt) "H". rewrite monPred_at_fupd. by iModIntro.
  Qed.

  (** The enclosing [Kfree], [Kloop], [Kpost] and [Kswitch] pass [Goto] on;
      [Kfree] destroys its variables first. *)
  Lemma Kfree_goto free Q l : Kfree tu free Q (Goto l) = interp tu free (Q (Goto l)).
  Proof. done. Qed.
  Lemma Kloop_goto I Q l : Kloop I Q (Goto l) = Q (Goto l).
  Proof. done. Qed.
  Lemma Kpost_goto I Q l : Kpost I Q (Goto l) = Q (Goto l).
  Proof. done. Qed.
  Lemma Kswitch_goto Q l : Kswitch Q (Goto l) = Q (Goto l).
  Proof. done. Qed.
  Lemma Kloop_break I Q : Kloop I Q Break = Q Normal.
  Proof. done. Qed.
  Lemma Kpost_break I Q : Kpost I Q Break = Q Break.
  Proof. done. Qed.
  Lemma Kfree_normal free Q : Kfree tu free Q Normal = interp tu free (Q Normal).
  Proof. done. Qed.

  (** The continuation at the target of a forward jump may use an update. *)
  Lemma skipped_fupd ρ l ss (Q : Kpred) rt :
    skipped (wp_block ρ) l ss Q rt |-- skipped (wp_block ρ) l ss (|={top}=> Q) rt.
  Proof.
    iApply (skipped_frame _ _ l ss ss with "[] []"); first done.
    - iIntros "!>" (????). iApply wp_block_frame.
    - iIntros (?) "H". rewrite monPred_at_fupd. by iModIntro.
  Qed.

  (** A <<goto>> heading a block, followed by [ss]: it resumes at the suffix
      of [ss] labeled [l], or leaves the block with [Goto l]. The
      continuation at the target, [skipped], has the labels that the jump
      skips as targets; it is [Q] when the target is the next statement
      ([skipped_here]). *)
  Lemma wp_block_goto ρ l ss Q :
    ▷ match find_label id l ss with
      | Some ss' => wp_block ρ ss' (skipped (wp_block ρ) l ss Q)
      | None => Q (Goto l)
      end
    |-- wp_block ρ (Sgoto l :: ss) Q.
  Proof.
    iIntros "H". rewrite wp_block_unfold /= /wp_block_head /=. iModIntro. iNext. iModIntro.
    iApply wp_goto. iNext. rewrite Kblock_goto.
    case: (find_label id l ss) => [ss'|].
    - iApply (wp_block_frame with "[] H"). iIntros (rt). iApply skipped_fupd.
    - rewrite monPred_at_fupd. by iModIntro.
  Qed.

  (** (i) A forward <<goto>> to a later label of the same block continues
      with the labeled suffix, in the same scope; the statements in between
      are skipped. *)
  Lemma wp_block_goto_forward ρ l s ss1 ss2 Q :
    find_label id l (ss1 ++ Slabeled l s :: ss2) = Some (Slabeled l s :: ss2) ->
    ▷ wp_block ρ (Slabeled l s :: ss2)
        (skipped (wp_block ρ) l (ss1 ++ Slabeled l s :: ss2) Q)
    |-- wp_block ρ (Sgoto l :: ss1 ++ Slabeled l s :: ss2) Q.
  Proof. move=> Hf. rewrite -wp_block_goto Hf. done. Qed.

  (** The search does compute; e.g. the body of <<clamp0>> (issue #515). *)
  Example find_label_clamp0 (e0 e1 : Expr) :
    find_label id "neg" [Sreturn (Some e1); Slabeled "neg" (Sreturn (Some e0))]
    = Some [Slabeled "neg" (Sreturn (Some e0))].
  Proof. reflexivity. Qed.

  (** Statements without declarations can be skipped. *)
  Example find_label_ladder (e1 e2 e3 : Expr) :
    find_label id "res1_fail"
      [ Sexpr e1
      ; Slabeled "actions_fail" (Sexpr e2)
      ; Slabeled "res2_fail" (Sexpr e2)
      ; Slabeled "res1_fail" (Sreturn (Some e3)) ]
    = Some [Slabeled "res1_fail" (Sreturn (Some e3))].
  Proof. reflexivity. Qed.

  (** Reaching a labeled statement in sequence, without an invariant for the
      label: the statement runs as if unlabeled, and no <<goto>> may come
      back to the label. *)
  Lemma wp_block_labeled ρ l s ss Q :
    head_labels s = [] ->
    wp_block ρ (s :: ss) (Klabel [l] False Q) |-- wp_block ρ (Slabeled l s :: ss) Q.
  Proof.
    intros Hs. etrans; last by apply wp_block_label_once.
    rewrite wp_block_unfold /wp_block_head /Klabels /= Hs /=.
    destruct (stmt_decl s); first done.
    iIntros ">H !> !>"; iMod "H"; iModIntro; by iApply wp_labeled.
  Qed.

  (** A labeled declaration is run as a declaration: its variables scope
      the rest of the block. *)
  Lemma wp_block_labeled_decl ρ l ds ss Q :
    wp_block ρ (Sdecl ds :: ss) (Klabel [l] False Q)
    |-- wp_block ρ (Slabeled l (Sdecl ds) :: ss) Q.
  Proof. by apply wp_block_labeled. Qed.

  (** (ii) A <<goto>> out of a nested block that declared a variable: the
      variable is destroyed ([interp free]) before the labeled suffix runs,
      and the suffix runs in the outer region [ρ], not in [ρ']. *)
  Lemma wp_goto_out_of_block ρ d l s ss Q :
    wp_decls tu ρ [d] (fun _ρ' free => interp tu free (wp_block ρ (Slabeled l s :: ss) Q))
    |-- wp_block ρ (Sseq [Sdecl [d]; Sgoto l] :: Slabeled l s :: ss) Q.
  Proof.
    rewrite (wp_block_unfold _ ρ (Sseq _ :: _)) /= /wp_block_head /=.
    iIntros "H". iModIntro. iNext. iModIntro.
    iApply wp_seq. rewrite (wp_block_unfold _ ρ (Sdecl _ :: _)) /= /wp_block_head /=.
    iApply (wp_decls_frame with "[] H"). iIntros (ρ' free) "H".
    iModIntro. iNext. iModIntro.
    iApply wp_block_goto. iNext. rewrite find_label_nil. cbv iota beta. rewrite Kfree_goto.
    iApply (interp_frame with "[] H"). iIntros "H".
    rewrite Kblock_goto find_label_here // skipped_here. cbv iota beta.
    by iApply wp_block_frame_fupd.
  Qed.

  (** (iii) A <<goto>> out of a <<while>> body to a label after the loop:
      both the jump and the loop's normal exit continue with the same
      labeled suffix. *)
  Lemma wp_while_goto_out ρ e l s ss Q :
    ▷ wp_test tu ρ e (fun _ free => interp tu free (wp_block ρ (Slabeled l s :: ss) Q))
    |-- wp_block ρ (Swhile None e (Sgoto l) :: Slabeled l s :: ss) Q.
  Proof.
    rewrite (wp_block_unfold _ ρ (Swhile _ _ _ :: _)) /= /wp_block_head /=.
    iIntros "H". iModIntro. iNext. iModIntro.
    iApply wp_while_unroll. rewrite /while_unroll. iApply wp_if. iNext.
    iApply (wp_test_frame with "[] H"). iIntros (c free) "H".
    iApply (interp_frame with "[] H"). iIntros "H".
    destruct c.
    - iApply wp_goto. iNext. rewrite Kloop_goto.
      rewrite Kblock_goto find_label_here // skipped_here. cbv iota beta.
      by iApply wp_block_frame_fupd.
    - iApply wp_break. iNext. rewrite Kloop_break Kblock_normal.
      by iApply wp_block_frame_fupd.
  Qed.

  (** (iii') <<for (int i = ...; e; incr) goto l;>>: the loop variable [i],
      declared by the init statement, is destroyed on both exits before the
      labeled suffix runs in the outer region. *)
  Lemma wp_for_goto_out ρ d e incr l s ss Q :
    wp_decls tu ρ [d] (fun ρ' free =>
      wp_test tu ρ' e (fun _ free' =>
        interp tu free' (interp tu free (wp_block ρ (Slabeled l s :: ss) Q))))
    |-- wp_block ρ (Sfor (Some (Sdecl [d])) None (Some e) incr (Sgoto l)
                    :: Slabeled l s :: ss) Q.
  Proof.
    rewrite (wp_block_unfold _ ρ (Sfor _ _ _ _ _ :: _)) /= /wp_block_head /=.
    iIntros "H". iModIntro. iNext. iModIntro.
    iApply wp_for_init. iApply wp_seq. rewrite (wp_block_unfold _ ρ (Sdecl _ :: _)) /= /wp_block_head /=.
    iApply (wp_decls_frame with "[] H"). iIntros (ρ' free) "H".
    iModIntro. iNext. iModIntro.
    rewrite (wp_block_unfold _ ρ' (Sfor _ _ _ _ _ :: _)) /= /wp_block_head /=. iModIntro. iNext. iModIntro.
    iApply wp_for_unroll. rewrite /for_unroll /for_body_unroll.
    iApply wp_if. iNext.
    iApply (wp_test_frame with "[] H"). iIntros (c free') "H".
    iApply (interp_frame with "[] H"). iIntros "H".
    destruct c.
    - iApply wp_goto. iNext. rewrite Kpost_goto Kloop_goto.
      rewrite Kblock_goto find_label_nil. cbv iota beta.
      rewrite monPred_at_fupd Kfree_goto. iModIntro.
      iApply (interp_frame with "[] H"). iIntros "H".
      rewrite Kblock_goto find_label_here // skipped_here. cbv iota beta.
      by iApply wp_block_frame_fupd.
    - iApply wp_break. iNext. rewrite Kpost_break Kloop_break.
      rewrite Kblock_normal (wp_block_unfold _ ρ' []). iModIntro. iNext. iModIntro.
      rewrite !monPred_at_fupd Kfree_normal. iModIntro.
      iApply (interp_frame with "[] H"). iIntros "H".
      rewrite Kblock_normal.
      by iApply wp_block_frame_fupd.
  Qed.

  (** (iv) A <<goto>> whose label is not among the following statements of
      its block, up to the next declaration, leaves the block. *)
  Lemma wp_block_goto_unfound ρ l ss (Q : Kpred) :
    find_label id l ss = None ->
    ▷ Q (Goto l) |-- wp_block ρ (Sgoto l :: ss) Q.
  Proof. move=> Hf. by rewrite -wp_block_goto Hf. Qed.

  (** Backward: <<l: s; goto l;>>. The <<goto>> is the last statement, so
      nothing follows it: the forward search fails, and the jump is left to
      the continuation of the block (see [Klabel] below). *)
  Example find_label_backward l : find_label id l [] = None.
  Proof. done. Qed.

  (** Past a declaration, initialized or not: <<goto l; int x; l: ...>>. *)
  Example find_label_past_decl l ds s ss :
    find_label id l (Sdecl ds :: Slabeled l s :: ss) = None.
  Proof. done. Qed.

  (** A labeled declaration stops the search for other labels, and so does
      a declaration with attributes. *)
  Example find_label_labeled_decl l l' ds ss :
    l <> l' -> find_label id l (Slabeled l' (Sdecl ds) :: ss) = None.
  Proof. move=> H. by rewrite find_label_cons /= bool_decide_false. Qed.
  Example find_label_attr_decl l attrs ds ss :
    find_label id l (Sattr attrs (Sdecl ds) :: ss) = None.
  Proof. done. Qed.

  (** A labeled declaration is the target of its own label: at the label
      its variables are not active yet, so the jump skips nothing. *)
  Example find_label_decl_target l ds ss :
    find_label id l (Slabeled l (Sdecl ds) :: ss) = Some (Slabeled l (Sdecl ds) :: ss).
  Proof. apply find_label_here. Qed.

  (** H1, <<{ goto L; SKIP: int x; L: x = 8; }>>: the labeled declaration
      between the <<goto>> and its label stops the search. *)
  Example find_label_H1 ds s :
    find_label id "L" [Slabeled "SKIP" (Sdecl ds); Slabeled "L" s] = None.
  Proof. reflexivity. Qed.

  (** H3, <<switch (0) { SKIP: int x; case 0: x = 8; }>>: a [case] after a
      labeled declaration makes the body unsupported. *)
  Example switch_block_H3 Ldef ds sb ss :
    wp_switch_block Ldef (Slabeled "SKIP" (Sdecl ds) :: Scase sb :: ss) = None.
  Proof. done. Qed.

  (** At the function boundary [Goto] is [False]: an unfound label leaves
      only [▷ False] to prove. *)
  Lemma Kreturn_goto cv (P : ptr -> mpred) l : Kreturn cv P (Goto l) = False%I.
  Proof. done. Qed.
  Lemma Kreturn_void_goto (P : mpred) l : Kreturn_void P (Goto l) = False%I.
  Proof. done. Qed.

  (** A <<goto>> to a label that no enclosing block has reached. *)
  Lemma wp_block_goto_unreached ρ l cv P :
    ▷ False |-- wp_block ρ [Sgoto l] (Kreturn cv P).
  Proof. iIntros "H". by iApply wp_block_goto_unfound. Qed.

  (** ** Backward jumps

      A block's continuation remembers the labeled statements it has gone
      past ([Klabels], [Kagain]). *)

  (** Going past a labeled statement: from then on, a <<goto>> to its label
      runs the block from that statement again, with the continuation [Q]
      that the block had there. *)
  Lemma wp_block_labeled_unfold ρ l s ss Q :
    wp_block ρ (Slabeled l s :: ss) Q =
    wp_block_head ρ (Slabeled l s) ss
      (Kagain (l :: head_labels s) (wp ρ (Sseq (Slabeled l s :: ss))) Q).
  Proof. by rewrite wp_block_unfold. Qed.

  Lemma Kagain_goto ls (B : Kpred -> mpred) Q l :
    Kagain ls B Q (Goto l) = if is_label l ls then B Q else Q (Goto l).
  Proof. done. Qed.
  Lemma Kagain_normal ls (B : Kpred -> mpred) Q : Kagain ls B Q Normal = Q Normal.
  Proof. done. Qed.
  Lemma Kagain_return ls (B : Kpred -> mpred) Q p :
    Kagain ls B Q (ReturnVal p) = Q (ReturnVal p).
  Proof. done. Qed.
  Lemma Kagain_break ls (B : Kpred -> mpred) Q : Kagain ls B Q Break = Q Break.
  Proof. done. Qed.

  (** (v) <<l: s; ...; goto l;>>: the jump runs the block from the label
      again. *)
  Lemma wp_block_goto_again ρ l (B : Kpred -> mpred) Q :
    ▷ B Q |-- wp_block ρ [Sgoto l] (Kagain [l] B Q).
  Proof.
    iIntros "P". iApply wp_block_goto_unfound; first done.
    by rewrite Kagain_goto /= bool_decide_true.
  Qed.

  (** (vi) A forward jump keeps the labels it skips:
      <<goto B; A: eA; B: eB; ...; goto A;>>. At [B], the continuation
      knows [A]. *)
  Example skipped_label ρ (eA eB : Expr) Q :
    let ss := [Slabeled "A" (Sexpr eA); Slabeled "B" (Sexpr eB)] in
    skipped (wp_block ρ) "B" ss Q = Kagain ["A"%pstring] (wp_block ρ ss) Q.
  Proof. reflexivity. Qed.

  (** The same continuations with any [P] for the block from the label
      ([Klabel]); [wp_block_label_unroll], [wp_block_label_inv] and
      [wp_block_label_once] in [logic/stmt.v] are stated with it. *)
  Lemma Klabel_goto ls (P : mpred) Q l :
    Klabel ls P Q (Goto l) = if is_label l ls then P else Q (Goto l).
  Proof. done. Qed.
  Lemma Klabel_normal ls (P : mpred) Q : Klabel ls P Q Normal = Q Normal.
  Proof. done. Qed.

  Lemma wp_block_goto_back ρ l (P : mpred) Q :
    ▷ P |-- wp_block ρ [Sgoto l] (Klabel [l] P Q).
  Proof.
    iIntros "P". iApply wp_block_goto_unfound; first done.
    by rewrite Klabel_goto /= bool_decide_true.
  Qed.

  (** (vii) <<l: ...; T x; ...; goto l;>>: a <<goto>> back over a
      declaration destroys its variables ([interp free]) before the block
      from the label runs again; that block then runs the declaration
      again. *)
  Lemma wp_block_goto_back_over_decl ρ' free l (P : mpred) Q :
    ▷ interp tu free P |-- wp_block ρ' [Sgoto l] (Kfree tu free (Klabel [l] P Q)).
  Proof.
    iIntros "P". iApply wp_block_goto_unfound; first done.
    by rewrite Kfree_goto Klabel_goto /= bool_decide_true.
  Qed.

  (** (viii) Out of a nested block and back: the label is found by the
      continuation of the enclosing block, after the nested block's
      variables are destroyed. *)
  Lemma wp_block_goto_back_out_of_block ρ d l ss (P : mpred) Q :
    find_label id l ss = None ->
    wp_decls tu ρ [d] (fun _ρ' free => interp tu free (|={⊤}=> P))
    |-- wp_block ρ (Sseq [Sdecl [d]; Sgoto l] :: ss) (Klabel [l] P Q).
  Proof.
    intros Hf. rewrite (wp_block_unfold _ ρ (Sseq _ :: _)) /= /wp_block_head /=.
    iIntros "H". iModIntro. iNext. iModIntro.
    iApply wp_seq. rewrite (wp_block_unfold _ ρ (Sdecl _ :: _)) /= /wp_block_head /=.
    iApply (wp_decls_frame with "[] H"). iIntros (ρ' free) "H".
    iModIntro. iNext. iModIntro.
    iApply wp_block_goto. iNext. rewrite find_label_nil. cbv iota beta. rewrite Kfree_goto.
    iApply (interp_frame with "[] H"). iIntros "H".
    rewrite Kblock_goto Hf. cbv iota beta.
    by rewrite monPred_at_fupd Klabel_goto /= bool_decide_true.
  Qed.

  (** (ix) A label of another statement is not affected: the jump goes on
      to the enclosing continuation. *)
  Lemma Klabel_goto_other l l' (P : mpred) Q :
    l <> l' -> Klabel [l'] P Q (Goto l) = Q (Goto l).
  Proof. intros. by rewrite Klabel_goto /= bool_decide_false. Qed.

  (** (x) Partial correctness, as for loops: <<l: goto l;>> never
      completes, so it satisfies every continuation. The invariant is
      [emp]. *)
  Lemma wp_block_goto_self ρ l Q :
    |-- wp_block ρ [Slabeled l (Sgoto l)] Q.
  Proof.
    iApply (wp_block_label_inv tu emp%I); first done. iSplit; first done.
    iIntros "!> _". rewrite /wp_block_head /=. iModIntro. iNext. iModIntro.
    iApply wp_labeled. iApply wp_goto. iNext.
    by rewrite Kblock_goto find_label_nil monPred_at_fupd Klabel_goto /= bool_decide_true.
  Qed.

End with_cpp.
