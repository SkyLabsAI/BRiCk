(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.iris.extra.proofmode.proofmode.
Require Import skylabs.lang.cpp.logic.

(** * <<goto>> through [Goto] and [Kblock]

Derived consequences of [wp_goto], [wp_labeled] and [wp_block]: where a
<<goto>> resumes, and which variables are destroyed on the way. *)

Section with_cpp.
  Context `{Σ : cpp_logic} {σ : genv} (tu : translation_unit).

  #[local] Notation wp := (wp tu).
  #[local] Notation wp_block := (wp_block tu).

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

  (** A <<goto>> heading a block, followed by [ss]: it resumes at the suffix
      of [ss] labeled [l], or leaves the block with [Goto l]. *)
  Lemma wp_block_goto ρ l ss Q :
    ▷ match find_label id l ss with
      | Some ss' => wp_block ρ ss' Q
      | None => Q (Goto l)
      end
    |-- wp_block ρ (Sgoto l :: ss) Q.
  Proof.
    iIntros "H". rewrite wp_block_unfold. iModIntro. iNext. iModIntro.
    iApply wp_goto. iNext. rewrite Kblock_goto.
    case: (find_label id l ss) => [ss'|].
    - by iApply wp_block_frame_fupd.
    - rewrite monPred_at_fupd. by iModIntro.
  Qed.

  (** (i) A forward <<goto>> to a later label of the same block continues
      with the labeled suffix, in the same scope and continuation; the
      statements in between are skipped. *)
  Lemma wp_block_goto_forward ρ l s ss1 ss2 Q :
    find_label id l (ss1 ++ Slabeled l s :: ss2) = Some (Slabeled l s :: ss2) ->
    ▷ wp_block ρ (Slabeled l s :: ss2) Q
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

  (** Reaching the labeled statement in sequence is the same as running it. *)
  Lemma wp_block_labeled ρ l s ss Q :
    wp_block ρ (s :: ss) Q |-- wp_block ρ (Slabeled l s :: ss) Q.
  Proof.
    rewrite !wp_block_unfold /=. destruct (stmt_decl s); first done.
    iIntros ">H !> !>"; iMod "H"; iModIntro; by iApply wp_labeled.
  Qed.

  (** A labeled declaration is run as a declaration: its variables scope
      the rest of the block. *)
  Lemma wp_block_labeled_decl ρ l ds ss Q :
    wp_block ρ (Slabeled l (Sdecl ds) :: ss) Q = wp_block ρ (Sdecl ds :: ss) Q.
  Proof. by rewrite !wp_block_unfold. Qed.

  (** (ii) A <<goto>> out of a nested block that declared a variable: the
      variable is destroyed ([interp free]) before the labeled suffix runs,
      and the suffix runs in the outer region [ρ], not in [ρ']. *)
  Lemma wp_goto_out_of_block ρ d l s ss Q :
    wp_decls tu ρ [d] (fun _ρ' free => interp tu free (wp_block ρ (Slabeled l s :: ss) Q))
    |-- wp_block ρ (Sseq [Sdecl [d]; Sgoto l] :: Slabeled l s :: ss) Q.
  Proof.
    rewrite (wp_block_unfold _ ρ (Sseq _ :: _)). iIntros "H". iModIntro. iNext. iModIntro.
    iApply wp_seq. rewrite (wp_block_unfold _ ρ (Sdecl _ :: _)).
    iApply (wp_decls_frame with "[] H"). iIntros (ρ' free) "H".
    iModIntro. iNext. iModIntro.
    iApply wp_block_goto. iNext. rewrite find_label_nil. cbv iota beta. rewrite Kfree_goto.
    iApply (interp_frame with "[] H"). iIntros "H".
    rewrite Kblock_goto find_label_here //. cbv iota beta.
    by iApply wp_block_frame_fupd.
  Qed.

  (** (iii) A <<goto>> out of a <<while>> body to a label after the loop:
      both the jump and the loop's normal exit continue with the same
      labeled suffix. *)
  Lemma wp_while_goto_out ρ e l s ss Q :
    ▷ wp_test tu ρ e (fun _ free => interp tu free (wp_block ρ (Slabeled l s :: ss) Q))
    |-- wp_block ρ (Swhile None e (Sgoto l) :: Slabeled l s :: ss) Q.
  Proof.
    rewrite (wp_block_unfold _ ρ (Swhile _ _ _ :: _)). iIntros "H". iModIntro. iNext. iModIntro.
    iApply wp_while_unroll. rewrite /while_unroll. iApply wp_if. iNext.
    iApply (wp_test_frame with "[] H"). iIntros (c free) "H".
    iApply (interp_frame with "[] H"). iIntros "H".
    destruct c.
    - iApply wp_goto. iNext. rewrite Kloop_goto.
      rewrite Kblock_goto find_label_here //. cbv iota beta.
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
    rewrite (wp_block_unfold _ ρ (Sfor _ _ _ _ _ :: _)). iIntros "H". iModIntro. iNext. iModIntro.
    iApply wp_for_init. iApply wp_seq. rewrite (wp_block_unfold _ ρ (Sdecl _ :: _)).
    iApply (wp_decls_frame with "[] H"). iIntros (ρ' free) "H".
    iModIntro. iNext. iModIntro.
    rewrite (wp_block_unfold _ ρ' (Sfor _ _ _ _ _ :: _)). iModIntro. iNext. iModIntro.
    iApply wp_for_unroll. rewrite /for_unroll /for_body_unroll.
    iApply wp_if. iNext.
    iApply (wp_test_frame with "[] H"). iIntros (c free') "H".
    iApply (interp_frame with "[] H"). iIntros "H".
    destruct c.
    - iApply wp_goto. iNext. rewrite Kpost_goto Kloop_goto.
      rewrite Kblock_goto find_label_nil. cbv iota beta.
      rewrite monPred_at_fupd Kfree_goto. iModIntro.
      iApply (interp_frame with "[] H"). iIntros "H".
      rewrite Kblock_goto find_label_here //. cbv iota beta.
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
      nothing follows it. *)
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

  Lemma wp_block_goto_backward ρ l cv P :
    ▷ False |-- wp_block ρ [Sgoto l] (Kreturn cv P).
  Proof. iIntros "H". by iApply wp_block_goto_unfound. Qed.

End with_cpp.
