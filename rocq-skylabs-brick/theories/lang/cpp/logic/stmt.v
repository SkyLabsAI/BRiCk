(*
 * Copyright (c) 2020-2023 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.iris.extra.proofmode.proofmode.

Require Import skylabs.iris.extra.bi.atomic_commit.
Require Import skylabs.iris.extra.bi.spec.exclusive.

Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.semantics.
Require Import skylabs.lang.cpp.logic.pred.
Require Import skylabs.lang.cpp.logic.path_pred.
Require Import skylabs.lang.cpp.logic.heap_pred.
Require Import skylabs.lang.cpp.logic.destroy.
Require Import skylabs.lang.cpp.logic.wp.
Require Import skylabs.lang.cpp.logic.initializers.
Require Import skylabs.iris.extra.bi.errors.

Module Type Stmt.
  #[local] Arguments wp_test [_ _ _ _] _ _ _.

  (** weakest pre-condition for statements
   *)
  Section with_resolver.
    Context `{Σ : cpp_logic} {σ : genv}.
    Variable (tu : translation_unit).

    #[local] Notation wp := (wp tu).
    #[local] Notation interp := (interp tu).
    #[local] Notation wp_initialize := (wp_initialize tu).
    #[local] Notation default_initialize := (default_initialize tu).

    Implicit Types Q : Kpred.

    Definition Kseq_inner (Q : Kpred -> mpred) (k : Kpred) (rt : ReturnType) : mpred :=
      match rt with
      | Normal => Q k
      | rt => k rt
      end.
    #[global] Arguments Kseq_inner _ _ !rt /.

    Definition Kseq (Q : Kpred -> mpred) (k : Kpred) : Kpred :=
      KP $ Kseq_inner Q k.
    #[global] Hint Opaque Kseq : typeclass_instances.

    Lemma Kseq_frame (Q1 Q2 : Kpred -> mpred) (k1 k2 : Kpred) (rt : ReturnType) :
      ((Forall rt : ReturnType, k1 rt -* k2 rt) -* Q1 k1 -* Q2 k2) |--
      (Forall rt : ReturnType, k1 rt -* k2 rt) -*
      Kseq Q1 k1 rt -* Kseq Q2 k2 rt.
    Proof.
      iIntros "HQ Hk". destruct rt; cbn; try iExact "Hk".
      by iApply "HQ".
    Qed.

    Definition Kfree (free : FreeTemp) : Kpred -> Kpred :=
      Kat_exit (interp free).

    Lemma Kfree_frame free Q Q' rt :
      Q rt -* Q' rt |-- Kfree free Q rt -* Kfree free Q' rt.
    Proof.
      iIntros "X". iApply Kat_exit_frame => //.
      iIntros (??) "H"; by iApply interp_frame.
    Qed.

    (** * Attribute Evaluation *)

    (* NOTE: this assumes that attributes do not have a semantic
       impact on the code. There are some attributes, e.g. <<OMP::for>>
       that have a semantic impact on the code, but Clang chooses to
       represent these using different AST nodes. *)
    Axiom wp_attr : forall ρ attrs s Q,
        wp ρ s Q |-- wp ρ (Sattr attrs s) Q.

    (** * Expression Evaluation *)

    Axiom wp_expr : forall ρ e Q,
        |> wp_discard tu ρ e (fun free => interp free (Q Normal))
        |-- wp ρ (Sexpr e) Q.

    (** * Declarations *)

    (* This definition performs allocation of local variables.
     *)
    Definition wp_decl_var (ρ : region) (x : ident) (ty : type) (init : option Expr)
               (k : region -> FreeTemp -> epred)
      : mpred :=
      Forall (addr : ptr),
        let finish frees :=
            interp frees (k (Rbind x addr ρ) (FreeTemps.delete ty addr))
        in
        match init with
        | Some init =>
            (* In C++ (and in C) the scope of the name begins immediately after
               the name is declared, before it is initialized.
               See <https://eel.is/c++draft/basic.scope.pdecl#1>
             *)
            wp_initialize (Rbind x addr ρ) ty addr init finish
        | None => default_initialize ty addr finish
        end.

    Lemma wp_decl_var_frame : forall x ρ init ty (k k' : region -> FreeTemps -> epred),
        Forall a (b : _), k a b -* k' a b
        |-- wp_decl_var ρ x ty init k -* wp_decl_var ρ x ty init k'.
    Proof.
      rewrite /wp_decl_var; intros.
      iIntros "X Y" (addr); iSpecialize ("Y" $! addr); iRevert "Y".
      case_match;
        [ iApply wp_initialize_frame; [done|]
        | iApply default_initialize_frame; [done|] ];
        iIntros (?); iApply interp_frame; iApply "X".
    Qed.

    (* the variables declared in a destructing declaration must have initializers *)
    Record destructuring_declaration (d : VarDecl) : Prop := {}.

    Fixpoint wp_destructure (ρ_init : region) (ds : list BindingDecl)
      (ρ : region) (k : region -> FreeTemps -> epred) (free : FreeTemps) {struct ds} : mpred :=
      match ds with
      | nil => k ρ free
      | d :: ds =>
          let fix wp_binding (d : BindingDecl) : mpred :=
            match d with
            | Bvar x ty init =>
                Forall p, wp_initialize ρ_init ty p init (fun free' => wp_destructure ρ_init ds (Rbind x p ρ) k (FreeTemps.delete ty p >*> free' >*> free)%free)
            | Bbind x _ init =>
                wp_glval tu ρ_init init (fun p free' => wp_destructure ρ_init ds (Rbind x p ρ) k (free' >*> free)%free)
            | BLocInfo _ d => wp_binding d
            end
          in wp_binding d
      end.

    Lemma wp_destructure_frame : forall ds ρ ρ_init m m' free,
        Forall a b, m a b -* m' a b
        |-- wp_destructure ρ_init ds ρ m free -* wp_destructure ρ_init ds ρ m' free.
    Proof.
      induction ds as [|d ds IHds]; simpl; intros.
      { iIntros "X"; iApply "X". }
      induction d; simpl.
      { iIntros "X H" (p); iSpecialize ("H" $! p); iRevert "H".
        iApply wp_initialize_frame => //.
        iIntros (?); by iApply IHds. }
      { iIntros "X H". iRevert "H"; iApply wp_glval_frame => //.
        iIntros (??). by iApply IHds. }
      { exact IHd. }
    Qed.

    (* [static_initialized gn b] is ownership of the initialization
       state of the global [gn].

       We use atomic commits to access this state which requires the C++
       abstract machine to have access to some state (e.g. the boolean used
       in the implementation) to determine the current state. This is simple
       using an [auth]/[frag] construction where the abstract machine owns
       the [auth] and [static_initialized] is the [frag].
     *)
    Variant init_state : Set :=
    | uninitialized | initializing | initialized.
    Parameter static_initialized : forall {σ : genv}, globname -> init_state -> mpred.
    #[global] Declare Instance init_state_timeless {σ : genv} : Timeless2 static_initialized.
    #[global] Declare Instance init_state_uninitialized_excl {σ : genv} nm : Exclusive0 (static_initialized nm uninitialized).
    #[global] Declare Instance init_state_initializing_excl {σ : genv} nm : Exclusive0 (static_initialized nm initializing).
    #[global] Declare Instance init_state_initialized_pers {σ : genv} nm : Persistent (static_initialized nm initialized).
    #[global] Declare Instance init_state_initialized_affine {σ : genv} nm : Affine (static_initialized nm initialized).

    (* This instance allows proving
       [[
       static_initialized nm initializing ** static_initialized nm i |-- False
       ]]
       indirectly through [init_state_initiailized_excl]
     *)
    #[global] Declare Instance init_state_agree nm : Agree1 (static_initialized nm).


    Fixpoint wp_decl (ρ : region) (d : VarDecl) (k : region -> FreeTemps -> epred) {struct d} : mpred :=
      match d with
      | Dvar x ty init => wp_decl_var ρ x ty init k
      | Ddecompose init x ds =>
        (* NOTE: the **declaration type** of the initializer *)
        let common_type := decltype_of_expr init in
        Forall common_p : ptr,
        (* unlike for variables (see [wp_decl_var]), the variables in a structured binding
           are not available in the initializer.
           See <https://eel.is/c++draft/dcl.struct.bind#2>
         *)
        wp_initialize ρ common_type common_p init (fun free =>
           (* NOTE: [free] is used to deallocate temporaries generated in the execution of [init].
              It should not matter if it is destroyed immediately or after the destructuring occurs.
            *)
           wp_destructure (Rbind x common_p ρ) ds ρ (fun ρ f => interp free $ k ρ f) (FreeTemps.delete common_type common_p))
      | Dinit ts nm ty init =>
        let k := k ρ in (* scope does not change *)
        let do_init k :=
            match init with
            | None => default_initialize ty (_global nm) k
            | Some init => wp_initialize ρ ty (_global nm) init k
            end
        in
        if ts then
          let Mouter := ⊤ ∖ ↑pred_ns in
          let Minner := ∅ in
          (* 1. atomically check the initialization state, mark it
                [initializing] if it is currently [uninitialized].
             2. perform initialization (non-atomically)
             3. mark the state [initialized].
           *)
          AC1 << ∀ i, static_initialized nm i >> @ Mouter , Minner
              << match i with
                 | uninitialized => static_initialized nm initializing
                 | initializing =>
                     (* the C++ thread waits unless the state is either [initialized] or [uninitialized]. *)
                     False
                 | _ => static_initialized nm i
                 end
               , COMM match i with
                      | uninitialized =>
                          letI* free := do_init in
                          AC1 << ∀ i, static_initialized nm i >> @ Mouter , Minner
                              << [| i = initializing |] **
                                 static_initialized nm initialized
                               , COMM k free >>
                      | _ => k FreeTemps.id
                      end >>
        else
          Exists i, static_initialized nm i **
          if i is uninitialized then
            do_init $ fun free => static_initialized nm initialized -* k free
          else k FreeTemps.id
      | DLocInfo _ d => wp_decl ρ d k
      end%I.

    Lemma wp_decl_frame : forall ds ρ m m',
        Forall a b, m a b -* m' a b
        |-- wp_decl ρ ds m -* wp_decl ρ ds m'.
    Proof.
      induction ds; simpl; intros.
      { iIntros "X". iApply wp_decl_var_frame. iIntros (?); eauto. }
      { iIntros "A X" (p); iSpecialize ("X" $! p); iRevert "X".
        iApply wp_initialize_frame; [done|].
        iIntros (?). iApply wp_destructure_frame.
        iIntros (??); iApply interp_frame; eauto. }
      { case_match.
        { iIntros "F H".
          iApply (atomic_commit1_ppost_wand with "H").
          iIntros "!>" ([ | | ]); eauto.
          case_match;
            first [ iApply wp_initialize_frame
                  | iApply default_initialize_frame ] => //;
            iIntros (?) "H";
            iApply (atomic_commit1_ppost_wand with "H");
            iIntros "!>" (?); eauto. }
        { iIntros "F H".
          iDestruct "H" as (i) "H"; iExists i.
          iDestruct "H" as "[$ H]".
          case_match; try solve [ iApply "F"; eauto ].
          iRevert "H".
          case_match;
            first [ iApply wp_initialize_frame
                  | iApply default_initialize_frame ] => //;
            iIntros (?) "X Y"; iApply "F"; iApply "X"; done. } }
      { apply IHds. }
    Qed.

    (* [wp_decls ρ_init ds ρ K] evalutes the declarations in [ds]
    using the environment [ρ_init] and binds the declarations
    in [ρ] (which it passes to [K]) *)
    Fixpoint wp_decls_def (ρ : region) (ds : list VarDecl)
      (k : region -> FreeTemps -> epred) : mpred :=
      match ds with
      | nil => |={⊤}=> k ρ FreeTemps.id
      | d :: ds => |={⊤}=> |> wp_decl ρ d (fun ρ free => wp_decls_def ρ ds (fun ρ free' => k ρ (free' >*> free)%free))
      end.
    Definition wp_decls_aux : seal (@wp_decls_def). Proof. by eexists. Qed.
    Definition wp_decls := wp_decls_aux.(unseal).
    Definition wp_decls_eq : @wp_decls = _ := wp_decls_aux.(seal_eq).

    Lemma wp_decls_frame : forall ds ρ (Q Q' : region -> FreeTemps -> epred),
        Forall a (b : _), Q a b -* Q' a b
        |-- wp_decls ρ ds Q -* wp_decls ρ ds Q'.
    Proof.
      rewrite wp_decls_eq.
      induction ds; simpl; intros.
      - iIntros "a H". iMod "H". iIntros "!>". iRevert "H".
        iApply "a".
      - iIntros "a b". iMod "b". iIntros "!> !>". iRevert "b".
        iApply wp_decl_frame.
        iIntros (??). iApply IHds. iIntros (??) "X". by iApply "a".
    Qed.

    Lemma wp_decls_shift ρ ds (Q : region -> FreeTemps -> epred) :
      (|={top}=> wp_decls ρ ds (funI ρ free => |={top}=> Q ρ free)) |--
      wp_decls ρ ds Q.
    Proof.
      rewrite wp_decls_eq /=.
      elim: ds ρ Q => [|d ds IH] ρ Q /=.
      - by iIntros ">>H".
      - iIntros ">>H !> !>".
        iApply (wp_decl_frame with "[] H").
        iIntros (??) "H". iApply IH. by iModIntro.
    Qed.

    Lemma fupd_wp_decls ρ ds (Q : region -> FreeTemps -> epred) :
      (|={top}=> wp_decls ρ ds Q) |-- wp_decls ρ ds Q.
    Proof.
      rewrite -{2}wp_decls_shift; f_equiv.
      iApply wp_decls_frame. by iIntros "* $".
    Qed.

    Lemma wp_decls_fupd ρ ds (Q : region -> FreeTemps -> epred) :
      wp_decls ρ ds (funI ρ free => |={top}=> Q ρ free) |--
      wp_decls ρ ds Q.
    Proof. iIntros "H". iApply wp_decls_shift. by iModIntro. Qed.

    (** * Blocks *)

    Fixpoint wp_block_stmt (ρ : region) (s : Stmt)
        (body : region -> Kpred -> mpred) (Q : Kpred) : mpred :=
      match s with
      | Sdecl ds =>
          wp_decls ρ ds (funI ρ free =>
                           |={top}=> |> |={top}=> body ρ (Kfree free Q))
      | SLocInfo _ s => wp_block_stmt ρ s body Q
      | _ =>
          |={top}=> |> |={top}=> wp ρ s (Kseq (body ρ) (|={top}=> Q))
      end.

    Fixpoint wp_block_def (ρ : region) (ss : list Stmt) (Q : Kpred) : mpred :=
      match ss with
      | nil => |={top}=> |> |={top}=> Q Normal
      | s :: ss => wp_block_stmt ρ s (fun ρ Q => wp_block_def ρ ss Q) Q
      end.
    Definition wp_block_aux : seal (@wp_block_def). Proof. by eexists. Qed.
    Definition wp_block := wp_block_aux.(unseal).
    Definition wp_block_eq : @wp_block = _ := wp_block_aux.(seal_eq).

    (* Show [wp_block] satisfies the fixpoint equation. *)
    Lemma wp_block_unfold (ρ : region) (ss : list Stmt) (Q : Kpred) :
      wp_block ρ ss Q =
      (match ss with
      | nil => |={top}=> |> |={top}=> Q Normal
      | s :: ss => wp_block_stmt ρ s (fun ρ Q => wp_block ρ ss Q) Q
      end)%I.
    Proof. rewrite !wp_block_eq; by destruct ss. Qed.

    Lemma wp_block_loc_info ρ li s ss Q :
      wp_block ρ (SLocInfo li s :: ss) Q = wp_block ρ (s :: ss) Q.
    Proof. by rewrite !wp_block_unfold. Qed.

    Lemma wp_block_frame : forall ss ρ (Q Q' : Kpred),
        (Forall rt, Q rt -* Q' rt)
        |-- wp_block ρ ss Q -* wp_block ρ ss Q'.
    Proof.
      induction ss as [|s ss]; simpl; intros. {
        rewrite !wp_block_unfold.
        by iIntros "Hcnt HQ"; iMod "HQ"; iApply "Hcnt".
      }
      assert ((Forall rt, Q rt -* Q' rt) |--
        (|={⊤}▷=> wp ρ s (Kseq (wp_block ρ ss) (|={⊤}=> Q))) -*
        (|={⊤}▷=> wp ρ s (Kseq (wp_block ρ ss) (|={⊤}=> Q')))) as Himpl.
      { iIntros "X >H !> !>". iMod "H"; iModIntro.
        iApply (wp_frame with "[X] H"); first by reflexivity.
        iAssert (Forall rt, (|={⊤}=> Q) rt -* (|={⊤}=> Q') rt)%I with "[X]" as "X". {
          setoid_rewrite monPred_at_fupd.
          iIntros (?) ">H !>". by iApply "X".
        }
        iIntros (rt); destruct rt => //=.
        by iApply IHss. }
      rewrite !wp_block_unfold /=.
      iIntros "X". induction s; simpl; try by iApply (Himpl with "X").
      - iApply wp_decls_frame.
        iIntros (??) ">H !> !>". iMod "H"; iModIntro.
        iApply (IHss with "[X] H"); iIntros (?).
        iApply Kfree_frame. iApply "X".
      - apply IHs.
        rewrite !(@wp_loc_info _ _ _ _ tu ρ l s) in Himpl. exact Himpl.
    Qed.

    Lemma wp_block_shift ρ ds (Q : Kpred) :
      (|={top}=> wp_block ρ ds (|={top}=> Q)) |--
      wp_block ρ ds Q.
    Proof.
      elim: ds ρ Q => [|d ds IH] ρ Q /=.
      - rewrite !wp_block_unfold /=.
        iIntros ">>H !> !> /=". by iMod "H" as ">$".
      - assert (
        (|={⊤}=> |={⊤}▷=> wp ρ d (Kseq (wp_block ρ ds) (|={⊤}=> |={⊤}=> Q))) |--
        |={⊤}▷=> wp ρ d (Kseq (wp_block ρ ds) (|={⊤}=> Q))) as W. {
          iIntros ">>H !> !> !>". iMod "H". iApply (wp_frame with "[] H"). done.
          iIntros (?) "H".
          iApply (Kseq_frame with "[] [] H").
          { iApply wp_block_frame. }
          iIntros (?) "H". by rewrite fupd_idemp.
      }
      rewrite !wp_block_unfold /=.
      induction d; simpl; try by iApply W.
      + iIntros "H". iApply wp_decls_shift. iMod "H"; iModIntro.
        iApply (wp_decls_frame with "[] H"); iIntros (??) ">H !> !> !> !>".
        iApply IH. iMod "H"; iModIntro.
        iApply (wp_block_frame with "[] H"); iIntros (rt) "H !> /=".
        rewrite monPred_at_fupd. iApply (interp_shift with "H").
      + apply IHd.
        rewrite !(@wp_loc_info _ _ _ _ tu ρ l d) in W. exact W.
    Qed.

    Lemma fupd_wp_block ρ ds Q :
      (|={top}=> wp_block ρ ds Q) |-- wp_block ρ ds Q.
    Proof.
      rewrite -{2}wp_block_shift; f_equiv.
      iApply wp_block_frame. by iIntros "* $".
    Qed.

    Lemma wp_block_fupd ρ ds Q :
      wp_block ρ ds (|={top}=> Q) |--
      wp_block ρ ds Q.
    Proof. iIntros "H". iApply wp_block_shift. by iModIntro. Qed.

    #[global] Instance wp_block_mono ρ ls : Proper (bi_entails ==> bi_entails) (wp_block ρ ls).
    Proof.
      move => x y [Hxy].
      apply bi.wand_entails.
      rewrite -wp_block_frame.
      apply bi.forall_intro => ?.
      by apply bi.entails_wand.
    Qed.
    #[global] Instance wp_block_flip_mono ρ ls : Proper (flip bi_entails ==> flip bi_entails) (wp_block ρ ls).
    Proof. solve_proper. Qed.
    #[global] Instance wp_block_proper ρ ls : Proper (equiv ==> equiv) (wp_block ρ ls).
    Proof.
      move => x y /bi.equiv_entails []
           => /wp_block_mono Hxy
           => /wp_block_mono Hyx.
      by split'.
    Qed.

    (* proof mode *)
    #[global] Instance elim_modal_fupd_wp_block p P ρ body Q :
      ElimModal True p false (|={top}=> P) P (wp_block ρ body Q) (wp_block ρ body Q).
    Proof.
      rewrite /ElimModal. rewrite bi.intuitionistically_if_elim/=.
      by rewrite fupd_frame_r bi.wand_elim_r fupd_wp_block.
    Qed.
    #[global] Instance elim_modal_bupd_wp_lval p P Q ρ body :
      ElimModal True p false (|==> P) P (wp_block ρ body Q) (wp_block ρ body Q).
    Proof.
      rewrite /ElimModal (bupd_fupd top). exact: elim_modal_fupd_wp_block.
    Qed.
    #[global] Instance add_modal_fupd_wp_lval P Q ρ body :
      AddModal (|={top}=> P) P (wp_block ρ body Q).
    Proof.
      rewrite/AddModal. by rewrite fupd_frame_r bi.wand_elim_r fupd_wp_block.
    Qed.

    Axiom wp_seq : forall ρ Q ss,
        wp_block ρ ss Q |-- wp ρ (Sseq ss) Q.

    (** * <<if>> *)

    Definition pre_stmt (init : option Stmt) (decl : option VarDecl) : option (list Stmt) :=
      match init , decl with
      | None , None      => None
      | Some s , None    => Some [s]
      | None , Some vd   => Some [Sdecl [vd]]
      | Some s , Some vd => Some [s; Sdecl [vd]]
      end.

    Axiom wp_if : forall ρ init decl e thn els Q,
        match pre_stmt init decl with
        | None =>
        |> letI* c , free := Unfold WPE.wp_test (wp_test tu ρ e) in
           interp free $
             if c
             then wp ρ thn Q
             else wp ρ els Q
        | Some ss =>
            wp ρ (Sseq (ss ++ [Sif None None e thn els])) Q
        end
      |-- wp ρ (Sif init decl e thn els) Q.

    (* The loops are phrased using 1-step unfoldings and invariant rules are
       proved using Löb induction.

       C++ (and C) allow optimizing away certain infinite loops,
       e.g. <<while (1);>> can be optimized to <<;>>.
       These loop rules are not sound for use with compilations that use this
       optimization.
     *)

    (* loop with invariant `I` *)
    Definition Kloop_inner (I : mpred) (Q : Kpred) (rt : ReturnType) : mpred :=
      match rt with
      | Break => Q Normal
      | Normal | Continue => I
      | rt => Q rt
      end.
    #[global] Arguments Kloop_inner _ _ !rt /.

    Definition Kloop (I : mpred) (Q : Kpred) : Kpred :=
      KP $ Kloop_inner I Q.

    (** * <<while>> *)

    Definition while_unroll ρ decl test body :=
      wp ρ (Sif None decl test body Sbreak).

    Axiom wp_while_unroll : forall ρ decl test body Q,
            while_unroll ρ decl test body (Kloop (|> wp ρ (Swhile decl test body) Q) Q)
        |-- wp ρ (Swhile decl test body) Q.

    Theorem wp_while_inv I : forall ρ decl test body Q,
        I |-- while_unroll ρ decl test body (Kloop (|> I) Q) ->
        I |-- wp ρ (Swhile decl test body) Q.
    Proof.
      intros.
      iLöb as "IH".
      iIntros "I".
      iApply wp_while_unroll.
      rewrite {2}H.
      iRevert "I"; iApply wp_frame; first reflexivity.
      iIntros (rt) "K"; destruct rt; simpl; eauto.
      - iApply "IH"; eauto.
      - iApply "IH"; eauto.
    Qed.

    (* for backwards compatibility *)
    Lemma wp_while_inv_nolater I : forall ρ decl test body Q,
        I |-- Unfold while_unroll (while_unroll ρ decl test body (Kloop I Q)) ->
        I |-- wp ρ (Swhile decl test body) Q.
    Proof.
      intros.
      iApply wp_while_inv.
      rewrite {1}H.
      iApply wp_frame; first reflexivity.
      iIntros (rt); destruct rt; simpl; eauto.
    Qed.

    (** * <<for>> *)
    Definition Kpost_inner I Q (rt : ReturnType) :=
      match rt with
      | Normal | Continue => I
      | _ => Q rt
      end.
    #[global] Arguments Kpost_inner _ _ !rt /.

    Definition Kpost I Q :=
      KP $ Kpost_inner I Q.

    Definition for_unroll ρ test incr body (Q : Kpred) :=
      let Kinc :=
        Kpost (match incr with
               | None => Q Normal
               | Some incr => wp_discard tu ρ incr (fun free => interp free $ Q Normal)
               end) Q
      in
      match test with
      | None => wp ρ body
      | Some test => wp ρ (Sif None None test body Sbreak)
      end Kinc.

    Axiom wp_for_unroll : forall ρ test incr body Q,
            for_unroll ρ test incr body (Kloop (|> wp ρ (Sfor None test incr body) Q) Q)
        |-- wp ρ (Sfor None test incr body) Q.

    Theorem wp_for_inv I : forall ρ test incr body Q,
        I |-- for_unroll ρ test incr body (Kloop (|> I) Q) ->
        I |-- wp ρ (Sfor None test incr body) Q.
    Proof.
      intros.
      iLöb as "IH".
      iIntros "I".
      iApply wp_for_unroll.
      rewrite {2}H /for_unroll.
      iRevert "I"; case_match; (iApply wp_frame; first reflexivity).
      all: iIntros (rt); destruct rt; simpl; eauto.
      all: case_match.
      all: try (iApply wp_discard_frame; first reflexivity;
                iIntros (?); iApply interp_frame;
                iIntros "I !>"; iApply "IH"; eauto).
      all: iIntros "I !>"; iApply "IH"; eauto.
    Qed.

    Lemma wp_for_inv_nolater I : forall ρ test incr body Q,
        I |-- Unfold for_unroll (for_unroll ρ test incr body (Kloop (|> I) Q)) ->
        I |-- wp ρ (Sfor None test incr body) Q.
    Proof.
      intros.
      apply wp_for_inv.
      rewrite {1}H /for_unroll/=.
      iIntros "X"; iRevert "X".
      case_match; simpl.
      all: iApply wp_frame; first reflexivity.
      all: iIntros (rt); destruct rt; simpl; eauto.
      all: case_match.
      all: try (iApply wp_discard_frame; first reflexivity;
                iIntros (?); iApply interp_frame).
    Qed.

    (**
       `for (init; test; incr) body` desugars to `{ init; for (; test; incr) body }`
     *)
    Axiom wp_for_init : forall ρ init test incr b Q,
            wp ρ (Sseq (init :: Sfor None test incr b :: nil)) Q
        |-- wp ρ (Sfor (Some init) test incr b) Q.

    (** * <<do>> *)

    Definition do_unroll ρ body test (Q : Kpred) :=
      wp ρ body (Kpost (Unfold WPE.wp_test (wp_test tu ρ test (fun c free => interp free $ if c then Q Continue else Q Break))) Q).

    Axiom wp_do_unroll : forall ρ body test Q,
            do_unroll ρ body test (Kloop (|> wp ρ (Sdo body test) Q) Q)
        |-- wp ρ (Sdo body test) Q.

    Theorem wp_do_inv I : forall ρ body test Q,
        I |-- do_unroll ρ body test (Kloop (|> I) Q) ->
        I |-- wp ρ (Sdo body test) Q.
    Proof.
      intros.
      iLöb as "IH".
      iIntros "I".
      iApply wp_do_unroll.
      rewrite {2}H /do_unroll.
      iRevert "I"; iApply wp_frame; first reflexivity.
      iIntros (rt) "K"; destruct rt; simpl; eauto.
      { iRevert "K"; iApply wp_test_frame; iIntros (??).
        iApply interp_frame; case_match; eauto.
        iIntros "? !>"; iApply "IH"; eauto. }
      { iRevert "K"; iApply wp_test_frame; iIntros (??).
        iApply interp_frame; case_match; eauto.
        iIntros "? !>"; iApply "IH"; eauto. }
    Qed.

    Lemma wp_do_inv_nolater I : forall ρ body test Q,
        I |-- Unfold do_unroll (do_unroll ρ body test (Kloop I Q)) ->
        I |-- wp ρ (Sdo body test) Q.
    Proof.
      intros.
      apply wp_do_inv.
      rewrite {1}H /do_unroll.
      iIntros "X"; iRevert "X".
      iApply wp_frame; first reflexivity.
      iIntros (rt); destruct rt; simpl; eauto.
      all: iApply wp_test_frame; iIntros (??).
      all: iApply interp_frame; case_match; eauto.
    Qed.

    (** * <<return>> *)

    (* the semantics of return is like an initialization
     * expression.
     *)
    Axiom wp_return_void : forall ρ Q,
        get_return_type ρ = Tvoid ->
        |> Q ReturnVoid |-- wp ρ (Sreturn None) Q.

    Axiom wp_return : forall ρ e (Q : Kpred),
          (let rty := get_return_type ρ in
           Forall p, wp_initialize ρ rty p e (fun frees =>
                                         interp frees (|> Q (ReturnVal p))))
       |-- wp ρ (Sreturn (Some e)) Q.

    Axiom wp_return_frame : forall ρ rv (Q Q' : Kpred),
        match rv with
        | None => Q ReturnVoid -* Q' ReturnVoid
        | Some _ =>
          (* NOTE unsound in the presence of exceptions *)
          Forall v, Q (ReturnVal v) -* Q' (ReturnVal v)
        end |-- wp ρ (Sreturn rv) Q -* wp ρ (Sreturn rv) Q'.

    (** * <<break>> *)

    Axiom wp_break : forall ρ Q,
        |> Q Break |-- wp ρ Sbreak Q.
    Axiom wp_break_frame : forall ρ (Q Q' : Kpred),
        Q Break -* Q' Break |-- wp ρ Sbreak Q -* wp ρ Sbreak Q'.

    (** * <<continue>> *)
    Axiom wp_continue : forall ρ Q,
        |> Q Continue |-- wp ρ Scontinue Q.
    Axiom wp_continue_frame : forall ρ (Q Q' : Kpred),
        Q Continue -* Q' Continue |-- wp ρ Scontinue Q -* wp ρ Scontinue Q'.

    (** * <<switch>> *)

    (* compute the [Prop] that is known if this switch branch is taken *)
    Definition wp_switch_branch (s : SwitchBranch) (v : Z) : Prop :=
      match s with
      | Exact i => v = i
      | Range low high => low <= v <= high
      end%Z.

    (* This performs a syntactic check on [s] to ensure that there are no [case] or [default]
       statements. This is used to avoid missing one of these statements which would compromise
       the soundness of [wp_switch_block]
     *)
    Fixpoint no_case (s : Stmt) : bool :=
      match s with
      | Sseq ls => forallb no_case ls
      | Sdecl _ => true
      | Sif _ _ _ a b
      | Sif_consteval a b => no_case a && no_case b
      | Swhile _ _ s => no_case s
      | Sfor _ _ _ s => no_case s
      | Sdo s _ => no_case s
      | Sattr _ s => no_case s
      | Sswitch _ _ _ _ => true
      | Scase _
      | Sdefault => false
      | Sbreak
      | Scontinue
      | Sreturn _
      | Sexpr _
      | Sasm _ _ _ _ _ => true
      | Slabeled _ s => no_case s
      | Sgoto _ => true
      | Sunsupported _ => false
      | SLocInfo _ s => no_case s
      end.

    Fixpoint get_case (s : Stmt) : option SwitchBranch :=
      match s with
      | Scase sb => Some sb
      | SLocInfo _ s => get_case s
      | _ => None
      end.

    Fixpoint get_cases (ls : list Stmt) : list SwitchBranch :=
      match ls with
      | s :: ls =>
          match get_case s with
          | Some sb => sb :: get_cases ls
          | None => get_cases ls
          end
      | nil => nil
      end.

    Definition default_from_cases (ls : list SwitchBranch) (v : Z) : Prop :=
      (fold_right (fun sb P => ~wp_switch_branch sb v /\ P) True ls).


    (** apply the [wp] calculation to the body of a switch

        NOTE that the semantics of [switch] statements is *very* conservative in the
        current setup. In particular.

          1. We do not support using a [case] to jump over a variable declaration
          2. We do not support [case] statements that jump into the bodies of loops,
             i.e. Duft's device.

        Supporting 1 should not be difficult in principle.
        Full support for 2 seems to require a more sophisticated setup for [wp].
        In other work, this sort of thing is handled as essentially unstructured
        programs.

        We interpret the semantics of [wp_switch_block] by el
     *)
    Fixpoint wp_switch_block_stmt
        (next : option (Z -> Prop) -> option (list ((Z -> Prop) * list Stmt)))
        (Ldef : option (Z -> Prop)) (s : Stmt) (ls' : list Stmt)
        : option (list ((Z -> Prop) * list Stmt)) :=
      match s with
      | Scase sb =>
          (fun x => (wp_switch_branch sb, ls') :: x) <$> next Ldef
      | Sdefault =>
          match Ldef with
          | None =>
              (* NOTE in this case there were multiple [default] statements which is
                 not legal *)
              None
          | Some def => (fun x => (def, ls') :: x) <$> next None
          end
      | Sdecl _ =>
          (* NOTE this check ensures that we never case past a declaration which
             could be problematic from a soundness point of view. *)
          if no_case (Sseq ls') then next Ldef else None
      | SLocInfo _ s => wp_switch_block_stmt next Ldef s ls'
      | s => if no_case s then next Ldef else None
      end.

    Fixpoint wp_switch_block (Ldef : option (Z -> Prop)) (ls : list Stmt)
      : option (list ((Z -> Prop) * list Stmt)) :=
      match ls with
      | s :: ls' =>
          wp_switch_block_stmt (fun Ldef => wp_switch_block Ldef ls') Ldef s ls'
      | nil =>
          match Ldef with
          | None => Some nil
          | Some def => Some ((def, nil) :: nil)
          end
      end.

    Definition Kswitch_inner (k : Kpred) (rt : ReturnType) : mpred :=
      match rt with
      | Break => k Normal
      | rt => k rt
      end.
    #[global] Arguments Kswitch_inner _ !rt /.

    Definition Kswitch (k : Kpred) : Kpred :=
      KP $ Kswitch_inner k.

    Lemma Kswitch_idemp Q :
      Kswitch (Kswitch Q) -|- Kswitch Q.
    Proof. by constructor => -[]. Qed.

    Lemma fupd_Kswitch Q :
      (|={⊤}=> Kswitch Q)
     -|- Kswitch (|={⊤}=> Q).
    Proof.
      by constructor; case => /= *;
         rewrite !monPred_at_fupd /=.
    Qed.

    (* An error to say that a `switch` block with [body] is not supported *)
    Record switch_block (body : list Stmt) : Prop := {}.

    Axiom wp_switch : forall ρ init decl e b Q,
        match pre_stmt init decl with
        | None =>
          match wp_switch_block (Some $ default_from_cases (get_cases b)) b with
          | None => UNSUPPORTED (switch_block b)
          | Some cases =>
            letI* v, free := wp_operand tu ρ e in
            interp free $
              Exists vv : Z, [| v = Vint vv |] **
              [∧list] x ∈ cases, [| x.1 vv |] -* wp_block ρ x.2 (Kswitch Q)
          end
        | Some ss =>
            wp ρ (Sseq (ss ++ [Sswitch None None e (Sseq b)])) Q
        end
        |-- wp ρ (Sswitch init decl e (Sseq b)) Q.

    (* note: case and default statements are only meaningful inside of [switch].
     * this is handled by [wp_switch_block].
     *)
    Axiom wp_case : forall ρ sb Q, Q Normal |-- wp ρ (Scase sb) Q.
    Axiom wp_default : forall ρ Q, Q Normal |-- wp ρ Sdefault Q.

  End with_resolver.

  (* ideally, we would like to use the following line, but [cbn] does not seem to
       like the !.
      Arguments wp_decl_var _ _ _ _ !_ _ /. *)
  #[global] Arguments wp_decl_var _ _ _ _ _ _ _ _ _ /.
  #[global] Arguments wp_decl _ _ _ _ _ _ _ /. (* ! should occur on [d] *)


  #[global,deprecated(since="20240204",note="use [wp_for_inv_nolater].")]
  Notation wp_for := wp_for_inv_nolater (only parsing).
  #[global,deprecated(since="20240204",note="use [wp_do_inv_nolater].")]
  Notation wp_do := wp_do_inv_nolater (only parsing).
  #[global,deprecated(since="20240204",note="use [wp_while_inv_nolater].")]
  Notation wp_while := wp_while_inv_nolater (only parsing).

End Stmt.

Declare Module S : Stmt.

Export S.
