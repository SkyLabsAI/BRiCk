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
  #[local] Arguments wp_test {_ _ _ _} _ _ _.
  Import UPoly.

  (** weakest pre-condition for statements
   *)
  Section with_resolver.
    Context `{Σ : cpp_logic} {σ : genv}.
    Variable (tu : translation_unit).

    #[local] Notation wp := (wp tu).
    #[local] Notation interp := (interp tu).
    #[local] Notation wp_initialize := (wp_initialize tu).
    #[local] Notation default_initialize := (default_initialize tu).

    (** * Attribute Evaluation *)

    (* NOTE: this assumes that attributes do not have a semantic
       impact on the code. There are some attributes, e.g. <<OMP::for>>
       that have a semantic impact on the code, but Clang chooses to
       represent these using different AST nodes. *)
    Axiom wp_attr : forall ρ attrs s,
        wp ρ s ⊆ wp ρ (Sattr attrs s).

    (** * Expression Evaluation *)

    (*
    Definition Knormal (Q : Kpred) (_ : unit) (free : FreeTemps.t) (_ : FreeTemps.IsCanonical free) : mpred :=
      interp free $ Q Normal.
     *)

    Axiom wp_expr : forall ρ e,
        (Mfree_all tu $ wp_discard tu ρ e)
        ⊆ wp ρ (Sexpr e).

    (** * Declarations *)

    (* This definition performs allocation of local variables.
     *)
    Definition Mdefault_initialize (ty : decltype) (p : ptr) : Mlocal FreeTemps.t :=
      letWP* _ := default_initialize ty p in
      mret FreeTemps.id.
      (* {| _wp K := default_initialize ty p (fun free => interp free $ K (Normal $ FreeTemps.delete ty p) FreeTemps.id _) |}. *)

    #[program]
    Definition Mopt_initialize (ρ : region) (ty : decltype) (n : localname) (init : option Expr) : Mlocal (region * FreeTemps.t) :=
      letM* p := demonic ptr in
      pair (Rbind n p ρ) <$>
      match init with
      | Some init =>
          (* In C++ (and in C) the scope of the name begins immediately after
               the name is declared, before it is initialized.
               See <https://eel.is/c++draft/basic.scope.pdecl#1>
           *)
          wp_initialize (Rbind n p ρ) ty p init
      | None => Mdefault_initialize ty p
      end.

    #[program]
    Definition Mopt_initialize_anon (ρ : region) (ty : decltype) (init : option Expr) : Mlocal (ptr * FreeTemps.t) :=
      letM* p := demonic ptr in
      pair p <$> match init with
                 | Some init => wp_initialize ρ ty p init
                 | None => Mdefault_initialize ty p
                 end.

    Definition wp_decl_var (ρ : region) (x : ident) (ty : type) (init : option Expr)
      : Mlocal region :=
      letM* p := demonic ptr in
      letM* '(ρ, free) := Mfree_all tu $ Mopt_initialize ρ ty x init in
      letM* _ := Mexpr.push_free free in
      mret ρ.

    (*
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
    *)

    (* the variables declared in a destructing declaration must have initializers *)
    Record destructuring_declaration (d : VarDecl) : Prop := {}.

    Fixpoint wp_destructure (ρ_init : region) (ds : list BindingDecl)
      (ρ : region) {struct ds} : Mlocal region :=
      match ds with
      | nil => mret ρ
      | Bvar x ty init :: ds =>
          letWP* p := demonic ptr in
          letWP* free := wp_initialize ρ_init ty p init in
          letWP* '() := Mexpr.push_free free in
          wp_destructure ρ_init ds (Rbind x p ρ)
      | Bbind x _ init :: ds =>
          letWP* p := wp_glval tu ρ_init init in
          wp_destructure ρ_init ds (Rbind x p ρ)
      end.

    (*
    Lemma wp_destructure_frame : forall ds ρ ρ_init m m' free,
        Forall a b, m a b -* m' a b
        |-- wp_destructure ρ_init ds ρ m free -* wp_destructure ρ_init ds ρ m' free.
    Proof.
      induction ds; simpl; intros.
      { iIntros "X"; iApply "X". }
      { iIntros "X H"; case_match.
        { iIntros (p); iSpecialize ("H" $! p); iRevert "H"; iApply wp_initialize_frame => //.
          iIntros (?); by iApply IHds. }
        { iRevert "H"; iApply wp_glval_frame => //.
          iIntros (??). by iApply IHds. } }
    Qed.
    *)

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

    Definition wp_decl (ρ : region) (d : VarDecl) : Mlocal region :=
      match d with
      | Dvar x ty init => wp_decl_var ρ x ty init
      | Ddecompose init x ds =>
        (* NOTE: the **declaration type** of the initializer *)
        let common_type := decltype_of_expr init in
        letWP* common_p := demonic ptr in
        (* unlike for variables (see [wp_decl_var]), the variables in a structured binding
           are not available in the initializer.
           See <https://eel.is/c++draft/dcl.struct.bind#2>
         *)
        letWP* free := Mfree_all tu $ wp_initialize ρ common_type common_p init in
        (* NOTE: [free] is the de-allocation of the initialized value *)
        letWP* '() := Mexpr.push_free free in
           (* NOTE: [free] is used to deallocate temporaries generated in the execution of [init].
              It should not matter if it is destroyed immediately or after the destructuring occurs.
            *)
        wp_destructure (Rbind x common_p ρ) ds ρ
      | Dinit ts nm ty init =>
        let do_init :=
            match init with
            | None => Mdefault_initialize ty (_global nm)
            | Some init => wp_initialize ρ ty (_global nm) init
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
          letWP* '(TeleArgCons i tt) :=
            ac (TT:=[tele (i : _)])
                (fun i => static_initialized nm i)
                Mouter Minner
                (TT':=[tele])
                (fun i =>
                   match i with
                   | uninitialized => static_initialized nm initializing
                   | initializing =>
                       (* the C++ thread waits unless the state is either [initialized] or [uninitialized]. *)
                       False
                   | _ => static_initialized nm i
                   end)
          in
          if i is uninitialized then
              letWP* _free := do_init in (* ignore [_free] since we are initiailizing a global *)
              letWP* _ := ac (TT:=[tele (i : _)])
                              (fun i => static_initialized nm i)
                              Mouter Minner
                              (TT':=[tele])
                              (fun i => [| i = initializing |] ** static_initialized nm initialized) in
              mret ρ
          else
            mret ρ
        else
          letWP* i := angelic _ in
          letWP* '() := consume (static_initialized nm i) in
          if i is uninitialized then
            letWP* _free := do_init in (* ignore [_free] since we are initializing a global *)
            letWP* '() := produce (static_initialized nm initialized) in
            mret ρ
          else
            letWP* '() := produce (static_initialized nm i) in
            mret ρ
      end%I.

    (*
    Lemma wp_decl_frame : forall ds ρ m m',
        Forall a b, m a b -* m' a b
        |-- wp_decl ρ ds m -* wp_decl ρ ds m'.
    Proof.
      destruct ds; simpl; intros.
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
    Qed.
    *)

    (* [wp_decls ρ_init ds ρ K] evalutes the declarations in [ds]
    using the environment [ρ_init] and binds the declarations
    in [ρ] (which it passes to [K]) *)
    Fixpoint wp_decls_def (ρ : region) (ds : list VarDecl)
      : Mlocal region :=
      match ds with
      | nil =>
          non_atomically $ mret ρ
      | d :: ds =>
          letWP* ρ := wp_decl ρ d in
          wp_decls_def ρ ds
      end.
    Definition wp_decls_aux : seal (@wp_decls_def). Proof. by eexists. Qed.
    Definition wp_decls := wp_decls_aux.(unseal).
    Definition wp_decls_eq : @wp_decls = _ := wp_decls_aux.(seal_eq).

    (*
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
    *)

    (*
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
    *)

    (*
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
    *)

    (** * Blocks *)
    (* #[program] *)
    (* Definition Mlater `{Σ : cpp_logic} : M () := *)
    (*   {| _wp K := |> K () FreeTemps.id _ |}. *)
    (* Next Obligation. *)
    (*   simpl. intros. *)
    (*   iIntros "K A"; iNext; iRevert "A"; iApply "K". *)
    (* Qed. *)
    (* #[program] *)
    (* Instance Fupd {T} : FUpd (M T) := *)
    (*   fun E1 E2 m => {| _wp K := |={E1,E2}=> m.(_wp) K |}%I. *)
    (* Next Obligation. *)
    (*   simpl; intros. *)
    (*   iIntros "A >B !>". iRevert "B"; iApply _ok; iApply "A"; iAssumption. *)
    (* Qed. *)

    Fixpoint wp_block_def (ρ : region) (ss : list Stmt) : Mlocal unit :=
      match ss with
      | nil => (* |={top}=> |> |={top}=> *) mret tt
      | Sdecl ds :: ss =>
          letM* ρ := wp_decls ρ ds in
          (* |={top}=> |> |={top}=> *) wp_block_def ρ ss
      | s :: ss =>
        (* |={top}=> |> |={top}=> *)
          letM* '() := wp ρ s in
          (wp_block_def ρ ss)
      end.
    Definition wp_block_aux : seal (@wp_block_def). Proof. by eexists. Qed.
    Definition wp_block := wp_block_aux.(unseal).
    Definition wp_block_eq : @wp_block = _ := wp_block_aux.(seal_eq).

    (* Show [wp_block] satisfies the fixpoint equation. *)
    Lemma wp_block_unfold (ρ : region) (ss : list Stmt) :
      wp_block ρ ss ≡
      (match ss with
      | nil => (* |={top}=> |> |={top}=> *) mret tt
      | Sdecl ds :: ss =>
          letM* ρ := wp_decls ρ ds in
          (* |={top}=> |> |={top}=> *) wp_block ρ ss
      | s :: ss =>
        (* |={top}=> |> |={top}=> *) letM* '() := wp ρ s in wp_block ρ ss
      end)%I.
    Proof. rewrite !wp_block_eq; by destruct ss. Qed.

    (*
    Lemma wp_block_frame : forall ss ρ, monad.Frame (wp_block ρ ss) (wp_block ρ ss).
    Proof.
      rewrite /monad.Frame. (*
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
      rewrite !wp_block_unfold.
      iIntros "X"; destruct s; try by iApply (Himpl with "X").
      iApply wp_decls_frame.
      iIntros (??) ">H !> !>". iMod "H"; iModIntro.
      iApply (IHss with "[X] H"); iIntros (?).
      iApply Kfree_frame. iApply "X".
    Qed. *) Admitted.
    *)

    (*
    Lemma wp_block_shift ρ ds (Q : _) :
      (|={top}=> WP (wp_block ρ ds) (fun a b c => |={top}=> Q a b c)) |-- WP (wp_block ρ ds) Q.
    Proof. (*
      elim: ds ρ Q => [|d ds IH] ρ Q /=; rewrite !wp_block_unfold /=.
      - iIntros ">>H !> !> /=". by iMod "H" as ">$".
      - iAssert (
        (|={⊤}=> |={⊤}▷=> wp ρ d (Kseq (wp_block ρ ds) (|={⊤}=> |={⊤}=> Q))) -∗
        |={⊤}▷=> wp ρ d (Kseq (wp_block ρ ds) (|={⊤}=> Q)))%I as "W". {
          iIntros ">>H !> !> !>". iMod "H". iApply (wp_frame with "[] H"). done.
          iIntros (?) "H".
          iApply (Kseq_frame with "[] [] H").
          { iApply wp_block_frame. }
          iIntros (?) "H". by rewrite fupd_idemp.
      }
      destruct d; try by iExact "W".
      iIntros "{W} H". iApply wp_decls_shift. iMod "H"; iModIntro.
      iApply (wp_decls_frame with "[] H"); iIntros (??) ">H !> !> !> !>".
      iApply IH. iMod "H"; iModIntro.
      iApply (wp_block_frame with "[] H"); iIntros (rt) "H !> /=".
      rewrite monPred_at_fupd. iApply (interp_shift with "H").
    Qed. *) Admitted.

    Lemma fupd_wp_block ρ ds Q :
      (|={top}=> WP (wp_block ρ ds) Q) |-- WP (wp_block ρ ds) Q.
    Proof.
      rewrite -{2}wp_block_shift; f_equiv.
(*      iApply wp_block_frame. by iIntros "* $".
    Qed. *) Admitted.

    Lemma wp_block_fupd ρ ds Q :
      WP (wp_block ρ ds) (fun a b c => |={top}=> Q a b c) |-- WP (wp_block ρ ds) Q.
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
      ElimModal True p false (|={top}=> P) P (WP (wp_block ρ body) Q) (WP (wp_block ρ body) Q).
    Proof.
      rewrite /ElimModal. rewrite bi.intuitionistically_if_elim/=.
      by rewrite fupd_frame_r bi.wand_elim_r fupd_wp_block.
    Qed.
    #[global] Instance elim_modal_bupd_wp_lval p P Q ρ body :
      ElimModal True p false (|==> P) P (WP (wp_block ρ body) Q) (WP (wp_block ρ body) Q).
    Proof.
      rewrite /ElimModal (bupd_fupd top). exact: elim_modal_fupd_wp_block.
    Qed.
    #[global] Instance add_modal_fupd_wp_lval P Q ρ body :
      AddModal (|={top}=> P) P (WP (wp_block ρ body) Q).
    Proof.
      rewrite/AddModal. by rewrite fupd_frame_r bi.wand_elim_r fupd_wp_block.
    Qed.
    *)

    Axiom wp_seq : forall ρ ss,
        wp_block ρ ss ⊆ wp ρ (Sseq ss).

    (** * <<if>> *)

    Axiom wp_if : forall ρ e thn els,
        (letM* (c : bool) := Mfree_all tu $ wp_test tu ρ e in
           if c
           then wp ρ thn
           else wp ρ els)
      ⊆ wp ρ (Sif None e thn els).

    Axiom wp_if_decl : forall ρ d e thn els,
        wp ρ (Sseq (Sdecl (d :: nil) :: Sif None e thn els :: nil))
        ⊆ wp ρ (Sif (Some d) e thn els).

    (* The loops are phrased using 1-step unfoldings and invariant rules are
       proved using Löb induction.

       C++ (and C) allow optimizing away certain infinite loops,
       e.g. <<while (1);>> can be optimized to <<;>>.
       These loop rules are not sound for use with compilations that use this
       optimization.
     *)

    (*
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
     *)

    (** * <<while>> *)

    Definition while_unroll ρ decl test body :=
      wp ρ (Sif decl test body Sbreak).

    Require Import iris.bi.lib.fixpoint.
    Import UPoly.

    #[program]
    Definition Mhandle_loop {U}
      (body : Mlocal ())
      (normal_continue : Mlocal U) (* go to the top *)
      (break : Mlocal U) (* finish the loop *)
      : Mlocal U :=
      Compose.mk $
        letWP* rt := Mexpr.handle (Mfree_all tu body) in
          Compose._prun
          match rt with
          | Mexpr.Normal _
          | Mexpr.Continue => normal_continue
          | Mexpr.Break => Mexpr.break
          | Mexpr.ReturnVoid => Mexpr.return_void
          | Mexpr.ReturnVal p => Mexpr.return_val p
          | Mexpr.Exception ty p => Mexpr.throw ty p
          end.

    #[program]
    Definition Mhandle_break {U}
      (body : Mlocal U)
      (break : Mlocal U) (* finish the loop *)
      : Mlocal U :=
      Compose.mk $
        letWP* rt := Mexpr.handle (Mfree_all tu body) in
          Compose._prun
            match rt return Mexpr.M _ with
            | Mexpr.Normal v => mret v
            | Mexpr.Continue => Mexpr.continue
            | Mexpr.Break => Mexpr.break
            | Mexpr.ReturnVoid => Mexpr.return_void
            | Mexpr.ReturnVal p => Mexpr.return_val p
            | Mexpr.Exception ty p => Mexpr.throw ty p
            end.

    Definition M_raw T : ofe := (with_temps.Result (Mexpr.Result T) -> mpredI) -d> mpredI.

    Lemma M_raw_dist_ext {T} (x y : M_raw T) n :
      dist n x y <->
      forall K, dist n (x K) (y K).
    Proof.
      clear. intros.
      rewrite /M_raw/=.
      rewrite /discrete_funO /= /ofe_car.
      simpl. simpl ofe_car.
      rewrite /discrete_fun/=.
      rewrite /discrete_fun_dist/=.
      unfold ofe_car. simpl.
      unfold ofe_dist. simpl. reflexivity.
    Qed.


    Lemma M_raw_forall {T} (x y : M_raw T) n :
      dist_later n x y ->
      forall K, dist_later n (x K) (y K).
    Proof.
      clear. intros.
      constructor. intros.
      apply M_raw_dist_ext.
      by apply H.
    Qed.

    Lemma Mexpr_frame {T} (a : Mexpr.M T) K1 K2 :
      (∀ x, K1 x -∗ K2 x) ⊢ Mexpr._wp a K1 -∗ Mexpr._wp a K2.
    Proof.
      rewrite /Mexpr._wp. iIntros "X". iApply M._frame.
      eauto.
    Qed.

    (* TODO: the fixpoint part of this should hold on [M.M], but
       the actual handling of the loop needs to happen in [Mexpr.M] *)
    #[program]
    Definition Mloop (body : Mlocal ()) : Mlocal () :=
      Mexpr.mk (
      {| M._wp :=
          @fixpoint _ _ _ (funI (continue : M_raw ()) K =>
                      letI* rt := Mexpr._wp (@Mfree_all _ _ Σ σ tu _ body) in
                      match rt.(with_temps._result) with
                      | Mexpr.Normal _ | Mexpr.Continue => |> continue K
                      | Mexpr.Break => K (mret $ Mexpr.Normal ())
                      | exc => K (mret exc)
                      end) _ |}).
    Next Obligation.
      (* Contractive *)
      simpl; intros.
      red. red. intros.
      intro; simpl.
      apply M._ne; intro.
      case_match; try reflexivity.
      { apply later_contractive. by apply M_raw_forall. }
      { apply later_contractive. by apply M_raw_forall. }
    Qed.
    Next Obligation.
      (* _frame *)
      simpl; intros.
      iIntros "K".
      iLöb as "IH".
      match goal with
      | |- context [ @fixpoint ?X ?Y ?I ?F ?C _ ] =>
          generalize C; intro CC;
          remember F as BODY ;
          generalize (@fixpoint_unfold X Y I BODY CC)
      end.
      match goal with
      | |- context [ @fixpoint ?X ?Y ?I ?F ?C _ ] =>
          generalize (@fixpoint X Y I F C)
      end.
      intros FIX Hfix.
      assert (forall K, FIX K ≡ BODY FIX K) by apply Hfix.
      rewrite {2}(H K1) {2}(H K2).
      rewrite HeqBODY.
      iApply Mexpr_frame; iIntros (?).
      case_match;
        try solve [ iApply "K" | iIntros "X"; iNext; iRevert "X"; iApply "IH"; iApply "K" ].
    Qed.
    Next Obligation.
      (* _ne *)
      intros.
    Admitted.

    Definition while_loop (ρ : region)
      (decl : option VarDecl)
      (test : Expr)
      (body : Stmt)
      : Mlocal () :=
      Mhandle_loop (letM* ρ :=
                      match decl with
                      | None => mret ρ
                      | Some decl => wp_decl ρ decl
                      end
                    in
                    letM* (c : bool) := Mfree_all tu $ wp_test tu ρ test in
                    if c
                    then wp ρ body
                    else Mexpr.break)
        Mexpr.continue
        Mexpr.break.

    Axiom wp_while_unroll : forall ρ decl test body,
           Mloop (while_loop ρ decl test body)
        ⊆ wp ρ (Swhile decl test body).

    (*
    Theorem wp_while_inv I : forall ρ test body Q,
        I |-- while_unroll ρ test body (Kloop (|> I) Q) ->
        I |-- wp ρ (Swhile None test body) Q.
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
*)

    (** * <<for>> *)
    Definition for_loop (ρ : region) (test : option Expr)
      (incr : option Expr)
      (body : Stmt)
      : Mlocal () :=
      letM* c := Mfree_all tu $
        match test with
        | None => mret true
        | Some test => wp_test tu ρ test
        end
      in
      Mhandle_loop (Mfree_all tu $ wp ρ body)
        (match incr with
         | None => mret ()
         | Some incr => wp_discard tu ρ incr
         end)
        Mexpr.break.

    Axiom wp_for_unroll : forall ρ test incr body,
           Mloop (for_loop ρ test incr body)
        ⊆ wp ρ (Sfor None test incr body).

    (*
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
      (* all: iIntros "I !>"; iApply "IH"; eauto.
    Qed. *) Admitted.

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
    *)

    (**
       `for (init; test; incr) body` desugars to `{ init; for (; test; incr) body }`
     *)
    Axiom wp_for_init : forall ρ init test incr b,
           wp ρ (Sseq (init :: Sfor None test incr b :: nil))
        ⊆ wp ρ (Sfor (Some init) test incr b).

    (** * <<do>> *)

    Definition do_loop (ρ : region) (s : Stmt) (e : Expr) : Mlocal () :=
      Mhandle_loop (Mfree_all tu $ wp ρ s)
                   (letM* (c : bool) := wp_test tu ρ e in
                    if c then Mexpr.continue else Mexpr.break)
                   Mexpr.break.

    (*
    Definition do_unroll ρ body test (Q : Kpred) :=
      wp ρ body (Kpost (WP (wp_test tu ρ test) (fun c free _ => interp free $ if c then Q Continue else Q Break)) Q).
     *)

    Axiom wp_do_unroll : forall ρ body test,
            Mloop (do_loop ρ body test) ⊆ wp ρ (Sdo body test).

    (*
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
      iIntros (rt) "K"; destruct rt; simpl; eauto. (*
      { iRevert "K"; iApply wp_test_frame; iIntros (??).
        iApply interp_frame; case_match; eauto.
        iIntros "? !>"; iApply "IH"; eauto. }
      { iRevert "K"; iApply wp_test_frame; iIntros (??).
        iApply interp_frame; case_match; eauto.
        iIntros "? !>"; iApply "IH"; eauto. }
    Qed. *) Admitted.

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
      (* all: iApply wp_test_frame; iIntros (??).
      all: iApply interp_frame; case_match; eauto.
    Qed. *) Admitted.
    *)

    (** * <<return>> *)

    (* the semantics of return is like an initialization
     * expression.
     *)
    Axiom wp_return_void : forall ρ,
        Mexpr.return_void ⊆ wp ρ (Sreturn None).

    Axiom wp_return : forall ρ e,
          (let rty := get_return_type ρ in
           letM* '(p, free) := Mfree_all tu $ Mopt_initialize_anon ρ rty $ Some e in
           (* TODO: I need to free everything except the top because there is no scope extrusion
                    in return values *)
           Mexpr.return_val p)
      ⊆ wp ρ (Sreturn (Some e)).

    (*
    Axiom wp_return_frame : forall ρ rv (Q Q' : Kpred),
        match rv with
        | None => Q ReturnVoid -* Q' ReturnVoid
        | Some _ =>
          (* NOTE unsound in the presence of exceptions *)
          Forall v, Q (ReturnVal v) -* Q' (ReturnVal v)
        end |-- wp ρ (Sreturn rv) Q -* wp ρ (Sreturn rv) Q'.
    *)

    (** * <<break>> *)

    Axiom wp_break : forall ρ,
        (letM* '() := step in Mexpr.break) ⊆ wp ρ Sbreak.
    (*
    Axiom wp_break_frame : forall ρ (Q Q' : Kpred),
        Q Break -* Q' Break |-- wp ρ Sbreak Q -* wp ρ Sbreak Q'.
     *)

    (** * <<continue>> *)
    Axiom wp_continue : forall ρ,
        (letM* '() := step in Mexpr.continue) ⊆ wp ρ Scontinue.
    (*
    Axiom wp_continue_frame : forall ρ (Q Q' : Kpred),
        Q Continue -* Q' Continue |-- wp ρ Scontinue Q -* wp ρ Scontinue Q'.
     *)

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
      | Sif _ _ a b
      | Sif_consteval a b => no_case a && no_case b
      | Swhile _ _ s => no_case s
      | Sfor _ _ _ s => no_case s
      | Sdo s _ => no_case s
      | Sattr _ s => no_case s
      | Sswitch _ _ _ => true
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
      end.

    Fixpoint get_cases (ls : list Stmt) : list SwitchBranch :=
      match ls with
      | Scase sb :: ls =>
        sb :: get_cases ls
      | _ :: ls => get_cases ls
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
    Fixpoint wp_switch_block (Ldef : option (Z -> Prop)) (ls : list Stmt)
      : option (list ((Z -> Prop) * list Stmt)) :=
      match ls with
      | Scase sb :: ls =>
        (fun x => (wp_switch_branch sb, ls) :: x) <$> wp_switch_block Ldef ls
      | Sdefault :: ls =>
        match Ldef with
        | None =>
          (* NOTE in this case there were multiple [default] statements which is
             not legal *)
          None
        | Some def =>
          (fun x => (def, ls) :: x) <$> wp_switch_block None ls
        end
      | Sdecl _ :: ls' =>
        (* NOTE this check ensures that we never case past a declaration which
           could be problematic from a soundness point of view.
         *)
        if no_case (Sseq ls') then
          wp_switch_block Ldef ls'
        else
          None
      | s :: ls' =>
        if no_case s then
          wp_switch_block Ldef ls'
        else
          None
      | nil =>
        match Ldef with
        | None => Some nil
        | Some def => Some ((def, nil) :: nil)
        end
      end.

    (*
    Definition Kswitch_inner (k : Kpred) (rt : ReturnType) : mpred :=
      match rt with
      | Break => k Normal
      | rt => k rt
      end.
    #[global] Arguments Kswitch_inner _ !rt /.

    Definition Kswitch (k : Kpred) : Kpred :=
      KP $ Kswitch_inner k.
     *)

    Axiom wp_switch_decl : forall ρ d e ls,
        wp ρ (Sseq (Sdecl (d :: nil) :: Sswitch None e ls :: nil))
        ⊆ wp ρ (Sswitch (Some d) e ls).

    (* An error to say that a `switch` block with [body] is not supported *)
    Record switch_block (body : list Stmt) : Prop := {}.

    (*
    #[program]
    Definition Mall {T} (ls : list (M T)) : M T :=
      {| _wp K := [∧list] x ∈ ls , x.(_wp) K |}%I.
    Next Obligation.
      simpl; intros; clear.
      induction ls; simpl.
      { iIntros "? ?"; eauto. }
      { iIntros "K X"; iSplit; [ iDestruct "X" as "[X _]" | iDestruct "X" as "[_ X]" ]; iRevert "X".
        - iApply _ok; iApply "K".
        - iApply IHls. eauto. }
    Qed.
    *)

    Import UPoly.
    Definition Mas `{_ : MBind M} {_ : MRet M}  `{WP : WpMonad PROP M} {T U} (f : T -> U) (x : U) : M T :=
      letWP* y := angelic T in
      letWP* '() := consume [| x = f y |] in
      mret y.

    Axiom wp_switch : forall ρ e b,
        match wp_switch_block (Some $ default_from_cases (get_cases b)) b with
        | None => Munsupported (switch_block b)
        | Some cases =>
          letM* v := Mfree_all tu $ mbind (Mas Vint) $ wp_operand tu ρ e in
          letWP* c := demonic _ in
          letWP* '() := produce [| c ∈ cases |] in
          letWP* _ := produce [| c.1 v |] in
          Mhandle_break (wp_block ρ c.2) (mret ())
        end
        ⊆ wp ρ (Sswitch None e (Sseq b)).

    (* note: case and default statements are only meaningful inside of [switch].
     * this is handled by [wp_switch_block].
     *)
    Axiom wp_case : forall ρ sb, mret () ⊆ wp ρ (Scase sb).
    Axiom wp_default : forall ρ, mret () ⊆ wp ρ Sdefault.

  End with_resolver.

  (* ideally, we would like to use the following line, but [cbn] does not seem to
       like the !.
      Arguments wp_decl_var _ _ _ _ !_ _ /. *)
  #[global] Arguments wp_decl_var _ _ _ _ _ _ _ _ _ /.
  #[global] Arguments wp_decl _ _ _ _ _ _ _ /. (* ! should occur on [d] *)

(*
  #[global,deprecated(since="20240204",note="use [wp_for_inv_nolater].")]
  Notation wp_for := wp_for_inv_nolater (only parsing).
  #[global,deprecated(since="20240204",note="use [wp_do_inv_nolater].")]
  Notation wp_do := wp_do_inv_nolater (only parsing).
  #[global,deprecated(since="20240204",note="use [wp_while_inv_nolater].")]
  Notation wp_while := wp_while_inv_nolater (only parsing).
*)

End Stmt.

Declare Module S : Stmt.

Export S.
