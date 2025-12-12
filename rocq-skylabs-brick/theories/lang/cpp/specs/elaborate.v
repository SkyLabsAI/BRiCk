(*
 * Copyright (c) 2022-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(** Functionality to elaborate specifications that are written to take
    operands (i.e. [val]) and convert them to take materialized values.
 *)
Require Import bluerock.iris.extra.proofmode.proofmode.
Require Import bluerock.lang.cpp.syntax.
Require Import bluerock.lang.cpp.logic.
Require Import bluerock.lang.cpp.semantics.
Require Export bluerock.lang.cpp.specs.cpp_specs.
Require Import bluerock.lang.cpp.specs.wp_spec_compat.

Section with_cpp.
  Context `{Σ : cpp_logic} {σ : genv}.

  (** Determine if an argument is already materialized in the operand style.
      If it is, return [None], otherwise, return [Some (cv, ty)] used for [primR].
   *)
  Definition mtype (t : type) : option (type_qualifiers * type) :=
    let '(cv, t) := decompose_type t in
    pair cv <$> match t with
                | Tnamed cls => None
                | Tref ty
                | Trv_ref ty => Some (Tref $ erase_qualifiers ty)
                | _ => Some (erase_qualifiers t)
                end.

  #[local] Notation add_with name t := (fun K => add_with (T:=t) K name).

  (** [elaborate ret ts wpp args] builds a function specification around [wpp]
      assuming that [wpp] takes the arguments in [args] (in reverse order) and the
      remaining arguments in [ts].
   *)
  Fixpoint elaborate (ret : type) (ts : list type) (ar : function_arity) (args : list val) (wpp : WpSpec_cpp_val) : WpSpec mpredI ptr ptr :=
    match ts with
    | nil =>
        let finish args :=
          match mtype ret with
          | None =>
              wp_spec_bind wpp args (fun rv => WITH (fun pr : ptr => DONE pr [| Vptr pr = rv |]) "pr" DummyValue)
          | Some (cv, t) =>
              wp_spec_bind wpp args (fun rv => WITH (fun pr : ptr =>
                   DONE pr (pr |-> tptsto_fuzzyR t (cQp.mk (q_const cv) 1) rv)) "pr" DummyValue)
          end
        in
        match ar with
        | Ar_Definite => finish args
        | Ar_Variadic =>
            add_with "pv" ptr (fun pv =>
            letI* := add_arg pv in
            finish (args ++ [Vptr pv])) DummyValue
        end%I
    | t :: ts =>
        match mtype t with
        | None =>
            add_with "pv" ptr (fun pv =>
            letI* := add_arg pv in
            elaborate ret ts ar (args ++ [Vptr pv]) wpp) DummyValue
        | Some (_, t) => (* arguments are always passed as mutable *)
            add_with "pv" ptr (fun pv =>
            add_with "v" val (fun v =>
            letI* := add_arg pv in
            letI* := add_pre (pv |-> tptsto_fuzzyR t 1$m v) in
            letI* := add_post (pv |-> anyR t 1$m) in
            elaborate ret ts ar (args ++ [v]) wpp) DummyValue) DummyValue
        end%I
    end.

  (** [cpp_spec ret ts spec] is the elaborated version of the [spec]
      (operand-based) spec that is based on materialized values.
   *)
  Definition cpp_spec (ret : type) (ts : list type) {ar : function_arity} (wpp : WpSpec_cpp_val) : WpSpec_cpp_ptr :=
    elaborate ret ts ar nil wpp.

  #[global] Instance elaborate_ne ret ts ar : forall vs,
    NonExpansive (elaborate ret ts ar vs).
  Proof.
    induction ts; simpl; intros.
    { case_match; [case_match|]; repeat red; intros; [solve_proper..|].
      do 5 f_equiv; solve_proper. }
    { case_match; repeat red; intros; repeat f_equiv; done. }
  Qed.
  #[global] Instance elaborate_proper ret ts ar vs :
    Proper (equiv ==> equiv) (elaborate ret ts ar vs).
  Proof. exact: ne_proper. Qed.

  #[global] Instance cpp_spec_ne ret ts {ar} : NonExpansive (@cpp_spec ret ts ar).
  Proof. intros. apply elaborate_ne. Qed.
  #[global] Instance cpp_spec_proper ret ts {ar} :
    Proper (equiv ==> equiv) (@cpp_spec ret ts ar).
  Proof. exact: ne_proper. Qed.

  #[global] Instance : Params (@cpp_spec) 6 := {}.

  (** Specification implications

      NOTE: these can be strengthened to include extra information about well-typed values.
            (this includes [valid_ptr] on `this` if it exists                                                                  )
      NOTE: this should do the extra plumbing to avoid [K], though it isn't clear how to do this
      NOTE: this can be strengthened with extra fancy updates.
   *)
  Definition spec_impl {A R} (Q P : WpSpec mpredI A R) : mpredI :=
    wpspec_wand Q P.

  Definition spec_entails {A R} (Q P : WpSpec mpredI A R) : Prop :=
    wpspec_entails Q P.

  #[global] Instance spec_entails_refl A R : Reflexive (@spec_entails A R).
  Proof. exact: wpspec_relation_refl. Qed.
  #[global] Instance spec_entails_trans A R : Transitive (@spec_entails A R).
  Proof. exact: wpspec_relation_trans. Qed.

  Lemma spec_entails_impl {A R} Q P :
    (|-- @spec_impl A R P Q) ↔
    wpspec_entails P Q.
  Proof.
    rewrite /spec_impl/wpspec_relation; split; intros H **; first iApply H.
    iIntros (??). iApply H.
  Qed.

  Lemma elab_impl (Q P : WpSpec mpredI val val) ret ts ar :
    spec_impl Q P -∗ spec_impl (cpp_spec ret ts (ar:=ar) Q) (cpp_spec ret ts (ar:=ar) P).
  Proof.
    rewrite /spec_impl/wp_specD/cpp_spec.
    assert (forall ps xs Ps Qs,
               (∀ (vs : list val) (K : val → mpred), spec_internal P [] [] [] vs K -∗ spec_internal Q [] [] [] vs K) -∗
               ∀ (vs : list ptr) (K : ptr → mpred),
                 spec_internal (elaborate ret ts ar ps P) xs Ps Qs vs K -∗ spec_internal (elaborate ret ts ar ps Q) xs Ps Qs vs K).
    { induction ts; simpl; intros.
      { repeat case_match; rewrite /wp_spec_bind/=;
          try solve [ iIntros "H" (??) "[$ P]";
                      iRevert "P"; iApply list_sep_into_frame;
                      iApply "H"
                    | iIntros "H" (??) "P";
                      iDestruct "P" as (x) "[% P]";
                      iExists x; iFrame "%";
                      iRevert "P"; iApply list_sep_into_frame;
                      iApply "H"; eauto ]. }
      { repeat case_match; rewrite /wp_spec_bind/=.
        { iIntros "H" (??) "P".
          iDestruct "P" as (x y) "P".
          iExists x, y.
          iDestruct (IHts with "H") as "H".
          by iApply "H". }
        { iIntros "H" (??) "P".
          iDestruct "P" as (x) "P".
          iExists x.
          iDestruct (IHts with "H") as "H".
          by iApply "H". } } }
    { eauto. }
  Qed.

  Lemma elab_entails (Q P : WpSpec mpredI val val) ret ts ar :
    spec_entails Q P ->
    spec_entails (cpp_spec ret ts (ar:=ar) Q) (cpp_spec ret ts (ar:=ar) P).
  Proof. intros H%spec_entails_impl. iApply elab_impl. iApply H. Qed.

  #[global] Instance cpp_spec_mono ret ts ar :
    Proper (spec_entails ==> spec_entails) (cpp_spec ret ts (ar:=ar)).
  Proof. intros ???. exact: elab_entails. Qed.


  Definition spec_entails_fupd {A R} (Q P : WpSpec mpredI A R) :=
    wpspec_entails_fupd Q P.

  Definition spec_impl_fupd {A R} (Q P : WpSpec mpredI A R) : mpredI :=
    wpspec_wand_fupd Q P.

  Lemma spec_entails_impl_fupd {A R} Q P :
    (|-- @spec_impl_fupd A R P Q) ↔
    spec_entails_fupd P Q.
  Proof.
    rewrite /spec_impl_fupd/spec_entails_fupd; split; intros H **; first iApply H.
    iIntros (??). iApply H.
  Qed.

  Lemma list_sep_into_frame_fupd : forall ls (P P' : mpred),
    (P -∗ |={top}=> P') ⊢ list_sep_into ls P -∗ |={top}=> list_sep_into ls P'.
  Proof.
    intros. iIntros "A".
    rewrite (list_sep_into_take _ P) (list_sep_into_take _ P').
    iIntros "[X $]". iApply "A"; done.
  Qed.

  (* Variant of [elab_impl] allowing for fancy updates; neither statement implies the other.
  TODO: maybe the proof could be merged with [elab_impl]'s, by using a _conditional_ fancy update `|={ E }=>?b` and abstracting over `b`. *)
  Lemma elab_impl_fupd (Q P : WpSpec mpredI val val) ret ts ar :
    wpspec_wand_fupd Q P -∗
    wpspec_wand_fupd (cpp_spec ret ts (ar:=ar) Q) (cpp_spec ret ts (ar:=ar) P).
  Proof.
    rewrite /wpspec_wand_fupd/wp_specD/cpp_spec/=.
    assert (forall ps xs Ps Qs,
              (∀ (vs : list val) (K : val → mpred),
                spec_internal P [] [] [] vs K -∗ |={⊤}=> spec_internal Q [] [] [] vs (λ v, |={⊤}=> K v)) -∗
              ∀ (vs : list ptr) (K : ptr → mpred),
                spec_internal (elaborate ret ts ar ps P) xs Ps Qs vs K -∗
                |={⊤}=> spec_internal (elaborate ret ts ar ps Q) xs Ps Qs vs (λ v, |={⊤}=> K v)).
    { induction ts; simpl; intros.
      { repeat case_match; rewrite /wp_spec_bind/=.
        - iIntros "H" (??) "[$ P]".
          iRevert "P"; iApply list_sep_into_frame_fupd.
          iIntros "P".
          iDestruct ("H" with "P") as ">Q".
          iIntros "!>". iRevert "Q".
          iApply spec_internal_frame.
          iIntros (r) ">Q". iIntros (r') "L !>". by iApply "Q".
        - iIntros "H" (??) "[$ P]".
          iRevert "P"; iApply list_sep_into_frame_fupd.
          iIntros "P".
          iDestruct ("H" with "P") as ">Q".
          iIntros "!>". iRevert "Q".
          iApply spec_internal_frame.
          iIntros (r) ">Q". iIntros (r') "L !>". by iApply "Q".
        - iIntros "H" (??) "(%x & % & P)".
          iExists x; iFrame "%".
          iRevert "P"; iApply list_sep_into_frame_fupd.
          iIntros "P".
          iDestruct ("H" with "P") as ">Q".
          iIntros "!>". iRevert "Q".
          iApply spec_internal_frame.
          iIntros (r) ">Q". iIntros (r') "L !>". by iApply "Q".
        - iIntros "H" (??) "(%x & % & P)".
          iExists x; iFrame "%".
          iRevert "P"; iApply list_sep_into_frame_fupd.
          iIntros "P".
          iDestruct ("H" with "P") as ">Q".
          iIntros "!>". iRevert "Q".
          iApply spec_internal_frame.
          iIntros (r) ">Q". iIntros (r') "L !>". by iApply "Q". }
      { repeat case_match; rewrite /wp_spec_bind/=.
        { iIntros "H" (??) "P".
          iDestruct "P" as (x y) "P".
          iExists x, y.
          iDestruct (IHts with "H") as "H".
          by iApply "H". }
        { iIntros "H" (??) "P".
          iDestruct "P" as (x) "P".
          iExists x.
          iDestruct (IHts with "H") as "H".
          by iApply "H". } } }
    { eauto. }
  Qed.

  Lemma elab_entails_fupd (Q P : WpSpec mpredI val val) ret ts ar :
    spec_entails_fupd Q P ->
    spec_entails_fupd (cpp_spec ret ts (ar:=ar) Q) (cpp_spec ret ts (ar:=ar) P).
  Proof. intros H%spec_entails_impl_fupd. iApply elab_impl_fupd. iApply H. Qed.

  #[global] Instance cpp_spec_mono_fupd ret ts ar :
    Proper (spec_entails_fupd ==> spec_entails_fupd) (cpp_spec ret ts (ar:=ar)).
  Proof. intros ???. exact: elab_entails_fupd. Qed.
End with_cpp.
