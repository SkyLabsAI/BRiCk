(*
 * Copyright (c) 2020 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(**
Another (incomplete) consistency proof for [PTRS], based on Krebbers' PhD thesis, and
other formal models of C++ using structured pointers.
This is more complex than [SIMPLE_PTRS_IMPL], but will be necessary to justify [VALID_PTR_AXIOMS].

In this model, all valid pointers have an address pinned, but this is not meant
to be guaranteed.
*)

Require Import stdpp.gmap.
Require Import skylabs.prelude.base.
Require Import skylabs.prelude.addr.
Require Import skylabs.prelude.avl.
Require Import skylabs.prelude.bytestring.
Require Import skylabs.prelude.option.
Require Import skylabs.prelude.numbers.

Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.semantics.sub_module.
Require Import skylabs.lang.cpp.semantics.ptrs.
Require Import skylabs.lang.cpp.model.simple_pointers_utils.
Require Import skylabs.lang.cpp.model.inductive_pointers_utils.

Implicit Types (σ : genv) (z : Z).
#[local] Close Scope nat_scope.
#[local] Open Scope Z_scope.

Module PTRS_IMPL <: PTRS_INTF.
  Import canonical_tu address_sums merge_elems.

  Inductive raw_offset_seg : Set :=
  | o_field_ (* type-name: *) (f : field)
  | o_sub_ (ty : type) (z : Z)
  | o_base_ (derived base : globname)
  | o_derived_ (base derived : globname)
  | o_invalid_.
  #[local] Instance raw_offset_seg_eq_dec : EqDecision raw_offset_seg.
  Proof. solve_decision. Defined.
  #[global] Declare Instance raw_offset_seg_countable : Countable raw_offset_seg.

  Definition offset_seg : Set := raw_offset_seg * Z.
  #[local] Instance offset_seg_eq_dec : EqDecision offset_seg := _.
  #[local] Instance offset_seg_countable : Countable offset_seg := _.

  Definition eval_raw_offset_seg σ (ro : raw_offset_seg) : option Z :=
    match ro with
    | o_field_ f => o_field_off σ f
    | o_sub_ ty z => o_sub_off σ ty z
    | o_base_ derived base => o_base_off σ derived base
    | o_derived_ base derived => o_derived_off σ base derived
    | o_invalid_ => None
    end.
  Definition mk_offset_seg σ (ro : raw_offset_seg) : offset_seg :=
    match eval_raw_offset_seg σ ro with
    | None => (o_invalid_, 0%Z)
    | Some off => (ro, off)
    end.

  (* This list is reversed.
  The list of offsets in [[p; o_1; ...; o_n]] is represented as [[o_n; ... o_1]].
  This way, we can cons new offsets to the head, and consume them at the tail. *)
  Definition raw_offset := list offset_seg.
  #[local] Instance raw_offset_eq_dec : EqDecision raw_offset := _.
  #[local] Instance raw_offset_countable : Countable raw_offset := _.

  Notation isnt o pattern :=
    (match o with | pattern => False | _ => True end).

  Section roff_canon.
    (* Context {σ : genv}. *)

    (* We currently ensure the offsets in the destination are correct wrt the source, not that the ones in the source are consistent with each other. *)
    Inductive roff_canon : raw_offset -> raw_offset -> Prop :=
    | o_nil :
      roff_canon [] []
    | o_field_canon s d f o :
      (* is_Some (o_field_off σ f) -> *) (* not canonicalization's problem? *)
      roff_canon s d ->
      roff_canon ((o_field_ f, o) :: s) ((o_field_ f, o) :: d)
    | o_base_canon s d base derived o :
      (* no, because (valid?) normal forms don't use [o_derived]? *)
      (* isnt d ((o_derived_ _ _ , _) :: _) -> *)
      roff_canon s d ->
      roff_canon ((o_base_ derived base, o) :: s) ((o_base_ derived base, o) :: d)
    (* should paths start from the complete object? If
    yes, as done by Ramananandro [POPL 2012],
    o_derived should just cancel out o_base, and this should be omitted. *)
    (* | o_derived_wf s d derived base :
      isnt d (o_base_ _ _ :: d) ->
      roff_canon s d ->
      roff_canon (o_derived_ base derived :: s) (o_derived_ base derived :: d) *)
    | o_derived_cancel_canon s d derived base o1 o2 :
      o1 + o2 = 0 ->
      roff_canon s d ->
      (* This premise is a hack, but without it, normalization might not be deterministic. Thankfully, paths can't contain o_derived step, so we're good! *)
      (* roff_canon (o_base_ derived base :: s) (o_base_ derived base :: d) -> *)
      roff_canon ((o_derived_ base derived, o1) :: (o_base_ derived base, o2) :: s) d
    | o_sub_0_canon s d ty :
      roff_canon s d ->
      roff_canon ((o_sub_ ty 0, 0) :: s) d
    | o_sub_canon s d ty1 z o :
      match d with
      | ((o_sub_ ty2 _, _) :: _) => ty1 <> ty2
      | _ => True
      end ->
      (* In fact, we want [0 < z], but that's a matter of validity, not canonicalization. *)
      z <> 0 ->
      (* isnt o (o_sub_ _ _) *)
      roff_canon s d ->
      roff_canon ((o_sub_ ty1 z, o) :: s) ((o_sub_ ty1 z, o) :: d)
    | o_sub_merge_canon s d ty z1 z2 o1 o2 :
      (* Again, validity would require [> 0]. *)
      z1 + z2 <> 0 ->
      roff_canon s ((o_sub_ ty z1, o1) :: d) ->
      roff_canon ((o_sub_ ty z2, o2) :: s) ((o_sub_ ty (z1 + z2), o1 + o2) :: d)
    .
  End roff_canon.

  Lemma roff_canon_o_base_inv s d derived base o1 o2 :
    roff_canon ((o_base_ derived base, o1) :: s) ((o_base_ derived base, o2) :: d) ->
    roff_canon s d.
  Proof. inversion 1; auto. Qed.

  Lemma roff_canon_o_sub_wf s d ty z o :
    roff_canon s ((o_sub_ ty z, o) :: d) ->
    z <> 0.
  Proof.
    move E: (_ :: _) => d' Hcn.
    elim: Hcn E; naive_solver eauto with lia.
  Qed.

  Lemma roff_canon_o_sub_no_dup s d o ty1 z ro :
    roff_canon s ((o_sub_ ty1 z, ro) :: o :: d) ->
    match o with
    | (o_sub_ ty2 _, _) => ty1 <> ty2
    | _ => True
    end.
  Proof.
    move E: ((o_sub_ _ _, _) :: _) => d' Hcn.
    elim: Hcn z ro E; naive_solver.
  Qed.

  Definition offset_seg_cons (os : offset_seg) (oss : list offset_seg) : list offset_seg :=
    match os, oss with
    | (o_sub_ ty1 n1, off1), _ =>
      if decide (n1 = 0 /\ off1 = 0)%Z then oss else
      match oss with
        | (o_sub_ ty2 n2, off2) :: oss' =>
        if decide (ty1 <> ty2)
          then os :: oss
          else if decide (n2 + n1 = 0 /\ off1 + off2 = 0)%Z
          then oss'
          else (o_sub_ ty1 (n2 + n1), (off2 + off1)%Z) :: oss'
        | _ => os :: oss
      end
    | (o_base_ der1 base1, off1), (o_derived_ base2 der2, off2) :: oss'
    | (o_derived_ base1 der1, off1), (o_base_ der2 base2, off2) :: oss' =>
      (* Like for [o_sub_], only cancel segments whose offsets also cancel, so
      that normalization preserves [eval_offset]. *)
      if decide (der1 = der2 /\ base1 = base2 /\ off1 + off2 = 0)%Z
      then oss'
      else os :: oss
    (* | (o_invalid_, _), _ => [(o_invalid_, 0%Z)] *)
    | (o_invalid_, z), _ => [(o_invalid_, z)]
    | _, _ => os :: oss
    end.

  Definition raw_offset_collapse : raw_offset -> raw_offset :=
    foldr offset_seg_cons [].
  Arguments raw_offset_collapse !_ /.

  Definition raw_offset_wf (ro : raw_offset) : Prop :=
    raw_offset_collapse ro = ro.
  Arguments raw_offset_wf !_ /.
  #[global] Instance raw_offset_wf_pi ro : ProofIrrel (raw_offset_wf ro) := _.
  Lemma singleton_raw_offset_wf {os}
    (Hn0 : isnt os (o_sub_ _ 0, _)) :
    raw_offset_wf [os].
  Proof. destruct os as [[] ?] => //=; case_decide; naive_solver. Qed.

  #[local] Hint Constructors roff_canon : core.
  Theorem canon_wf_0 src dst :
    roff_canon src dst ->
    roff_canon dst dst.
  Proof.
    intros Hrc; induction Hrc; eauto.
    inversion IHHrc; eauto 2; last have ?: z0 = 0 by [lia]; subst.
    (* Show that [o_sub_merge_canon] isn't applicable. *)
    all: by opose proof* roff_canon_o_sub_wf.
  Qed.

  #[local] Lemma roff_canon_no_derived_head src dst :
    roff_canon src dst ->
    match dst with (o_derived_ _ _, _) :: _ => False | _ => True end.
  Proof. induction 1; done. Qed.

  Theorem canon_wf' src dst : roff_canon src dst -> raw_offset_collapse src = dst.
  Proof.
    rewrite /raw_offset_wf /raw_offset_collapse => Hc;
    induction Hc => //=; rewrite ?IHHc /offset_seg_cons //=.
    { have Hno := roff_canon_no_derived_head _ _ Hc.
      destruct d as [|[seg off] d]; first done.
      destruct seg; done. }
    { have Hno := roff_canon_no_derived_head _ _ Hc.
      destruct d as [|[seg off] d]; [|destruct seg];
        simpl in Hno |- *; try contradiction.
      all: by rewrite decide_True //=; repeat (lia || f_equal). }
    all: repeat ((case_decide || case_match); destruct_and?; subst => //).
    by rewrite !right_id_L.
  Qed.

  Theorem canon_wf src dst : roff_canon src dst -> raw_offset_wf dst.
  Proof. intros ?%canon_wf_0. exact: canon_wf'. Qed.

  Definition raw_offset_merge (o1 o2 : raw_offset) : raw_offset :=
    raw_offset_collapse (o1 ++ o2).
  Arguments raw_offset_merge !_ _ /.

  Definition offset := {ro : raw_offset | raw_offset_wf ro}.
  #[global] Instance offset_eq_dec : EqDecision offset := _.

  #[local] Definition raw_offset_to_offset (ro : raw_offset) : option offset :=
    match decide (raw_offset_wf ro) with
    | left Hwf => Some (exist _ ro Hwf)
    | right _ => None
    end.
  #[global] Instance offset_countable : Countable offset.
  Proof.
    apply (inj_countable proj1_sig raw_offset_to_offset) => -[ro Hwf] /=.
    rewrite /raw_offset_to_offset; case_match => //.
    by rewrite (proof_irrel Hwf).
  Qed.

  Program Definition o_id : offset := [] ↾ _.
  Next Obligation. done. Qed.
  Program Definition mkOffset σ (ro : raw_offset_seg)
    (Hn0 : isnt ro (o_sub_ _ 0)) : offset :=
    [mk_offset_seg σ ro] ↾ singleton_raw_offset_wf _.
  Next Obligation.
    rewrite /mk_offset_seg; intros ? [] H => //=; repeat case_match => //.
  Qed.
  Definition o_invalid σ : offset := mkOffset σ o_invalid_ I.
  Definition o_field σ f : offset :=
    mkOffset σ (o_field_ f) I.
  Definition o_base σ derived base : offset :=
    mkOffset σ (o_base_ derived base) I.
  Definition o_derived σ base derived : offset :=
    mkOffset σ (o_derived_ base derived) I.
  (** Qualifiers do not distinguish subscript paths: [type_ptr_erase] requires
      their one-past pointers to share the same representation as well. *)
  #[program] Definition o_sub σ ty z : offset :=
    let ty := erase_qualifiers ty in
    if decide (z = 0)%Z
    then
      match size_of σ ty with
      | Some _ => o_id
      | None => o_invalid σ
      end
    else
    mkOffset σ (o_sub_ ty z) _.
  Next Obligation. intros; case_match; simplify_eq/=; case_match; naive_solver. Qed.

  Lemma o_sub_erase σ ty z :
    o_sub σ (erase_qualifiers ty) z = o_sub σ ty z.
  Proof.
    apply (sig_eq_pi _).
    rewrite /o_sub /= erase_qualifiers_idemp. by case_decide.
  Qed.

  Lemma last_last_equiv {X} d {xs : list X} : default d (last xs) = List.last xs d.
  Proof. elim: xs => // x1 xs /= <-. by case_match. Qed.
(*
  Section merge_elem.
    Context {X} (f : X -> X -> list X).
    Context (Hinv : ∀ x1 x2, merge_elems f (f x1 x2) = f x1 x2).

    #[global] Instance invol_merge_elems: Involutive (merge_elems f).
    Proof.
    Admitted.

    #[global] Instance invol_app_merge_elems: InvolApp (merge_elems f).
    Proof.
    Admitted.
  End merge_elem.
  #[local] Arguments merge_elems {X} f !_ /. *)

  Definition offset_seg_append : offset_seg -> raw_offset -> raw_offset :=
    offset_seg_cons.
(*
  Lemma offset_seg_cons_inv x1 x2 :
    raw_offset_collapse (offset_seg_cons x1 x2) = offset_seg_cons x1 x2.
  Proof.
    move=> /= [o1 off1] [o2 off2].
    destruct o1, o2 => //=; by repeat (case_decide; simpl).
  Qed. *)

  #[local] Definition test xs :=
    raw_offset_collapse (raw_offset_collapse xs) = raw_offset_collapse xs.

  Section tests.
    Ltac start := intros; red; simpl.
    Ltac step_true := rewrite ?decide_True //=.
    Ltac step_false := rewrite ?decide_False //=.
    Ltac res_true := start; repeat step_true.
    Ltac res_false := start; repeat step_false.

    Goal test []. Proof. res_true. Qed.
    Goal `{n1 <> 0 -> test [(o_sub_ ty n1, o1)] }.
    Proof. res_false; naive_solver. Qed.
    Goal `{n1 <> 0 -> n2 <> 0 -> n2 + n1 <> 0 -> test [(o_sub_ ty n1, o1); (o_sub_ ty n2, o2)] }.
    Proof. res_false; naive_solver. Qed.

    (* Goal `{test [(o_sub_ ty n1, o1); (o_sub_ ty n2, o2); (o_field_ f, o3)] }.
    Proof. res_true. Qed.

    Goal `{test [(o_field_ f, o1); (o_sub_ ty n1, o2); (o_sub_ ty n2, o3)] }.
    Proof. res_true. Qed.

    Goal `{ty1 ≠ ty2 → test [(o_sub_ ty1 n1, o1); (o_sub_ ty2 n2, o2); (o_field_ f, o3)] }.
    Proof. res_false. Qed.

    Goal `{ty1 ≠ ty2 → test [(o_sub_ ty1 n1, o1); (o_sub_ ty1 n2, o2); (o_sub_ ty2 n3, o3); (o_field_ f, o4)] }.
    Proof. start. step_false. step_true. step_false. Qed. *)
  End tests.

  (* This is probably sound, since it allows temporary underflows. *)
  Definition eval_offset_seg (os : offset_seg) : option Z :=
    match os with
    | (o_invalid_, _) => None
    | (_, z) => Some z
    end.
  Definition eval_raw_offset (o : raw_offset) : option Z :=
    foldr (liftM2 Z.add) (Some 0) (map eval_offset_seg o).
  Definition eval_offset (_ : genv) (o : offset) : option Z :=
    eval_raw_offset (`o).
  (* This is probably not generally applicable. *)
  Local Arguments liftM2 {_ _ _ _ _ _} _ !_ !_ / : simpl nomatch.

  Lemma eval_offset_nil :
    forall {σ : genv} (wf : raw_offset_wf []),
      eval_offset σ ([] ↾ wf) = Some 0.
  Proof. by unfold eval_offset, eval_raw_offset; simpl. Qed.

  Lemma eval_o_sub' σ ty (i : Z) sz :
    size_of σ ty = Some sz ->
    eval_offset σ (o_sub σ ty i) = Some (Z.of_N sz * i).
  Proof.
    move=> E. rewrite (comm_L _ _ i) /o_sub/eval_offset/eval_raw_offset /=.
    rewrite /mkOffset /mk_offset_seg/=/o_sub_off/=.
    case_decide; subst; rewrite /= size_of_erase_qualifiers {}E //=.
    by rewrite right_id_L.
  Qed.

  Lemma eval_o_field σ f n cls st :
    f = Field cls n ->
    glob_def σ cls = Some (Gstruct st) ->
    st.(s_layout) = POD \/ st.(s_layout) = Standard ->
    eval_offset σ (o_field σ f) = offset_of σ cls n.
  Proof.
    move => -> _ _.
    rewrite /eval_offset/= /mk_offset_seg /eval_raw_offset /=.
    case: offset_of => /= [off|//]. by rewrite right_id_L.
  Qed.

  Lemma eval_o_base σ (cls base : globname) st :
    glob_def σ cls = Some (Gstruct st) ->
    st.(s_layout) = POD \/ st.(s_layout) = Standard ->
    eval_offset σ (o_base σ cls base) = parent_offset σ cls base.
  Proof.
    move => _ _.
    rewrite /eval_offset/= /mk_offset_seg/= /eval_raw_offset /o_base_off.
    case: parent_offset => [off|//] /=. by rewrite right_id_L.
  Qed.

  Class InvolApp {X} (f : list X → list X) :=
    invol_app : ∀ xs1 xs2,
    f (xs1 ++ xs2) = f (f xs1 ++ f xs2).
  Class Involutive {X} (f : X → X) :=
    invol : ∀ x, f (f x) = f x.
  Lemma raw_offset_collapse_length xs :
    length (raw_offset_collapse xs) <= length xs.
  Proof.
    induction xs as [|[[f|ty n|derived base|base derived|] off] xs IH] => //=;
      rewrite /offset_seg_cons /=.
    all: move E: (raw_offset_collapse xs) => r in IH |- *.
    all: destruct r as [|[[f'|ty' n'|derived' base'|base' derived'|] off'] r].
    all: simpl in IH |- *; repeat case_decide; simpl in *; lia.
  Qed.

  Lemma raw_offset_collapse_wf_tail os oss :
    raw_offset_collapse (os :: oss) = os :: oss ->
    raw_offset_collapse oss = oss.
  Proof.
    rewrite /= /offset_seg_cons.
    move E: (raw_offset_collapse oss) => r.
    destruct os as [[f|ty n|derived base|base derived|] off];
      destruct r as [|[[f'|ty' n'|derived' base'|base' derived'|] off'] r] => /=;
      repeat case_decide; simplify_eq/=;
      intros Hx; try solve [naive_solver].
    all: have B := raw_offset_collapse_length oss; rewrite E in B; simpl in B.
    all: have L := f_equal (@length _) Hx; simpl in L; lia.
  Qed.

  #[global] Instance raw_offset_collapse_involutive :
    Involutive raw_offset_collapse.
  Proof.
    intros xs.
    induction xs as [|[[f|ty n|derived base|base derived|] off] xs IH] => //=.
    - by f_equal.
    - rewrite /offset_seg_cons /=.
      move E: (raw_offset_collapse xs) => ys.
      rewrite E in IH |- *.
      destruct ys as [|[[f'|ty' n'|derived' base'|base' derived'|] off'] ys] => //=.
      all: repeat case_decide; simplify_eq/=; try congruence; try lia.
      all: try have IH' := raw_offset_collapse_wf_tail _ _ IH.
      all: repeat case_decide; simplify_eq/=; rewrite ?IH ?IH' //; try lia.
      all: try have IHtail : raw_offset_collapse ys = ys :=
        raw_offset_collapse_wf_tail _ _ IH.
      all: repeat case_decide; simplify_eq/=; rewrite ?IHtail //; try lia.
      apply (raw_offset_collapse_wf_tail (o_sub_ ty' n', off') ys).
      rewrite /= /offset_seg_cons decide_False //.
      destruct H0; subst; simpl; f_equal; lia.
      have IHtail : raw_offset_collapse ys = ys.
      { apply (raw_offset_collapse_wf_tail (o_sub_ ty' n', off') ys).
        rewrite /= /offset_seg_cons decide_False //. }
      rewrite IHtail in IH |- *.
      destruct ys as [|[[f''|ty'' n''|derived'' base''|base'' derived''|] off''] ys].
      all: simpl in IH |- *.
      all: try done.
      repeat case_decide; simplify_eq/=; try done.
      all: exfalso; first
        [ have L := f_equal (@length _) IH; simpl in L; lia
        | have L := f_equal (@length _) H6; simpl in L; lia ].
    - move E: (raw_offset_collapse xs) => ys in IH |- *.
      have Hkeep (os : offset_seg) :
        raw_offset_collapse (os :: ys) = offset_seg_cons os ys.
      { change (offset_seg_cons os (raw_offset_collapse ys) = offset_seg_cons os ys).
        by rewrite IH. }
      destruct ys as [|[[f'|ty' n'|derived' base'|base' derived'|] off'] ys].
      all: try by rewrite Hkeep.
      case_decide.
      { exact (raw_offset_collapse_wf_tail _ _ IH). }
      by rewrite Hkeep /offset_seg_cons decide_False.
    - rewrite /offset_seg_cons /=.
      move E: (raw_offset_collapse xs) => ys in IH |- *.
      destruct ys as [|[[f'|ty' n'|derived' base'|base' derived'|] off'] ys].
      all: simpl in IH |- *.
      all: repeat case_decide; simplify_eq/=; try congruence.
      { have B := raw_offset_collapse_length ys.
        rewrite IH in B; simpl in B; lia. }
      { have IHtail : raw_offset_collapse ys = ys.
        { apply (raw_offset_collapse_wf_tail (o_sub_ ty' n', off') ys).
          rewrite /= /offset_seg_cons decide_False //. }
        rewrite IHtail in IH |- *.
        by rewrite IH. }
      { exact (raw_offset_collapse_wf_tail (o_base_ derived' base', off') ys IH). }
      rewrite IH decide_False; last done.
      done.
      have IHtail : raw_offset_collapse ys = ys.
      { apply (raw_offset_collapse_wf_tail (o_derived_ base' derived', off') ys).
        rewrite /= /offset_seg_cons. exact IH. }
      rewrite IHtail in IH |- *.
      rewrite IH.
      all: done.
  Qed.
  Lemma raw_offset_collapse_wf_singleton os oss :
    raw_offset_collapse (os :: oss) = os :: oss ->
    raw_offset_collapse [os] = [os].
  Proof.
    destruct os as [[f|ty n|derived base|base derived|] off] => /=;
      rewrite /offset_seg_cons /=;
      repeat case_decide; simplify_eq/=; try done.
    intros Hx.
    have B := raw_offset_collapse_length oss.
    have L := f_equal (@length _) Hx.
    simpl in L; lia.
  Qed.

  Lemma offset_seg_cons_assoc os1 os2 zs :
    raw_offset_collapse [os2] = [os2] ->
    raw_offset_collapse zs = zs ->
    foldr offset_seg_cons zs (offset_seg_cons os1 [os2]) =
      offset_seg_cons os1 (offset_seg_cons os2 zs).
  Proof.
    intros H2 Hzs.
    destruct os1 as [[f1|ty1 n1|derived1 base1|base1 derived1|] off1];
      destruct os2 as [[f2|ty2 n2|derived2 base2|base2 derived2|] off2];
      destruct zs as [|[[f3|ty3 n3|derived3 base3|base3 derived3|] off3] zs];
      rewrite /= /offset_seg_cons /= in H2 Hzs |- *;
      repeat case_decide; simplify_eq/=; try done; try lia.
    all: repeat (case_decide; simplify_eq/=); try done; try lia.
    - destruct H; subst.
      have B := raw_offset_collapse_length zs.
      rewrite Hzs in B. simpl in B. lia.
    - f_equal.
      f_equal; try lia.
      f_equal; lia.
    - destruct H4 as [Hn12 Hoff12].
      destruct H6 as [Hn32 Hoff32].
      have En : n1 = n3 by lia.
      have Eoff : off1 = off3 by lia.
      subst n1 off1.
      have HW : raw_offset_collapse ((o_sub_ ty3 n3, off3) :: zs) =
          (o_sub_ ty3 n3, off3) :: zs.
      { rewrite /= /offset_seg_cons decide_False; [exact Hzs|done]. }
      have HT := raw_offset_collapse_wf_tail _ _ HW.
      rewrite HT in Hzs. symmetry. exact Hzs.
    - f_equal.
      f_equal; try lia.
      f_equal; lia.
    - have HW : raw_offset_collapse ((o_sub_ ty3 n3, off3) :: zs) =
          (o_sub_ ty3 n3, off3) :: zs.
      { rewrite /= /offset_seg_cons decide_False; [exact Hzs|done]. }
      have HT := raw_offset_collapse_wf_tail _ _ HW.
      destruct zs as [|[[f|ty n|derived base|base derived|] off] zs].
      all: rewrite /= /offset_seg_cons /= in HT HW |- *.
      all: repeat (case_decide; simplify_eq/=); try done; try lia.
      all: try solve [repeat f_equal; lia].
      destruct H7; subst.
      have B := raw_offset_collapse_length zs.
      rewrite HT in B. simpl in B. lia.
      rewrite HT in HW.
      rewrite decide_False in HW; [|congruence].
      case_decide; simplify_eq/=.
      have L := f_equal (@length _) HW. simpl in L. lia.
      have L := f_equal (@length _) H11. simpl in L. lia.
      rewrite HT in HW.
      rewrite decide_False in HW; [|congruence].
      case_decide; simplify_eq/=.
      all: try match goal with
        | Hx : ?xs = _ :: ?xs |- _ =>
            have L := f_equal (@length _) Hx; simpl in L; lia
        | Hx : ?xs = _ :: _ :: ?xs |- _ =>
            have L := f_equal (@length _) Hx; simpl in L; lia
        end.
    - f_equal.
      f_equal; try lia.
      f_equal; lia.
    - destruct H as [-> [-> H12]].
      destruct H0 as [-> [-> H23]].
      have Eoff : off1 = off3 by lia.
      subst off1.
      have Htail := raw_offset_collapse_wf_tail (o_base_ derived3 base3, off3) zs Hzs.
      rewrite Htail in Hzs.
      exact (eq_sym Hzs).
    - destruct H as [-> [-> H12]].
      destruct H0 as [-> [-> H23]].
      have Eoff : off1 = off3 by lia. subst off1.
      have Htail := raw_offset_collapse_wf_tail (o_derived_ base3 derived3, off3) zs Hzs.
      rewrite Htail in Hzs. exact (eq_sym Hzs).
  Qed.

  Lemma offset_seg_cons_cons os1 os2 xs :
    isnt os1 (o_invalid_, _) ->
    offset_seg_cons os1 (os2 :: xs) =
      offset_seg_cons os1 [os2] ++ xs.
  Proof.
    destruct os1 as [[f1|ty1 n1|derived1 base1|base1 derived1|] off1];
      destruct os2 as [[f2|ty2 n2|derived2 base2|base2 derived2|] off2];
      rewrite /offset_seg_cons /=;
      repeat case_decide; simplify_eq/=; done.
  Qed.

  Lemma offset_seg_cons_foldr os xs zs :
    raw_offset_collapse xs = xs ->
    raw_offset_collapse zs = zs ->
    foldr offset_seg_cons zs (offset_seg_cons os xs) =
      offset_seg_cons os (foldr offset_seg_cons zs xs).
  Proof.
    intros Hxs Hzs.
    destruct xs as [|os2 xs].
    { destruct os as [[f|ty n|derived base|base derived|] off];
        rewrite /offset_seg_cons /=;
        repeat case_decide; simplify_eq/=; rewrite ?decide_False //. }
    have H2 : raw_offset_collapse [os2] = [os2] :=
      raw_offset_collapse_wf_singleton _ _ Hxs.
    have Htail : raw_offset_collapse xs = xs :=
      raw_offset_collapse_wf_tail _ _ Hxs.
    have ER : foldr offset_seg_cons zs xs =
        raw_offset_collapse (xs ++ zs).
    { unfold raw_offset_collapse in Hzs |- *. by rewrite foldr_app Hzs. }
    have HR : raw_offset_collapse (foldr offset_seg_cons zs xs) =
        foldr offset_seg_cons zs xs.
    { rewrite ER. apply invol. }
    destruct os as [[f|ty n|derived base|base derived|] off].
    all: try rewrite offset_seg_cons_cons // foldr_app.
    rewrite /offset_seg_cons //.
    change (foldr offset_seg_cons (foldr offset_seg_cons zs xs)
      (offset_seg_cons (o_sub_ ty n, off) [os2]) =
      offset_seg_cons (o_sub_ ty n, off)
        (offset_seg_cons os2 (foldr offset_seg_cons zs xs))).
    exact (offset_seg_cons_assoc _ _ _ H2 HR).
    exact (offset_seg_cons_assoc _ _ _ H2 HR).
    change (foldr offset_seg_cons (foldr offset_seg_cons zs xs)
      (offset_seg_cons (o_derived_ base derived, off) [os2]) =
      offset_seg_cons (o_derived_ base derived, off)
        (offset_seg_cons os2 (foldr offset_seg_cons zs xs))).
    exact (offset_seg_cons_assoc _ _ _ H2 HR).
    rewrite /offset_seg_cons //.
  Qed.

  Lemma raw_offset_collapse_foldr xs zs :
    raw_offset_collapse zs = zs ->
    foldr offset_seg_cons zs (raw_offset_collapse xs) =
      foldr offset_seg_cons zs xs.
  Proof.
    intros Hzs.
    induction xs as [|os xs IH] => //=.
    rewrite offset_seg_cons_foldr.
    - by rewrite IH.
    - apply invol.
    - exact Hzs.
  Qed.

  #[global] Instance raw_offset_collapse_invol_app : InvolApp raw_offset_collapse.
  Proof.
    intros xs1 xs2.
    rewrite /raw_offset_collapse !foldr_app.
    change (foldr offset_seg_cons (raw_offset_collapse xs2) xs1 =
      foldr offset_seg_cons (raw_offset_collapse (raw_offset_collapse xs2))
        (raw_offset_collapse xs1)).
    rewrite invol.
    symmetry. apply raw_offset_collapse_foldr. apply invol.
  Qed.

  Program Definition __o_dot : offset → offset → offset :=
    λ o1 o2, (raw_offset_merge (proj1_sig o1) (proj1_sig o2)) ↾ _.
  Next Obligation.
    move=> o1 o2 /=.
    exact: raw_offset_collapse_involutive.
  Qed.

  Lemma __o_dot_nil_r :
    forall o (wf_o : raw_offset_wf o) (wf_nil : raw_offset_wf []),
      __o_dot (o ↾ wf_o) ([] ↾ wf_nil) = o ↾ wf_o.
  Proof.
    intros **.
    unfold __o_dot, raw_offset_merge, raw_offset_collapse; simpl.
    induction o=> //=.
    - rewrite (proof_irrel (__o_dot_obligation_1 ([] ↾ wf_o) ([] ↾ wf_nil))).
      by rewrite (proof_irrel wf_o).
    - rewrite (proof_irrel (__o_dot_obligation_1 ((a :: o) ↾ wf_o) ([] ↾ wf_nil))). 1: {
        unfold raw_offset_wf, raw_offset_collapse, raw_offset_merge; simpl.
        rewrite app_nil_r.
        unfold raw_offset_merge, raw_offset_collapse in wf_o; simpl in wf_o.
        rewrite wf_o.
        done.
      }
      unfold raw_offset_merge, raw_offset_collapse; simpl; rewrite app_nil_r.
      unfold raw_offset_wf, raw_offset_collapse in wf_o; simpl in wf_o.
      rewrite wf_o; intros wf_o'.
      by erewrite (proof_irrel wf_o).
  Qed.

  Inductive root_ptr : Set :=
  | nullptr_
  | global_ptr_ (tu : translation_unit_canon) (o : obj_name)
  | fun_ptr_ (tu : translation_unit_canon) (o : obj_name)
  | alloc_ptr_ (a : alloc_id) (va : vaddr).

  #[local] Instance root_ptr_eq_dec : EqDecision root_ptr.
  Proof. solve_decision. Defined.
  #[global] Declare Instance root_ptr_countable : Countable root_ptr.
  #[global] Instance global_ptr__inj : Inj2 (=) (=) (=) global_ptr_.
  Proof. by intros ???? [=]. Qed.

  Definition root_ptr_alloc_id (rp : root_ptr) : option alloc_id :=
    match rp with
    | nullptr_ => Some null_alloc_id
    | global_ptr_ tu o => Some (global_ptr_encode_aid o)
    | fun_ptr_ tu o => Some (global_ptr_encode_aid o)
    | alloc_ptr_ aid _ => Some aid
    end.

  Definition root_ptr_vaddr (rp : root_ptr) : option vaddr :=
    match rp with
    | nullptr_ => Some 0%N
    | global_ptr_ tu o => Some (global_ptr_encode_vaddr o)
    | fun_ptr_ tu o => Some (global_ptr_encode_vaddr o)
    | alloc_ptr_ aid va => Some va
    end.

  Inductive ptr_ : Set :=
  | invalid_ptr_
  | offset_ptr (p : root_ptr) (o : offset).
  Definition ptr := ptr_.
  #[global] Instance ptr_eq_dec : EqDecision ptr.
  Proof. solve_decision. Defined.
  #[global] Instance ptr_countable : Countable ptr.
  Proof.
    apply (inj_countable
      (fun p : ptr => match p with
         | invalid_ptr_ => None
         | offset_ptr root off => Some (root, off)
         end)
      (fun encoded => Some (match encoded with
         | None => invalid_ptr_
         | Some (root, off) => offset_ptr root off
         end))).
    by intros [|root off].
  Qed.
  #[global] Instance offset_ptr_inj : Inj2 (=) (=) (=) offset_ptr.
  Proof. by intros ???? [=]. Qed.

  Definition ptr_alloc_id (p : ptr) : option alloc_id :=
    match p with
    | invalid_ptr_ => None
    | offset_ptr p o => root_ptr_alloc_id p
    end.

  (** Invalid layout segments have no address, even when their numeric offset
      is zero. Retain the existing underflow checks for defined paths. *)
  Definition ptr_vaddr {σ} (p : ptr) : option vaddr :=
    match p with
    | invalid_ptr_ => None
    | offset_ptr p o =>
      match eval_raw_offset (`o) with
      | None => None
      | Some _ =>
        foldr
          (λ off ova, ova ≫= offset_vaddr off)
          (root_ptr_vaddr p)
          (snd <$> `o)
      end
    end.

  Definition lift_root_ptr (rp : root_ptr) : ptr := offset_ptr rp o_id.
  Definition invalid_ptr := invalid_ptr_.
  Definition fun_ptr tu o := lift_root_ptr (fun_ptr_ (canonical_tu.tu_to_canon tu) o).

  Definition null_alloc_id : alloc_id := null_alloc_id.
  Definition nullptr := lift_root_ptr nullptr_.
  Definition global_ptr (tu : translation_unit) o :=
    lift_root_ptr (global_ptr_ (canonical_tu.tu_to_canon tu) o).
  Definition alloc_ptr a oid := lift_root_ptr (alloc_ptr_ a oid).

  Lemma global_ptr_nonnull tu o : global_ptr tu o <> nullptr.
  Proof. done. Qed.

  #[global] Instance global_ptr_inj tu : Inj (=) (=) (global_ptr tu) := _.

  Section with_genv.
    Context {σ}.

    (* Some proofs using these helpers could be shortened, tactic-wise, but I find
    them clearer this way, and they work in both models. *)
    Lemma ptr_vaddr_global_ptr tu o :
      ptr_vaddr (global_ptr tu o) = Some (global_ptr_encode_vaddr o).
    Proof. done. Qed.
    Lemma ptr_alloc_id_global_ptr tu o :
      ptr_alloc_id (global_ptr tu o) = Some (global_ptr_encode_aid o).
    Proof. done. Qed.

    Lemma global_ptr_nonnull_addr tu o : ptr_vaddr (global_ptr tu o) <> Some 0%N.
    Proof.
      rewrite ptr_vaddr_global_ptr.
      intros [= H].
      exact (global_ptr_encode_vaddr_nonnull o _ eq_refl H).
    Qed.
    Lemma global_ptr_nonnull_aid tu o : ptr_alloc_id (global_ptr tu o) <> Some null_alloc_id.
    Proof.
      rewrite ptr_alloc_id_global_ptr.
      intros [= H].
      exact (global_ptr_encode_vaddr_nonnull o _ eq_refl H).
    Qed.

    Lemma global_ptr_addr_inj tu o1 o2 ty1 ty2 init1 init2 sz1 sz2 :
      tu ⊧ σ ->
      tu.(translation_unit.symbols) !! o1 = Some (Ovar ty1 init1) ->
      tu.(translation_unit.symbols) !! o2 = Some (Ovar ty2 init2) ->
      size_of σ ty1 = Some sz1 -> (0 < sz1)%N ->
      size_of σ ty2 = Some sz2 -> (0 < sz2)%N ->
      same_property ptr_vaddr (global_ptr tu o1) (global_ptr tu o2) ->
      o1 = o2.
    Proof.
      intros _ _ _ _ _ _ _ (va & H1 & H2)%same_property_iff.
      rewrite !ptr_vaddr_global_ptr in H1 H2.
      apply (inj global_ptr_encode_vaddr). congruence.
    Qed.
    #[global] Instance global_ptr_aid_inj tu : Inj (=) (=) (λ o, ptr_alloc_id (global_ptr tu o)).
    Proof. intros ??. rewrite !ptr_alloc_id_global_ptr. by intros ?%(inj _)%(inj _). Qed.

    Lemma ptr_vaddr_nullptr : ptr_vaddr nullptr = Some 0%N.
    Proof. done. Qed.

    Lemma ptr_alloc_id_nullptr : ptr_alloc_id nullptr = Some null_alloc_id.
    Proof. done. Qed.
  End with_genv.

  (* Instance ptr_equiv : Equiv ptr := (=).
  Instance offset_equiv : Equiv offset := (=).
  Instance ptr_equivalence : Equivalence (≡@{ptr}) := _.
  Instance offset_equivalence : Equivalence (==@{offset}) := _.
  Instance ptr_equiv_dec : RelDecision (≡@{ptr}) := _.
  Instance offset_equiv_dec : RelDecision (==@{offset}) := _. *)

  (* Instance dot_assoc : Assoc (≡) o_dot := _. *)
  (* Instance dot_proper : Proper ((≡) ==> (≡) ==> (≡)) o_dot := _. *)

  Definition __offset_ptr (p : ptr) (o : offset) : ptr :=
    match p with
    | offset_ptr p' o' => offset_ptr p' (__o_dot o' o)
    | invalid_ptr_ => invalid_ptr_ (* too eager! *)
    end.

  Include PTRS_SYNTAX_MIXIN.
  (* Duplicated. *)
  #[global] Notation "p ., o" := (_dot p (o_field _ o))
    (at level 11, left associativity, only parsing) : stdpp_scope.

  #[local] Ltac UNFOLD_dot := rewrite _dot.unlock/DOT_dot/=.

  Lemma eval_raw_offset_cons os oss :
    eval_raw_offset (os :: oss) =
      liftM2 Z.add (eval_offset_seg os) (eval_raw_offset oss).
  Proof. done. Qed.

  (* Normalization preserves the sum of the offsets, since every cancellation
  it performs is between segments whose offsets sum to [0]. *)
  Lemma eval_raw_offset_seg_cons os oss :
    eval_raw_offset (offset_seg_cons os oss) = eval_raw_offset (os :: oss).
  Proof.
    rewrite !eval_raw_offset_cons.
    destruct os as [[f|ty n|derived base|base derived|] off];
      destruct oss as [|[[f'|ty' n'|derived' base'|base' derived'|] off'] oss];
      rewrite /offset_seg_cons; repeat case_decide; destruct_and?; simplify_eq;
      rewrite ?eval_raw_offset_cons /=; try done.
    all: case: eval_raw_offset => [?|] //=; f_equal; lia.
  Qed.

  Lemma eval_raw_offset_collapse xs :
    eval_raw_offset (raw_offset_collapse xs) = eval_raw_offset xs.
  Proof.
    elim: xs => [//|x xs IH] /=.
    by rewrite eval_raw_offset_seg_cons !eval_raw_offset_cons IH.
  Qed.

  Lemma eval_raw_offset_app xs ys :
    eval_raw_offset (xs ++ ys) =
      liftM2 Z.add (eval_raw_offset xs) (eval_raw_offset ys).
  Proof.
    elim: xs => [|x xs IH] /=.
    { by case: eval_raw_offset. }
    rewrite !eval_raw_offset_cons IH.
    case: eval_offset_seg => [?|] //=; case: eval_raw_offset => [?|] //=;
      case: eval_raw_offset => [?|] //=; f_equal; lia.
  Qed.

  Lemma eval_offset_dot : ∀ σ (o1 o2 : offset),
    ∀ s1 s2,
      eval_offset σ o1 = Some s1 ->
      eval_offset σ o2 = Some s2 ->
      eval_offset σ (o1 ,, o2) = Some (s1 + s2).
  Proof.
    UNFOLD_dot. rewrite /eval_offset => σ [o1 ?] [o2 ?] s1 s2 /= E1 E2.
    by rewrite /raw_offset_merge eval_raw_offset_collapse eval_raw_offset_app E1 E2.
  Qed.
  (** Defined stored offsets exclude missing-layout segments, independently of
      whether a pointer has a concrete virtual address. *)
  Definition ptr_offset_defined (p : ptr) : Prop :=
    match p with
    | invalid_ptr_ => False
    | offset_ptr _ o => is_Some (eval_raw_offset (`o))
    end.

  Lemma ptr_offset_defined_dot σ p o :
    ptr_offset_defined (p ,, o) <->
    ptr_offset_defined p /\ is_Some (eval_offset σ o).
  Proof.
    UNFOLD_dot. destruct p as [|root off]; first naive_solver.
    rewrite /ptr_offset_defined /= /raw_offset_merge
      eval_raw_offset_collapse eval_raw_offset_app /eval_offset.
    destruct (eval_raw_offset (`off)), (eval_raw_offset (`o)); naive_solver.
  Qed.

  Lemma eval_o_sub_defined σ ty i :
    is_Some (eval_offset σ (o_sub σ ty i)) -> is_Some (size_of σ ty).
  Proof.
    rewrite /o_sub; case_decide;
      rewrite /eval_offset /eval_raw_offset /= /mkOffset /mk_offset_seg /=
        /o_sub_off size_of_erase_qualifiers;
      destruct (size_of σ ty); naive_solver.
  Qed.


  (** A defined field appends a segment without changing its parent path. *)
  #[local] Lemma offset_seg_cons_field_app os xs f z ys :
    is_Some (eval_offset_seg os) ->
    offset_seg_cons os (xs ++ (o_field_ f,z) :: ys) =
      offset_seg_cons os xs ++ (o_field_ f,z) :: ys.
  Proof.
    destruct os as [[f1|ty1 n1|der1 base1|base1 der1|] z1];
      destruct xs as [|[[f2|ty2 n2|der2 base2|base2 der2|] z2] xs];
      rewrite /eval_offset_seg /= /offset_seg_cons /=;
      repeat case_decide; naive_solver.
  Qed.

  #[local] Lemma raw_offset_collapse_field_app xs f z ys :
    is_Some (eval_raw_offset xs) ->
    raw_offset_collapse (xs ++ (o_field_ f,z) :: ys) =
      raw_offset_collapse xs ++ (o_field_ f,z) :: raw_offset_collapse ys.
  Proof.
    induction xs as [|os xs IH]; first done.
    rewrite eval_raw_offset_cons.
    destruct (eval_offset_seg os) as [a|] eqn:Eos;
      destruct (eval_raw_offset xs) as [b|] eqn:Exs; simpl; try naive_solver.
    intros _. rewrite /= IH; last by eexists.
    apply offset_seg_cons_field_app. by eexists.
    all: intros [r Hr]; discriminate Hr.
  Qed.

  Lemma eval_o_field_defined σ f :
    is_Some (eval_offset σ (o_field σ f)) -> is_Some (o_field_off σ f).
  Proof.
    rewrite /eval_offset /eval_raw_offset /= /mk_offset_seg /=.
    destruct (o_field_off σ f); naive_solver.
  Qed.

  Lemma offset_field_raw σ o f z :
    is_Some (eval_offset σ o) -> o_field_off σ f = Some z ->
    proj1_sig (o ,, o_field σ f) = proj1_sig o ++ [(o_field_ f, z)].
  Proof.
    intros Ho Hf. rewrite _dot.unlock /DOT_dot /= /raw_offset_merge.
    rewrite /o_field /mkOffset /mk_offset_seg /= Hf /=.
    rewrite raw_offset_collapse_field_app; [by rewrite (proj2_sig o)|exact Ho].
  Qed.

  Lemma field_ptr_ne_null σ (p : ptr) f : p ,, o_field σ f <> nullptr.
  Proof.
    intros Heq.
    have Hdefined : ptr_offset_defined (p ,, o_field σ f).
    { rewrite Heq. by exists 0. }
    apply (ptr_offset_defined_dot σ) in Hdefined as [Hp Hf].
    have [z Hz] := eval_o_field_defined σ f Hf.
    destruct p as [|root off]; first exact Hp.
    apply (f_equal (fun p => match p with
      | invalid_ptr_ => [] | offset_ptr _ off => proj1_sig off end)) in Heq.
    rewrite _dot.unlock /DOT_dot /= in Heq.
    have Hraw := offset_field_raw σ off f z Hp Hz.
    rewrite _dot.unlock /DOT_dot /= in Hraw.
    rewrite Hraw in Heq.
    have Hlen := f_equal (@length _) Heq. rewrite length_app /= in Hlen. lia.
  Qed.

  (** A nonzero subscript after a field retains that field as a proper prefix. *)
  Lemma offset_field_sub_raw σ o f z ty i sz :
    is_Some (eval_offset σ o) -> o_field_off σ f = Some z ->
    size_of σ ty = Some sz -> i <> 0 ->
    proj1_sig ((o ,, o_field σ f) ,, o_sub σ ty i) =
      proj1_sig (o ,, o_field σ f) ++
        [(o_sub_ (erase_qualifiers ty) i, Z.of_N sz * i)].
  Proof.
    intros Ho Hf Hsz Hi.
    have Hfield := offset_field_raw σ o f z Ho Hf.
    rewrite _dot.unlock /DOT_dot /= in Hfield |- *.
    rewrite Hfield /raw_offset_merge /o_sub.
    case_decide; first contradiction.
    rewrite /mkOffset /mk_offset_seg /= /o_sub_off size_of_erase_qualifiers Hsz /=.
    rewrite -app_assoc /= raw_offset_collapse_field_app; last exact Ho.
    rewrite (proj2_sig o) /= /offset_seg_cons decide_False; last naive_solver.
    by rewrite -app_assoc /= (Z.mul_comm i).
  Qed.

  Lemma field_sub_ptr_ne_null σ (p : ptr) f ty i :
    i <> 0 -> p ,, o_field σ f ,, o_sub σ ty i <> nullptr.
  Proof.
    intros Hi Heq.
    have Hdefined : ptr_offset_defined (p ,, o_field σ f ,, o_sub σ ty i).
    { rewrite Heq. by exists 0. }
    apply (ptr_offset_defined_dot σ) in Hdefined as [Hpf Hsub].
    apply (ptr_offset_defined_dot σ) in Hpf as [Hp Hf].
    have [z Hz] := eval_o_field_defined σ f Hf.
    have [sz Hsz] := eval_o_sub_defined σ ty i Hsub.
    destruct p as [|root off]; first exact Hp.
    apply (f_equal (fun p => match p with
      | invalid_ptr_ => [] | offset_ptr _ off => proj1_sig off end)) in Heq.
    rewrite _dot.unlock /DOT_dot /= in Heq.
    have Hraw := offset_field_sub_raw σ off f z ty i sz Hp Hz Hsz Hi.
    rewrite _dot.unlock /DOT_dot /= in Hraw.
    rewrite Hraw in Heq.
    have Hlen := f_equal (@length _) Heq. rewrite length_app /= in Hlen. lia.
  Qed.

  #[local] Lemma offset_seg_cons_full_length os xs :
    length (offset_seg_cons os xs) = S (length xs) ->
    offset_seg_cons os xs = os :: xs.
  Proof.
    destruct os as [[f|ty n|derived base|base derived|] off];
      destruct xs as [|[[f'|ty' n'|derived' base'|base' derived'|] off'] xs];
      rewrite /offset_seg_cons /=;
      repeat case_decide; simpl; intros; try done; try lia.
  Qed.

  #[local] Lemma offset_seg_cons_length os xs :
    (length (offset_seg_cons os xs) <= S (length xs))%nat.
  Proof.
    destruct os as [[f|ty n|derived base|base derived|] off];
      destruct xs as [|[[f'|ty' n'|derived' base'|base' derived'|] off'] xs];
      rewrite /offset_seg_cons /=;
      repeat case_decide; simpl; lia.
  Qed.

  #[local] Lemma raw_offset_collapse_full_length xs :
    length (raw_offset_collapse xs) = length xs ->
    raw_offset_collapse xs = xs.
  Proof.
    induction xs as [|os xs IH]; first done.
    intros Hlen.
    have Hcons := offset_seg_cons_length os (raw_offset_collapse xs).
    have Htail := raw_offset_collapse_length xs.
    have E : length (raw_offset_collapse xs) = length xs.
    { change (length (offset_seg_cons os (raw_offset_collapse xs)) = S (length xs)) in Hlen.
      lia. }
    rewrite /= (IH E) in Hlen |- *.
    exact (offset_seg_cons_full_length _ _ Hlen).
  Qed.

  #[local] Lemma raw_offset_collapse_wf_init xs ys :
    raw_offset_collapse (xs ++ ys) = xs ++ ys ->
    raw_offset_collapse xs = xs.
  Proof.
    intros Hwf. apply raw_offset_collapse_full_length.
    have Hbound := raw_offset_collapse_length
      (raw_offset_collapse xs ++ raw_offset_collapse ys).
    have Hx := raw_offset_collapse_length xs.
    have Hy := raw_offset_collapse_length ys.
    rewrite -invol_app Hwf !length_app in Hbound.
    lia.
  Qed.

  #[local] Lemma raw_offset_collapse_wf_suffix xs ys :
    raw_offset_collapse (xs ++ ys) = xs ++ ys ->
    raw_offset_collapse ys = ys.
  Proof.
    induction xs as [|os xs IH]; first done.
    intros Hwf. apply IH. exact (raw_offset_collapse_wf_tail _ _ Hwf).
  Qed.

  Definition subscript_separated (ty : type) (xs : raw_offset) : Prop :=
    forall before n z, xs <> before ++ [(o_sub_ ty n, z)].

  #[local] Lemma offset_seg_cons_app_defined os xs ys :
    is_Some (eval_offset_seg os) -> xs <> [] ->
    offset_seg_cons os (xs ++ ys) = offset_seg_cons os xs ++ ys.
  Proof.
    intros Hdef Hxs. destruct xs as [|os' xs]; first contradiction.
    destruct os as [[f|ty n|derived base|base derived|] off];
      destruct os' as [[f'|ty' n'|derived' base'|base' derived'|] off'];
      rewrite /offset_seg_cons /=;
      repeat case_decide; simpl in Hdef |- *; try done; naive_solver.
  Qed.


  Lemma raw_offset_collapse_base_snoc xs derived base z :
    raw_offset_collapse xs = xs -> is_Some (eval_raw_offset xs) ->
    (exists prefix, xs = prefix ++ [(o_derived_ base derived,(-z)%Z)] /\
      raw_offset_collapse (xs ++ [(o_base_ derived base,z)]) = prefix) \/
    raw_offset_collapse (xs ++ [(o_base_ derived base,z)]) = xs ++ [(o_base_ derived base,z)].
  Proof.
    induction xs as [|os xs IH]; intros Hwf Hdef; first by right.
    have Htail := raw_offset_collapse_wf_tail _ _ Hwf.
    rewrite eval_raw_offset_cons in Hdef.
    destruct (eval_offset_seg os) as [a|] eqn:Eos; last by destruct Hdef.
    destruct (eval_raw_offset xs) as [b|] eqn:Exs; last by destruct Hdef.
    destruct (IH Htail (ex_intro _ b eq_refl)) as [(prefix & -> & E)|E].

    - left. exists (os :: prefix). split; first done.
      change (offset_seg_cons os (raw_offset_collapse
        ((prefix ++ [(o_derived_ base derived,(-z)%Z)]) ++ [(o_base_ derived base,z)])) = os :: prefix).
      rewrite E.
      have Hpre := raw_offset_collapse_wf_init (os :: prefix)
        [(o_derived_ base derived,(-z)%Z)] Hwf.
      have Hp := raw_offset_collapse_wf_tail _ _ Hpre.
      by rewrite /= Hp in Hpre.
    - destruct xs as [|os' xs].
      + destruct os as [[f|ty n|d ba|ba d|] dz];
          rewrite /= /offset_seg_cons /= in Hwf Eos |- *; try (right; done).
        * case_decide; [by right|by right].
        * case_decide as Hcancel.
          -- destruct Hcancel as (-> & -> & Hz). left. exists [].
             split; last done. simpl. f_equal. f_equal. lia.
          -- by right.
      + right. change (offset_seg_cons os
          (raw_offset_collapse ((os' :: xs) ++ [(o_base_ derived base,z)])) =
          (os :: os' :: xs) ++ [(o_base_ derived base,z)]).
        rewrite E offset_seg_cons_app_defined; [|by exists a|discriminate].
        change (offset_seg_cons os (raw_offset_collapse (os' :: xs)) = os :: os' :: xs) in Hwf.
        by rewrite Htail in Hwf; rewrite Hwf.
  Qed.

  Lemma eval_o_base' σ derived base z :
    parent_offset σ derived base = Some z ->
    eval_offset σ (o_base σ derived base) = Some z.
  Proof.
    intros Hz. rewrite /eval_offset /o_base /mkOffset /mk_offset_seg /= /o_base_off Hz.
    change (Some (z+0)%Z = Some z). by rewrite Z.add_0_r.
  Qed.

  Lemma offset_base_raw σ (off : offset) derived base z :
    parent_offset σ derived base = Some z ->
    proj1_sig (off ,, o_base σ derived base) =
      raw_offset_collapse (proj1_sig off ++ [(o_base_ derived base,z)]).
  Proof.
    intros Hz. rewrite _dot.unlock /DOT_dot /= /raw_offset_merge.
    by rewrite /o_base /mkOffset /mk_offset_seg /= /o_base_off Hz.
  Qed.

  #[local] Lemma raw_offset_collapse_sub_separated xs ty n z :
    raw_offset_collapse xs = xs ->
    is_Some (eval_raw_offset xs) ->
    subscript_separated ty xs ->
    raw_offset_collapse (xs ++ [(o_sub_ ty n,z)]) =
      xs ++ raw_offset_collapse [(o_sub_ ty n,z)].
  Proof.
    induction xs as [|os xs IH]; first done.
    intros Hwf Hdef Hsep.
    have Htail := raw_offset_collapse_wf_tail _ _ Hwf.
    rewrite eval_raw_offset_cons in Hdef.
    destruct (eval_offset_seg os) as [v|] eqn:Eos;
      destruct (eval_raw_offset xs) as [w|] eqn:Exs;
      simpl in Hdef; try naive_solver.
    have Hsep' : subscript_separated ty xs.
    { intros before m d E. apply (Hsep (os :: before) m d). by rewrite E. }
    destruct xs as [|os' xs].
    - destruct os as [[f|ty' m|derived base|base derived|] d];
        rewrite /= /offset_seg_cons /= in Hwf |- *;
        repeat case_decide; simplify_eq/=; try done; try naive_solver.
      all: exfalso; exact (Hsep [] m v eq_refl).
    - change (offset_seg_cons os
        (raw_offset_collapse ((os' :: xs) ++ [(o_sub_ ty n,z)])) =
        os :: (os' :: xs) ++ raw_offset_collapse [(o_sub_ ty n,z)]).
      rewrite IH; [|exact Htail|by eexists|exact Hsep'].
      rewrite offset_seg_cons_app_defined; [|by eexists|discriminate].
      change (offset_seg_cons os (raw_offset_collapse (os' :: xs)) =
        os :: os' :: xs) in Hwf.
      rewrite Htail in Hwf. by rewrite Hwf.

  Qed.

  #[local] Lemma subscript_separated_nil ty : subscript_separated ty [].
  Proof.
    intros before n z E. have Hlen := f_equal (@length _) E.
    rewrite length_app /= in Hlen. lia.
  Qed.

  #[local] Lemma subscript_separated_snoc xs os ty :
    (forall n z, os <> (o_sub_ ty n,z)) ->
    subscript_separated ty (xs ++ [os]).
  Proof.
    intros Hneq before n z E.
    apply app_inj_tail in E as [_ E]. exact (Hneq n z E).
  Qed.

  #[local] Lemma canonical_subscript_prefix_separated xs ty n z :
    raw_offset_collapse (xs ++ [(o_sub_ ty n,z)]) =
      xs ++ [(o_sub_ ty n,z)] ->
    subscript_separated ty xs.
  Proof.
    intros Hwf before m d E. subst xs.
    rewrite -app_assoc in Hwf.
    have Hpair := raw_offset_collapse_wf_suffix _ _ Hwf.
    simpl in Hpair.
    rewrite /offset_seg_cons /= in Hpair.
    repeat case_decide; simplify_eq/=;
      have Hlen := f_equal (@length _) Hpair; simpl in Hlen; lia.
  Qed.

  #[local] Lemma eval_raw_offset_app_defined xs ys :
    is_Some (eval_raw_offset (xs ++ ys)) ->
    is_Some (eval_raw_offset xs) /\ is_Some (eval_raw_offset ys).
  Proof.
    rewrite eval_raw_offset_app.
    destruct (eval_raw_offset xs) as [x|];
      destruct (eval_raw_offset ys) as [y|]; simpl.
    - intros _. split; by eexists.
    - intros [r Hr]; discriminate Hr.
    - intros [r Hr]; discriminate Hr.
    - intros [r Hr]; discriminate Hr.
  Qed.

  #[local] Lemma raw_offset_subscript_decompose xs ty :
    raw_offset_collapse xs = xs ->
    is_Some (eval_raw_offset xs) ->
    exists prefix n z,
      raw_offset_collapse prefix = prefix /\
      is_Some (eval_raw_offset prefix) /\
      subscript_separated ty prefix /\
      xs = prefix ++ raw_offset_collapse [(o_sub_ ty n,z)].
  Proof.
    intros Hwf Hdef.
    destruct xs as [|os xs] using rev_ind.
    - exists [], 0%Z, 0%Z. repeat split; try done.
      apply subscript_separated_nil.
    - have Hpre := raw_offset_collapse_wf_init _ _ Hwf.
      have Hlast := raw_offset_collapse_wf_suffix _ _ Hwf.
      have [Hdefpre _] := eval_raw_offset_app_defined _ _ Hdef.
      have Hdifferent : (forall n z, os <> (o_sub_ ty n,z)) ->
        exists prefix n z,
          raw_offset_collapse prefix = prefix /\
          is_Some (eval_raw_offset prefix) /\
          subscript_separated ty prefix /\
          xs ++ [os] = prefix ++ raw_offset_collapse [(o_sub_ ty n,z)].
      { intros Hneq. exists (xs ++ [os]), 0%Z, 0%Z.
        repeat split; try assumption.
        - apply subscript_separated_snoc. exact Hneq.
        - by rewrite /= /offset_seg_cons /= app_nil_r. }
      destruct os as [[f|ty' m|derived base|base derived|] d].
      all: try (apply Hdifferent; intros n z; discriminate).
      destruct (decide (ty' = ty)) as [->|Hneq].
      + exists xs, m, d. repeat split; try assumption.
        * exact (canonical_subscript_prefix_separated _ _ _ _ Hwf).
        * by rewrite Hlast.
      + apply Hdifferent. intros n z E. injection E as E _ _. contradiction.
  Qed.

  #[local] Lemma raw_offset_collapse_sub_pair ty m d n z :
    raw_offset_collapse [(o_sub_ ty m,d); (o_sub_ ty n,z)] =
      raw_offset_collapse [(o_sub_ ty (m+n),(d+z)%Z)].
  Proof.
    rewrite /= /offset_seg_cons /=.
    repeat case_decide; simplify_eq/=; try done; try lia.
  all: f_equal; apply pair_equal_spec; split; [f_equal|]; lia.
  Qed.

  #[local] Lemma raw_offset_collapse_app_collapse_r xs ys :
    raw_offset_collapse (xs ++ raw_offset_collapse ys) =
      raw_offset_collapse (xs ++ ys).
  Proof.
    rewrite (invol_app xs (raw_offset_collapse ys)) invol.
    by rewrite -(invol_app xs ys).
  Qed.

  #[local] Lemma raw_offset_subscript_extend prefix ty m d n z :
    raw_offset_collapse prefix = prefix ->
    is_Some (eval_raw_offset prefix) ->
    subscript_separated ty prefix ->
    raw_offset_collapse
      ((prefix ++ raw_offset_collapse [(o_sub_ ty m,d)]) ++
        raw_offset_collapse [(o_sub_ ty n,z)]) =
      prefix ++ raw_offset_collapse [(o_sub_ ty (m+n),(d+z)%Z)].
  Proof.
    intros Hwf Hdef Hsep.
    rewrite -app_assoc (invol_app prefix
      (raw_offset_collapse [(o_sub_ ty m,d)] ++ raw_offset_collapse [(o_sub_ ty n,z)])).
    rewrite Hwf -(invol_app [(o_sub_ ty m,d)] [(o_sub_ ty n,z)]).
    rewrite raw_offset_collapse_sub_pair raw_offset_collapse_app_collapse_r.
    exact (raw_offset_collapse_sub_separated _ _ _ _ Hwf Hdef Hsep).
  Qed.

  #[local] Lemma o_sub_raw_collapse σ ty i sz :
    size_of σ ty = Some sz ->
    proj1_sig (o_sub σ ty i) =
      raw_offset_collapse [(o_sub_ (erase_qualifiers ty) i, Z.of_N sz * i)].
  Proof.
    intros Hsz. rewrite /o_sub.
    case_decide.
    - subst i. rewrite size_of_erase_qualifiers Hsz /= /offset_seg_cons /=.
      by rewrite Z.mul_0_r.
    - rewrite /mkOffset /mk_offset_seg /= /o_sub_off size_of_erase_qualifiers Hsz /=.
      rewrite /offset_seg_cons decide_False; last naive_solver.
      by rewrite Z.mul_comm.
  Qed.

  (** Every subscript shares a stable prefix; stored displacement and index
      are tracked independently, including zero stride and cancellation. *)
  Lemma offset_subscript_decompose σ off ty sz :
    is_Some (eval_offset σ off) ->
    size_of σ ty = Some sz ->
    exists prefix n z,
      raw_offset_collapse prefix = prefix /\
      is_Some (eval_raw_offset prefix) /\
      subscript_separated (erase_qualifiers ty) prefix /\
      forall i,
        proj1_sig (off ,, o_sub σ ty i) =
          prefix ++ raw_offset_collapse
            [(o_sub_ (erase_qualifiers ty) (n+i), (z + Z.of_N sz * i)%Z)].
  Proof.
    intros Hdef Hsz.
    destruct (raw_offset_subscript_decompose (proj1_sig off) (erase_qualifiers ty)
      (proj2_sig off) Hdef) as (prefix & n & z & Hwf & Hpre & Hsep & E).
    exists prefix, n, z. repeat split; try assumption.
    intros i. rewrite _dot.unlock /DOT_dot /= /raw_offset_merge.
    rewrite (o_sub_raw_collapse σ ty i sz Hsz) E.
    exact (raw_offset_subscript_extend _ _ _ _ _ _ Hwf Hpre Hsep).
  Qed.

  Lemma fold_subscript_collapse prefix ty n d root :
    foldr (fun off ova => ova ≫= offset_vaddr off) root
      (snd <$> (prefix ++ raw_offset_collapse [(o_sub_ ty n,d)])) =
    foldr (fun off ova => ova ≫= offset_vaddr off)
      (root ≫= offset_vaddr d) (snd <$> prefix).
  Proof.
    rewrite /= /offset_seg_cons /=.
    case_decide as Hzero.
    - destruct Hzero as [-> ->].
      rewrite app_nil_r.
      destruct root as [base|]; simpl; first by rewrite offset_vaddr_0.
      done.
    - by rewrite fmap_app foldr_app /=.
  Qed.

  Lemma eval_subscript_collapse prefix ty n d :
    eval_raw_offset (prefix ++ raw_offset_collapse [(o_sub_ ty n,d)]) =
      liftM2 Z.add (eval_raw_offset prefix) (Some d).
  Proof.
    rewrite eval_raw_offset_app eval_raw_offset_collapse /=.
    change (liftM2 Z.add (eval_raw_offset prefix) (Some (d+0)) =
      liftM2 Z.add (eval_raw_offset prefix) (Some d)).
    by rewrite Z.add_0_r.
  Qed.

  #[local] Lemma raw_subscript_empty_index prefix ty n d :
    prefix ++ raw_offset_collapse [(o_sub_ ty n,d)] = [] -> n = 0.
  Proof.
    intros [_ E]%app_eq_nil.
    rewrite /= /offset_seg_cons in E.
    case_decide; [tauto|discriminate].
  Qed.

  #[local] Lemma offset_subscript_empty_inj σ off ty sz i k :
    is_Some (eval_offset σ off) ->
    size_of σ ty = Some sz ->
    proj1_sig (off ,, o_sub σ ty i) = [] ->
    proj1_sig (off ,, o_sub σ ty k) = [] ->
    i = k.
  Proof.
    intros Hdef Hsz Hi Hk.
    destruct (offset_subscript_decompose σ off ty sz Hdef Hsz)
      as (prefix & n & d & _ & _ & _ & E).
    rewrite E in Hi. rewrite E in Hk.
    apply raw_subscript_empty_index in Hi.
    apply raw_subscript_empty_index in Hk.
    lia.
  Qed.

  Lemma subscript_null_inj σ (p : ptr) ty i k :
    p ,, o_sub σ ty i = nullptr ->
    p ,, o_sub σ ty k = nullptr ->
    i = k.
  Proof.
    intros Hi Hk.
    have Hdefined : ptr_offset_defined (p ,, o_sub σ ty i).
    { rewrite Hi. by exists 0. }
    apply (ptr_offset_defined_dot σ) in Hdefined as [Hp Hsub].
    have [sz Hsz] := eval_o_sub_defined σ ty i Hsub.
    destruct p as [|root off]; first exact (False_ind _ Hp).
    apply (f_equal (fun p => match p with
      | invalid_ptr_ => [] | offset_ptr _ off => proj1_sig off end)) in Hi.
    apply (f_equal (fun p => match p with
      | invalid_ptr_ => [] | offset_ptr _ off => proj1_sig off end)) in Hk.
    rewrite _dot.unlock /DOT_dot /= in Hi, Hk.
    apply (offset_subscript_empty_inj σ off ty sz i k Hp Hsz).
    - by rewrite _dot.unlock /DOT_dot /=.
    - by rewrite _dot.unlock /DOT_dot /=.
  Qed.

  #[global] Instance id_dot : LeftId (=) o_id o_dot.
  Proof. UNFOLD_dot. intros o. apply /sig_eq_pi. by case: o. Qed.
  Lemma __o_dot_id : RightId (=) o_id __o_dot.
  Proof.
    intros o. apply /sig_eq_pi.
    rewrite /= /raw_offset_merge (right_id []).
    by case: o.
  Qed.
  #[global] Instance dot_id : RightId (=) o_id o_dot.
  Proof. UNFOLD_dot. apply __o_dot_id. Qed.
  #[global] Instance dot_assoc : Assoc (=) o_dot.
  Proof.
    UNFOLD_dot.
    intros o1 o2 o3. apply /sig_eq_pi.
    move: o1 o2 o3 => [ro1 /= wf1]
      [ro2 /= wf2] [ro3 /= wf3].
      rewrite /raw_offset_merge.
      rewrite -{1}wf1 -{2}wf3.
      rewrite -!invol_app; f_equiv.
      apply: assoc.
  Qed.

  Implicit Types (p : ptr) (o : offset).

  Lemma offset_ptr_id p : p ,, o_id = p.
  Proof. UNFOLD_dot. case: p => // p o. by rewrite /__offset_ptr __o_dot_id. Qed.

  Lemma offset_ptr_dot p o1 o2 : p ,, (o1 ,, o2) = p ,, o1 ,, o2.
  Proof.
    have := dot_assoc; UNFOLD_dot => Hassoc.
    destruct p => //=. by rewrite Hassoc.
  Qed.

  Lemma o_sub_0 σ ty :
    is_Some (size_of σ ty) ->
    o_sub σ ty 0 = o_id.
  Proof.
    rewrite /o_sub; case_decide=>//. rewrite size_of_erase_qualifiers.
    by intros [sz ->].
  Qed.

  Lemma ptr_alloc_id_offset {p o} :
    let p' := p ,, o in
    is_Some (ptr_alloc_id p') -> ptr_alloc_id p' = ptr_alloc_id p.
  Proof. UNFOLD_dot. by destruct p, o as [[] ?] => //= /is_Some_None []. Qed.
  #[local] Lemma fold_offset_vaddr_sum offsets pa va :
    foldr (fun off ova => ova ≫= offset_vaddr off) (Some pa) offsets = Some va ->
    Z.of_N va = Z.of_N pa + foldr Z.add 0 offsets.
  Proof.
    revert va. induction offsets as [|z zs IH]; intros va; simpl.
    - intros [= <-]. lia.
    - destruct (foldr (fun off ova => ova ≫= offset_vaddr off)
        (Some pa) zs) as [mid|] eqn:E; simpl; last discriminate.
      have Hmid := IH mid eq_refl.
      rewrite /offset_vaddr /=. case_guard; last discriminate.
      intros [= <-]. rewrite Z2N.id; lia.
  Qed.

  #[local] Lemma eval_raw_offset_sum offsets z :
    eval_raw_offset offsets = Some z ->
    foldr Z.add 0 (snd <$> offsets) = z.
  Proof.
    revert z. induction offsets as [|[seg off] rest IH]; intros z.
    - simpl. by intros [= <-].
    - rewrite eval_raw_offset_cons.
      destruct seg; simpl; try discriminate;
        destruct (eval_raw_offset rest) as [n|] eqn:E; simpl; try discriminate;
        intros [= <-]; rewrite (IH n eq_refl); done.
  Qed.

  Lemma ptr_vaddr_offset_ptr_inv σ root off va :
    @ptr_vaddr σ (offset_ptr root off) = Some va ->
    exists base z, root_ptr_vaddr root = Some base /\
      eval_offset σ off = Some z /\ Z.of_N va = Z.of_N base + z.
  Proof.
    have [base Hbase] : is_Some (root_ptr_vaddr root).
    { destruct root; eexists; done. }
    rewrite /ptr_vaddr. destruct (eval_raw_offset (`off)) as [z|] eqn:E;
      last discriminate.
    rewrite Hbase. intros Haddr.
    exists base, z. split; first done. split; first done.
    rewrite (fold_offset_vaddr_sum _ _ _ Haddr).
    by rewrite (eval_raw_offset_sum _ _ E).
  Qed.
  Lemma ptr_vaddr_offset_add σ p o va va' z :
    @ptr_vaddr σ p = Some va ->
    ptr_vaddr (p ,, o) = Some va' ->
    eval_offset σ o = Some z ->
    Z.of_N va' = Z.of_N va + z.
  Proof.
    intros Hp Hpo Ho. destruct p as [|root off]; first discriminate.
    rewrite _dot.unlock /DOT_dot /= in Hpo.
    destruct (ptr_vaddr_offset_ptr_inv σ root off va Hp)
      as (base1 & z1 & B1 & E1 & A1).
    destruct (ptr_vaddr_offset_ptr_inv σ root (__o_dot off o) va' Hpo)
      as (base2 & z2 & B2 & E2 & A2).
    have Hb : base2 = base1 by congruence. subst base2.
    rewrite /eval_offset /= /raw_offset_merge
      eval_raw_offset_collapse eval_raw_offset_app in E2.
    change (liftM2 Z.add (eval_offset σ off) (eval_offset σ o) = Some z2) in E2.
    rewrite E1 Ho /= in E2. injection E2 as <-. lia.
  Qed.


  Lemma ptr_vaddr_o_sub_eq : forall σ p ty n1 n2 sz,
    size_of σ ty = Some sz -> (sz > 0)%N ->
    same_property ptr_vaddr (p ,, o_sub _ ty n1) (p ,, o_sub _ ty n2) ->
    n1 = n2.
  Proof.
    intros σ p ty n1 n2 sz Hsz Hpos.
    rewrite same_property_iff. intros (va & H1 & H2).
    destruct p as [|root off]; rewrite _dot.unlock /DOT_dot /= in H1 H2;
      first discriminate.
    destruct (ptr_vaddr_offset_ptr_inv σ root (__o_dot off (o_sub σ ty n1)) va H1)
      as (base1 & z1 & B1 & E1 & A1).
    destruct (ptr_vaddr_offset_ptr_inv σ root (__o_dot off (o_sub σ ty n2)) va H2)
      as (base2 & z2 & B2 & E2 & A2).
    have Hb : base2 = base1 by congruence. subst base2.
    rewrite /eval_offset /= /raw_offset_merge
      !eval_raw_offset_collapse !eval_raw_offset_app in E1 E2.
    change (liftM2 Z.add (eval_offset σ off)
      (eval_offset σ (o_sub σ ty n1)) = Some z1) in E1.

    change (liftM2 Z.add (eval_offset σ off)
      (eval_offset σ (o_sub σ ty n2)) = Some z2) in E2.
    rewrite (eval_o_sub' σ ty n1 sz Hsz) in E1.
    rewrite (eval_o_sub' σ ty n2 sz Hsz) in E2.
    destruct (eval_offset σ off) as [z|]; simpl in E1, E2; last discriminate.
    injection E1 as <-. injection E2 as <-.
    have HszZ : 0 < Z.of_N sz by lia. nia.
  Qed.

  Lemma ptr_vaddr_defined σ p :
    is_Some (@ptr_vaddr σ p) -> ptr_offset_defined p.
  Proof.
    destruct p as [|root off]; first by intros [? H].
    rewrite /ptr_vaddr /ptr_offset_defined.
    destruct (eval_raw_offset (`off)); naive_solver.
  Qed.
  Arguments mk_offset_seg _ !_ /.
  Lemma o_dot_sub σ (z1 z2 : Z) ty :
    o_sub σ ty z1 ,, o_sub σ ty z2 = o_sub σ ty (z1 + z2).
  Proof.
    UNFOLD_dot.
    intros. apply /sig_eq_pi => /=.
    rewrite /o_sub /= /mkOffset. repeat case_decide => //=.
    all: subst; try lia.
    all: rewrite ?Z.add_0_r ?Z.add_0_l.
    all: rewrite /mk_offset_seg /= /o_sub_off; case: size_of => [sz|] //=.
    all: try by rewrite decide_False //=; lia.
    all: repeat (case_decide; try (lia || by auto)).
    repeat (lia || f_equiv).
  Qed.

  Lemma o_base_derived σ p base derived :
    directly_derives σ derived base ->
    p ,, o_base σ derived base ,, o_derived σ base derived = p.
  Proof.
    rewrite -offset_ptr_dot; UNFOLD_dot.
    intros Hsome. destruct p => //=.
    f_equiv.
    case: o => o. rewrite /raw_offset_wf => Hwf.
    apply (sig_eq_pi _) => /=.
    move: Hsome => [?].
    rewrite /o_base_off /o_derived_off parent_offset.unlock.
    destruct parent_offset_tu => //= -[_] /=.
    rewrite decide_True /=; last by split_and!; [..|lia].
    rewrite /raw_offset_merge/= app_nil_r //.
  Qed.

  Lemma o_derived_base σ p base derived :
    directly_derives σ derived base ->
    p ,, o_derived σ base derived ,, o_base σ derived base = p.
  Proof.
    rewrite -offset_ptr_dot; UNFOLD_dot.
    intros Hsome. destruct p => //=.
    f_equiv.
    case: o => o. rewrite /raw_offset_wf => Hwf.
    apply (sig_eq_pi _) => /=.
    move: Hsome => [?].
    rewrite /o_base_off /o_derived_off parent_offset.unlock.
    destruct parent_offset_tu => //= -[_] /=.
    rewrite decide_True /=; last by split_and!; [..|lia].
    rewrite /raw_offset_merge/= app_nil_r //.
  Qed.

  Include PTRS_DERIVED_MIXIN.
  Include PTRS_MIXIN.
End PTRS_IMPL.
