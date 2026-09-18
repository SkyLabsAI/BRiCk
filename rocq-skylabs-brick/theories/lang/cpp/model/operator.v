(*
 * Copyright (c) 2026 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(** An instance of [EVAL_BINOP_IMPURE] (lang/cpp/logic/operator.v).

    The development uses [EVAL_BINOP_IMPURE_AXIOM], which is assumed. This
    module is what makes that assumption safe: Coq checks it against the
    signature, so the rules cannot be jointly unsatisfiable. It is deliberately
    *not* a C++ semantics -- it records exactly the operand/result shapes the
    rules produce and nothing else, in the same spirit as [simple_pred.v].

    The model is informative rather than trivial: [Badd (Tptr ty) _ (Tptr ty)]
    relates [Vptr p] and [Vint o] only to [Vptr (p ,, _sub ty o)], so the rules
    really do pin down pointer arithmetic. What they do not pin down is typing;
    see [operand_not_well_typed] at the end. *)

Require Import skylabs.iris.extra.proofmode.proofmode.
Require Import skylabs.prelude.base.
Require Import skylabs.prelude.numbers.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.semantics.values.
Require Import skylabs.lang.cpp.semantics.operator.
Require Import skylabs.lang.cpp.logic.pred.
Require Import skylabs.lang.cpp.logic.operator.

Implicit Type (σ : genv).

#[local] Set Default Proof Using "All".

Module EVAL_BINOP_IMPURE_MODEL <: EVAL_BINOP_IMPURE.
  Section model.
    Context `{cpp_logic} {σ}.

    Definition cmp_binop (bo : BinOp) : Prop :=
      bo = Beq \/ bo = Bneq \/ bo = Ble \/ bo = Blt \/ bo = Bge \/ bo = Bgt.

    (** The intended relation, read off the rules. *)
    Definition binop_impure_ok (bo : BinOp) (lhsT rhsT resT : type)
        (lhs rhs res : val) : Prop :=
      (** [p <cmp> q]. The rules never determine the boolean:
          [ptr_comparable]/[ptr_ord_comparable] pin it down only under an
          assumption about [ptr_vaddr]. *)
      (exists ty p1 p2 (b : bool),
          cmp_binop bo /\
          lhsT = Tptr ty /\ rhsT = Tptr ty /\ resT = Tbool /\
          lhs = Vptr p1 /\ rhs = Vptr p2 /\ res = Vbool b)
      \/
      (** [p + n] and [p - n] *)
      (exists ty w s p1 (o : Z),
          lhsT = Tptr ty /\ rhsT = Tnum w s /\ resT = Tptr ty /\
          lhs = Vptr p1 /\ rhs = Vint o /\
          is_Some (size_of σ ty) /\
          (bo = Badd /\ res = Vptr (p1 ,, _sub ty o) \/
           bo = Bsub /\ res = Vptr (p1 ,, _sub ty (- o))))
      \/
      (** [n + p] *)
      (exists ty w s p1 (o : Z),
          bo = Badd /\
          lhsT = Tnum w s /\ rhsT = Tptr ty /\ resT = Tptr ty /\
          lhs = Vint o /\ rhs = Vptr p1 /\ res = Vptr (p1 ,, _sub ty o) /\
          is_Some (size_of σ ty))
      \/
      (** [p - q] *)
      (exists ty w base (o1 o2 : Z),
          bo = Bsub /\
          lhsT = Tptr ty /\ rhsT = Tptr ty /\ resT = Tnum w Signed /\
          lhs = Vptr (base ,, _sub ty o1) /\ rhs = Vptr (base ,, _sub ty o2) /\
          res = Vint (o1 - o2) /\
          is_Some (size_of σ ty) /\
          has_type_prop (Vint (o1 - o2)) (Tnum w Signed)).
  End model.

  Definition eval_binop_impure `{cpp_logic} {σ}
      (_ : translation_unit) (bo : BinOp) (lhsT rhsT resT : type)
      (lhs rhs res : val) : mpred :=
    [| binop_impure_ok bo lhsT rhsT resT lhs rhs res |].

  Section axioms.
    Context `{cpp_logic} {σ}.
    Variable tu : translation_unit.

    #[local] Notation EBI := (@eval_binop_impure _ _ _ _) (only parsing).

    (** Every rule has a pure conclusion, so its resource premises are dropped. *)
    #[local] Lemma intro_ok (P : mpred) bo lhsT rhsT resT lhs rhs res :
      binop_impure_ok bo lhsT rhsT resT lhs rhs res ->
      P ⊢ EBI tu bo lhsT rhsT resT lhs rhs res.
    Proof. intros. rewrite /eval_binop_impure. by iIntros "_". Qed.

    #[local] Lemma intro_ok_sep (P : mpred) bo lhsT rhsT resT lhs rhs res :
      binop_impure_ok bo lhsT rhsT resT lhs rhs res ->
      P ⊢ EBI tu bo lhsT rhsT resT lhs rhs res ∗ True.
    Proof.
      intros. rewrite /eval_binop_impure. iIntros "_".
      iSplitR; [ by iPureIntro | done ].
    Qed.

    Lemma eval_ptr_eq : forall ty p1 p2 res,
        ptr_comparable p1 p2 res
      ⊢ Unfold (@eval_ptr_eq_cmp_op) (eval_ptr_eq_cmp_op EBI tu Beq ty p1 p2 res).
    Proof.
      intros. apply intro_ok_sep.
      left. eexists _, _, _, _. rewrite /cmp_binop. naive_solver.
    Qed.

    Lemma eval_ptr_neq : forall ty p1 p2 res,
      Unfold (@eval_ptr_eq_cmp_op)
        (eval_ptr_eq_cmp_op EBI tu Beq ty p1 p2 res
      ⊢ eval_ptr_eq_cmp_op EBI tu Bneq ty p1 p2 (negb res)).
    Proof.
      intros. apply intro_ok_sep.
      left. eexists _, _, _, (negb res). rewrite /cmp_binop. naive_solver.
    Qed.

    #[local] Lemma ord_cmp bo f :
      cmp_binop bo -> Unfold (@eval_ptr_ord_cmp_op) (eval_ptr_ord_cmp_op EBI tu bo f).
    Proof.
      intros ? ty p1 p2 res. apply intro_ok_sep.
      left. eexists _, _, _, res. naive_solver.
    Qed.

    Lemma eval_ptr_le :
      Unfold (@eval_ptr_ord_cmp_op) (eval_ptr_ord_cmp_op EBI tu Ble N.leb).
    Proof. apply ord_cmp. rewrite /cmp_binop. naive_solver. Qed.
    Lemma eval_ptr_lt :
      Unfold (@eval_ptr_ord_cmp_op) (eval_ptr_ord_cmp_op EBI tu Blt N.ltb).
    Proof. apply ord_cmp. rewrite /cmp_binop. naive_solver. Qed.
    Lemma eval_ptr_ge :
      Unfold (@eval_ptr_ord_cmp_op) (eval_ptr_ord_cmp_op EBI tu Bge (fun x y => y <=? x)%N).
    Proof. apply ord_cmp. rewrite /cmp_binop. naive_solver. Qed.
    Lemma eval_ptr_gt :
      Unfold (@eval_ptr_ord_cmp_op) (eval_ptr_ord_cmp_op EBI tu Bgt (fun x y => y <? x)%N).
    Proof. apply ord_cmp. rewrite /cmp_binop. naive_solver. Qed.

    Lemma eval_ptr_int_add :
      Unfold (@eval_ptr_int_op) (eval_ptr_int_op EBI tu Badd (fun x => x)).
    Proof.
      intros w s p1 p2 o ty ??. apply intro_ok.
      right; left. eexists _, _, _, _, _. naive_solver.
    Qed.

    Lemma eval_int_ptr_add :
      Unfold (@eval_int_ptr_op) (eval_int_ptr_op EBI tu Badd (fun x => x)).
    Proof.
      intros w s p1 p2 o ty ??. apply intro_ok.
      right; right; left. eexists _, _, _, _, _. naive_solver.
    Qed.

    Lemma eval_ptr_int_sub :
      Unfold (@eval_ptr_int_op) (eval_ptr_int_op EBI tu Bsub Z.opp).
    Proof.
      intros w s p1 p2 o ty ??. apply intro_ok.
      right; left. eexists _, _, _, _, _. naive_solver.
    Qed.

    Lemma eval_ptr_ptr_sub :
      Unfold (@eval_ptr_ptr_sub_op) (eval_ptr_ptr_sub_op EBI tu).
    Proof.
      intros w p1 p2 o1 o2 base ty ????. apply intro_ok.
      right; right; right. eexists _, _, _, _, _. naive_solver.
    Qed.
  End axioms.
End EVAL_BINOP_IMPURE_MODEL.

(** ** What the rules do not entail

    [eval_binop_impure_well_typed] used to assert that [eval_binop_impure]
    relates each operand to a type it is a value of. The model relates
    [Vint (-1)] to <<unsigned int>>, so it refutes that assertion -- and it has
    to, since it validates [eval_ptr_int_op], which constrains neither [o]
    against [Tnum w s] nor [ty] against the pointers. A model of these rules
    therefore cannot entail well-typedness; recovering it means strengthening
    the rules, not re-adding the elimination. *)
Section not_well_typed.
  Context `{cpp_logic} {σ}.
  Import EVAL_BINOP_IMPURE_MODEL.

  #[local] Lemma minus_one_not_uint : has_type_prop (Vint (-1)) Tuint -> False.
  Proof.
    rewrite has_int_type'.
    intros [[z [Hz Hb]]|[r [Hr _]]]; last done.
    inversion Hz; subst.
    rewrite /bitsize.bound/bitsize.min_val/bitsize.max_val/= in Hb. lia.
  Qed.

  Theorem operand_not_well_typed (p : ptr) (Hsz : is_Some (size_of σ Tint)) :
    binop_impure_ok Badd (Tptr Tint) Tuint (Tptr Tint)
      (Vptr p) (Vint (-1)) (Vptr (p ,, _sub Tint (-1)))
    /\ ~ has_type_prop (Vint (-1)) Tuint.
  Proof.
    split; last exact minus_one_not_uint.
    right; left. exists Tint, int_rank.Iint, Unsigned, p, (-1)%Z. naive_solver.
  Qed.
End not_well_typed.

(** ** Alignment is preserved by pointer arithmetic

    [alignof(T)] divides [sizeof(T)] ([align_of_size_of']), so offsetting a
    [ty]-aligned pointer by whole [ty] elements preserves [ty]-alignment.
    Running off the object is ruled out by [valid_ptr] on the *result*, which
    the rules already require. So the result's [has_type] in
    [eval_ptr_int_op_wt] is not a new obligation on callers: it follows from
    the operand's alignment plus the validity they already prove.

    This belongs next to [offset_pinned_ptr_pure] in [logic/pred.v] if the
    [_wt] rules are adopted. *)
Section aligned_sub.
  Context `{cpp_logic} {σ}.

  Lemma aligned_ptr_ty_sub (p : ptr) (n : Z) ty :
    is_Some (size_of σ ty) ->
    [| aligned_ptr_ty ty p |] ∗ valid_ptr (p ,, _sub ty n)
    ⊢ [| aligned_ptr_ty ty (p ,, _sub ty n) |].
  Proof.
    intros [sz Hsz].
    destruct (align_of_size_of' _ _ Hsz) as (al & Hal & Hal0 & Hdvd).
    iIntros "[%Hp V]".
    destruct (ptr_vaddr (p ,, _sub ty n)) as [va'|] eqn:Hva'.
    2: { iPureIntro. exists al. split; first done. by right. }
    iDestruct (offset_inv_pinned_ptr_pure (_sub ty n) (Z.of_N sz * n) va' p
                 (eval_o_sub' sz Hsz) Hva' with "V") as %[Hge Hpva].
    iPureIntro. exists al. split; first done. left. exists va'. split; first done.
    (* [al] divides the base address and [Z.of_N sz * n], hence their sum. *)
    move: Hp => [al2 [Hal2 Hpal]].
    have Halq : al2 = al by congruence.
    rewrite Halq in Hpal.
    destruct Hpal as [[va [Hva Hdva]]|Hnone]; last by rewrite Hnone in Hpva.
    rewrite Hpva in Hva. injection Hva as Hva. rewrite -Hva in Hdva.
    have Hz : (Z.of_N al | Z.of_N va')%Z.
    { have -> : (Z.of_N va' = Z.of_N (Z.to_N (Z.of_N va' - Z.of_N sz * n))
                             + Z.of_N sz * n)%Z by rewrite Z2N.id//; lia.
      apply Z.divide_add_r.
      - exact: N2Z_inj_divide.
      - apply Z.divide_mul_l. exact: N2Z_inj_divide. }
    have Hpos : (0 < Z.of_N al)%Z by lia.
    have Hnn : (0 <= Z.of_N va')%Z by lia.
    move: (Z2N_inj_divide _ _ Hpos Hnn Hz). by rewrite !N2Z.id.
  Qed.

  (** Hence the [has_type] the result needs. *)
  Lemma has_type_ptr_sub (p : ptr) (n : Z) ty :
    is_Some (size_of σ ty) ->
    has_type (Vptr p) (Tptr ty) ∗ valid_ptr (p ,, _sub ty n)
    ⊢ has_type (Vptr (p ,, _sub ty n)) (Tptr ty).
  Proof.
    intros Hsz. rewrite !has_type_ptr'.
    iIntros "[[_ #A] #V]". iFrame "V".
    by iApply (aligned_ptr_ty_sub p n ty Hsz); iFrame "A V".
  Qed.
End aligned_sub.

(** ** Recovering [eval_binop_impure_well_typed]

    The elimination is sound once the rules' premises establish the typing it
    asserts: pointer operands typed at [Tptr ty] -- valid *and* [ty]-aligned,
    by [has_type_ptr'] -- rather than merely valid, and integer operands typed
    at their [Tnum]. Those are exactly the two gaps the counterexamples in
    SkyLabsAI/auto#468 exploit. [EVAL_BINOP_IMPURE_WT] is that variant of the
    interface, with the elimination put back, and [EVAL_BINOP_IMPURE_WT_MODEL]
    satisfies it: the strengthened rules are consistent *with* well-typedness,
    so it did not have to be given up.

    This is a checked proposal, not the interface the development uses. It is
    not a strengthening of [EVAL_BINOP_IMPURE]: the rules are weaker (their
    premises are stronger), so callers must supply the extra typing. In [auto]
    that costs callers nothing: [wp_eval_binop] already hands them
    [has_type a t1 ∗ has_type b t2], and [wp_eval_add_ptr_int] destructs
    exactly those and currently discards the alignment and the integer typing.
    In particular [p + n] does *not* acquire an obligation about the result:
    its premise keeps the original [valid_ptr p2], and the result's [has_type]
    is derived by [has_type_ptr_sub] above.

    Note the elimination below has no [tu ⊧ σ] premise, unlike the axiom that
    was removed: the model validates the stronger, unconditional form. *)

Section wt_skeletons.
  Context `{cpp_logic} {σ}.

  #[local] Notation EVAL :=
    (translation_unit -> BinOp -> type -> type -> type -> val -> val -> val -> mpred)
    (only parsing).

  Definition eval_binop_impure_well_typed_op (E : EVAL) tu : Prop :=
    forall bo ty1 ty2 ty3 v1 v2 v3,
      E tu bo ty1 ty2 ty3 v1 v2 v3 ⊢
      has_type v1 ty1 ∗ has_type v2 ty2 ∗ has_type v3 ty3.

  (** [P] is the comparability premise: [ptr_comparable] for [Beq], and
      [ptr_ord_comparable _ _ f] for the ordering operators. *)
  Definition eval_ptr_cmp_op_wt (E : EVAL) tu (bo : BinOp)
      (P : ptr -> ptr -> bool -> mpred) : Prop :=
    forall ty p1 p2 res,
      P p1 p2 res ∗ has_type (Vptr p1) (Tptr ty) ∗ has_type (Vptr p2) (Tptr ty) ⊢
      E tu bo (Tptr ty) (Tptr ty) Tbool (Vptr p1) (Vptr p2) (Vbool res) ∗ True.

  Definition eval_ptr_int_op_wt (E : EVAL) tu (bo : BinOp) (f : Z -> Z) : Prop :=
    forall w s p1 p2 o ty,
      is_Some (size_of σ ty) ->
      p2 = p1 ,, _sub ty (f o) ->
      has_type (Vptr p1) (Tptr ty) ∗ has_type (Vint o) (Tnum w s) ∗
      valid_ptr p2 ⊢
      E tu bo (Tptr ty) (Tnum w s) (Tptr ty) (Vptr p1) (Vint o) (Vptr p2).

  Definition eval_int_ptr_op_wt (E : EVAL) tu (bo : BinOp) (f : Z -> Z) : Prop :=
    forall w s p1 p2 o ty,
      is_Some (size_of σ ty) ->
      p2 = p1 ,, _sub ty (f o) ->
      has_type (Vint o) (Tnum w s) ∗ has_type (Vptr p1) (Tptr ty) ∗
      valid_ptr p2 ⊢
      E tu bo (Tnum w s) (Tptr ty) (Tptr ty) (Vint o) (Vptr p1) (Vptr p2).

  (** The result's typing needs no new premise: the existing no-overflow side
      condition already gives it. Only the operands' alignment is new. *)
  Definition eval_ptr_ptr_sub_op_wt (E : EVAL) tu : Prop :=
    forall w p1 p2 o1 o2 base ty,
      is_Some (size_of σ ty) ->
      p1 = base ,, _sub ty o1 ->
      p2 = base ,, _sub ty o2 ->
      has_type_prop (Vint (o1 - o2)) (Tnum w Signed) ->
      has_type (Vptr p1) (Tptr ty) ∗ has_type (Vptr p2) (Tptr ty) ⊢
      E tu Bsub (Tptr ty) (Tptr ty) (Tnum w Signed)
        (Vptr p1) (Vptr p2) (Vint (o1 - o2)).
End wt_skeletons.

Module Type EVAL_BINOP_IMPURE_WT.
  Parameter eval_binop_impure : forall `{cpp_logic} {σ},
      translation_unit -> BinOp -> forall (lhsT rhsT resT : type) (lhs rhs res : val), mpred.

  Section axioms.
    Context `{cpp_logic} {σ}.
    Variable tu : translation_unit.

    #[local] Notation EBI := (@eval_binop_impure _ _ _ _) (only parsing).

    (** The elimination removed in SkyLabsAI/BRiCk#321. *)
    Axiom eval_binop_impure_well_typed :
      Unfold (@eval_binop_impure_well_typed_op) (eval_binop_impure_well_typed_op EBI tu).

    Axiom eval_ptr_eq :
      Unfold (@eval_ptr_cmp_op_wt) (eval_ptr_cmp_op_wt EBI tu Beq ptr_comparable).

    Axiom eval_ptr_neq : forall ty p1 p2 res,
      Unfold (@eval_ptr_eq_cmp_op)
        (eval_ptr_eq_cmp_op EBI tu Beq ty p1 p2 res
      ⊢ eval_ptr_eq_cmp_op EBI tu Bneq ty p1 p2 (negb res)).

    Axiom eval_ptr_le : Unfold (@eval_ptr_cmp_op_wt)
      (eval_ptr_cmp_op_wt EBI tu Ble (fun p1 p2 r => ptr_ord_comparable p1 p2 N.leb r)).
    Axiom eval_ptr_lt : Unfold (@eval_ptr_cmp_op_wt)
      (eval_ptr_cmp_op_wt EBI tu Blt (fun p1 p2 r => ptr_ord_comparable p1 p2 N.ltb r)).
    Axiom eval_ptr_ge : Unfold (@eval_ptr_cmp_op_wt)
      (eval_ptr_cmp_op_wt EBI tu Bge (fun p1 p2 r => ptr_ord_comparable p1 p2 (fun x y => y <=? x)%N r)).
    Axiom eval_ptr_gt : Unfold (@eval_ptr_cmp_op_wt)
      (eval_ptr_cmp_op_wt EBI tu Bgt (fun p1 p2 r => ptr_ord_comparable p1 p2 (fun x y => y <? x)%N r)).

    Axiom eval_ptr_int_add :
      Unfold (@eval_ptr_int_op_wt) (eval_ptr_int_op_wt EBI tu Badd (fun x => x)).
    Axiom eval_int_ptr_add :
      Unfold (@eval_int_ptr_op_wt) (eval_int_ptr_op_wt EBI tu Badd (fun x => x)).
    Axiom eval_ptr_int_sub :
      Unfold (@eval_ptr_int_op_wt) (eval_ptr_int_op_wt EBI tu Bsub Z.opp).
    Axiom eval_ptr_ptr_sub :
      Unfold (@eval_ptr_ptr_sub_op_wt) (eval_ptr_ptr_sub_op_wt EBI tu).
  End axioms.
End EVAL_BINOP_IMPURE_WT.

Module EVAL_BINOP_IMPURE_WT_MODEL <: EVAL_BINOP_IMPURE_WT.
  Definition eval_binop_impure `{cpp_logic} {σ}
      (_ : translation_unit) (bo : BinOp) (lhsT rhsT resT : type)
      (lhs rhs res : val) : mpred :=
    [| EVAL_BINOP_IMPURE_MODEL.binop_impure_ok bo lhsT rhsT resT lhs rhs res |] ∗
    has_type lhs lhsT ∗ has_type rhs rhsT ∗ has_type res resT.

  Section axioms.
    Context `{cpp_logic} {σ}.
    Variable tu : translation_unit.

    #[local] Notation EBI := (@eval_binop_impure _ _ _ _) (only parsing).
    #[local] Notation ok := EVAL_BINOP_IMPURE_MODEL.binop_impure_ok (only parsing).
    #[local] Notation cmp_binop := EVAL_BINOP_IMPURE_MODEL.cmp_binop (only parsing).

    #[local] Lemma has_type_Vint_num z w s :
      has_type_prop (Vint z) (Tnum w s) -> ⊢@{mpredI} has_type (Vint z) (Tnum w s).
    Proof.
      intros HT. rewrite -(has_type_prop_has_type_noptr (Vint z) (Tnum w s))//.
      by iPureIntro.
    Qed.

    #[local] Lemma has_type_Vbool (b : bool) : ⊢@{mpredI} has_type (Vbool b) Tbool.
    Proof.
      rewrite -(has_type_prop_has_type_noptr (Vbool b) Tbool)//.
      iPureIntro. apply has_type_prop_bool. by eexists.
    Qed.

    #[local] Lemma intro_wt (P : mpred) bo lhsT rhsT resT lhs rhs res :
      ok bo lhsT rhsT resT lhs rhs res ->
      (P ⊢ has_type lhs lhsT ∗ has_type rhs rhsT ∗ has_type res resT) ->
      P ⊢ EBI tu bo lhsT rhsT resT lhs rhs res.
    Proof.
      intros Hok HT. rewrite /eval_binop_impure.
      iIntros "P". iSplitR; first by iPureIntro. by iApply HT.
    Qed.

    #[local] Lemma intro_wt_sep (P : mpred) bo lhsT rhsT resT lhs rhs res :
      ok bo lhsT rhsT resT lhs rhs res ->
      (P ⊢ has_type lhs lhsT ∗ has_type rhs rhsT ∗ has_type res resT) ->
      P ⊢ EBI tu bo lhsT rhsT resT lhs rhs res ∗ True.
    Proof. intros. etrans; [ exact: intro_wt | by iIntros "$" ]. Qed.

    Lemma eval_binop_impure_well_typed :
      Unfold (@eval_binop_impure_well_typed_op) (eval_binop_impure_well_typed_op EBI tu).
    Proof. intros *. rewrite /eval_binop_impure. by iIntros "(_ & $ & $ & $)". Qed.

    #[local] Lemma cmp_wt bo P :
      cmp_binop bo -> Unfold (@eval_ptr_cmp_op_wt) (eval_ptr_cmp_op_wt EBI tu bo P).
    Proof.
      intros Hbo ty p1 p2 res. apply intro_wt_sep.
      { left. eexists _, _, _, res. naive_solver. }
      iIntros "(_ & #$ & #$)". iApply has_type_Vbool.
    Qed.

    Lemma eval_ptr_eq :
      Unfold (@eval_ptr_cmp_op_wt) (eval_ptr_cmp_op_wt EBI tu Beq ptr_comparable).
    Proof. apply cmp_wt. rewrite /cmp_binop. naive_solver. Qed.

    Lemma eval_ptr_neq : forall ty p1 p2 res,
      Unfold (@eval_ptr_eq_cmp_op)
        (eval_ptr_eq_cmp_op EBI tu Beq ty p1 p2 res
      ⊢ eval_ptr_eq_cmp_op EBI tu Bneq ty p1 p2 (negb res)).
    Proof.
      intros. apply intro_wt_sep.
      { left. eexists _, _, _, (negb res). rewrite /cmp_binop. naive_solver. }
      rewrite /eval_binop_impure. iIntros "((_ & #$ & #$ & _) & _)".
      iApply has_type_Vbool.
    Qed.

    Lemma eval_ptr_le : Unfold (@eval_ptr_cmp_op_wt)
      (eval_ptr_cmp_op_wt EBI tu Ble (fun p1 p2 r => ptr_ord_comparable p1 p2 N.leb r)).
    Proof. apply cmp_wt. rewrite /cmp_binop. naive_solver. Qed.
    Lemma eval_ptr_lt : Unfold (@eval_ptr_cmp_op_wt)
      (eval_ptr_cmp_op_wt EBI tu Blt (fun p1 p2 r => ptr_ord_comparable p1 p2 N.ltb r)).
    Proof. apply cmp_wt. rewrite /cmp_binop. naive_solver. Qed.
    Lemma eval_ptr_ge : Unfold (@eval_ptr_cmp_op_wt)
      (eval_ptr_cmp_op_wt EBI tu Bge (fun p1 p2 r => ptr_ord_comparable p1 p2 (fun x y => y <=? x)%N r)).
    Proof. apply cmp_wt. rewrite /cmp_binop. naive_solver. Qed.
    Lemma eval_ptr_gt : Unfold (@eval_ptr_cmp_op_wt)
      (eval_ptr_cmp_op_wt EBI tu Bgt (fun p1 p2 r => ptr_ord_comparable p1 p2 (fun x y => y <? x)%N r)).
    Proof. apply cmp_wt. rewrite /cmp_binop. naive_solver. Qed.

    Lemma eval_ptr_int_add :
      Unfold (@eval_ptr_int_op_wt) (eval_ptr_int_op_wt EBI tu Badd (fun x => x)).
    Proof.
      intros w s p1 p2 o ty Hsz ->. apply intro_wt.
      { right; left. eexists _, _, _, _, _. naive_solver. }
      iIntros "(#T & #$ & #V)". iFrame "T".
      by iApply (has_type_ptr_sub p1 o ty Hsz); iFrame "T V".
    Qed.

    Lemma eval_int_ptr_add :
      Unfold (@eval_int_ptr_op_wt) (eval_int_ptr_op_wt EBI tu Badd (fun x => x)).
    Proof.
      intros w s p1 p2 o ty Hsz ->. apply intro_wt.
      { right; right; left. eexists _, _, _, _, _. naive_solver. }
      iIntros "(#$ & #T & #V)". iFrame "T".
      by iApply (has_type_ptr_sub p1 o ty Hsz); iFrame "T V".
    Qed.

    Lemma eval_ptr_int_sub :
      Unfold (@eval_ptr_int_op_wt) (eval_ptr_int_op_wt EBI tu Bsub Z.opp).
    Proof.
      intros w s p1 p2 o ty Hsz ->. apply intro_wt.
      { right; left. eexists _, _, _, _, _. naive_solver. }
      iIntros "(#T & #$ & #V)". iFrame "T".
      by iApply (has_type_ptr_sub p1 (- o) ty Hsz); iFrame "T V".
    Qed.

    Lemma eval_ptr_ptr_sub :
      Unfold (@eval_ptr_ptr_sub_op_wt) (eval_ptr_ptr_sub_op_wt EBI tu).
    Proof.
      intros w p1 p2 o1 o2 base ty ????. apply intro_wt.
      { right; right; right. eexists _, _, _, _, _. naive_solver. }
      iIntros "(#$ & #$)". by iApply has_type_Vint_num.
    Qed.
  End axioms.
End EVAL_BINOP_IMPURE_WT_MODEL.

