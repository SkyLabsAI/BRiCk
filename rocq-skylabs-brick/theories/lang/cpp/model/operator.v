(*
 * Copyright (c) 2026 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(** An instance of [EVAL_BINOP_IMPURE] (lang/cpp/logic/operator.v).

    The development uses [EVAL_BINOP_IMPURE_AXIOM], which is assumed. This
    module is what makes that assumption safe: Coq checks it against the
    signature, so the rules -- including [eval_binop_impure_well_typed] --
    cannot be jointly unsatisfiable. It is deliberately *not* a C++ semantics:
    it records the operand/result shapes the rules produce, and the typing
    they claim, and nothing else, in the same spirit as [simple_pred.v].

    The model is informative rather than trivial: [Badd (Tptr ty) _ (Tptr ty)]
    relates [Vptr p] and [Vint o] only to [Vptr (p ,, _sub ty o)], so the rules
    do pin down pointer arithmetic.

    See [operand_not_well_typed] for why the rules' premises are stated with
    [has_type] rather than [valid_ptr]. *)

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
  Section shape.
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
  End shape.

  Definition eval_binop_impure `{cpp_logic} {σ}
      (_ : translation_unit) (bo : BinOp) (lhsT rhsT resT : type)
      (lhs rhs res : val) : mpred :=
    [| binop_impure_ok bo lhsT rhsT resT lhs rhs res |] ∗
    has_type lhs lhsT ∗ has_type rhs rhsT ∗ has_type res resT.

  Section axioms.
    Context `{cpp_logic} {σ}.
    Variable tu : translation_unit.

    #[local] Notation EBI := (@eval_binop_impure _ _ _ _) (only parsing).

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

    (** Each rule establishes the shape, and carries the typing over from its
        premises. *)
    #[local] Lemma intro_ok (P : mpred) bo lhsT rhsT resT lhs rhs res :
      binop_impure_ok bo lhsT rhsT resT lhs rhs res ->
      (P ⊢ has_type lhs lhsT ∗ has_type rhs rhsT ∗ has_type res resT) ->
      P ⊢ EBI tu bo lhsT rhsT resT lhs rhs res.
    Proof.
      intros Hok HT. rewrite /eval_binop_impure.
      iIntros "P". iSplitR; first by iPureIntro. by iApply HT.
    Qed.

    #[local] Lemma intro_ok_sep (P : mpred) bo lhsT rhsT resT lhs rhs res :
      binop_impure_ok bo lhsT rhsT resT lhs rhs res ->
      (P ⊢ has_type lhs lhsT ∗ has_type rhs rhsT ∗ has_type res resT) ->
      P ⊢ EBI tu bo lhsT rhsT resT lhs rhs res ∗ True.
    Proof. intros. etrans; [ exact: intro_ok | by iIntros "$" ]. Qed.

    Lemma eval_binop_impure_well_typed :
      Unfold (@eval_binop_impure_well_typed_op) (eval_binop_impure_well_typed_op EBI tu).
    Proof. intros *. rewrite /eval_binop_impure. by iIntros "(_ & $ & $ & $)". Qed.

    #[local] Lemma cmp_ok bo P :
      cmp_binop bo -> Unfold (@eval_ptr_cmp_op) (eval_ptr_cmp_op EBI tu bo P).
    Proof.
      intros Hbo ty p1 p2 res. apply intro_ok_sep.
      { left. eexists _, _, _, res. naive_solver. }
      iIntros "(_ & #$ & #$)". iApply has_type_Vbool.
    Qed.

    Lemma eval_ptr_eq :
      Unfold (@eval_ptr_cmp_op) (eval_ptr_cmp_op EBI tu Beq ptr_comparable).
    Proof. apply cmp_ok. rewrite /cmp_binop. naive_solver. Qed.

    Lemma eval_ptr_neq : forall ty p1 p2 res,
      Unfold (@eval_ptr_eq_cmp_op)
        (eval_ptr_eq_cmp_op EBI tu Beq ty p1 p2 res
      ⊢ eval_ptr_eq_cmp_op EBI tu Bneq ty p1 p2 (negb res)).
    Proof.
      intros. apply intro_ok_sep.
      { left. eexists _, _, _, (negb res). rewrite /cmp_binop. naive_solver. }
      rewrite /eval_binop_impure. iIntros "((_ & #$ & #$ & _) & _)".
      iApply has_type_Vbool.
    Qed.

    Lemma eval_ptr_le : Unfold (@eval_ptr_cmp_op)
      (eval_ptr_cmp_op EBI tu Ble (fun p1 p2 r => ptr_ord_comparable p1 p2 N.leb r)).
    Proof. apply cmp_ok. rewrite /cmp_binop. naive_solver. Qed.
    Lemma eval_ptr_lt : Unfold (@eval_ptr_cmp_op)
      (eval_ptr_cmp_op EBI tu Blt (fun p1 p2 r => ptr_ord_comparable p1 p2 N.ltb r)).
    Proof. apply cmp_ok. rewrite /cmp_binop. naive_solver. Qed.
    Lemma eval_ptr_ge : Unfold (@eval_ptr_cmp_op)
      (eval_ptr_cmp_op EBI tu Bge (fun p1 p2 r => ptr_ord_comparable p1 p2 (fun x y => y <=? x)%N r)).
    Proof. apply cmp_ok. rewrite /cmp_binop. naive_solver. Qed.
    Lemma eval_ptr_gt : Unfold (@eval_ptr_cmp_op)
      (eval_ptr_cmp_op EBI tu Bgt (fun p1 p2 r => ptr_ord_comparable p1 p2 (fun x y => y <? x)%N r)).
    Proof. apply cmp_ok. rewrite /cmp_binop. naive_solver. Qed.

    Lemma eval_ptr_int_add :
      Unfold (@eval_ptr_int_op) (eval_ptr_int_op EBI tu Badd (fun x => x)).
    Proof.
      intros w s p1 p2 o ty Hsz ->. apply intro_ok.
      { right; left. eexists _, _, _, _, _. naive_solver. }
      iIntros "(#T & #$ & #V)". iFrame "T".
      by iApply (has_type_ptr_sub p1 o ty Hsz); iFrame "T V".
    Qed.

    Lemma eval_int_ptr_add :
      Unfold (@eval_int_ptr_op) (eval_int_ptr_op EBI tu Badd (fun x => x)).
    Proof.
      intros w s p1 p2 o ty Hsz ->. apply intro_ok.
      { right; right; left. eexists _, _, _, _, _. naive_solver. }
      iIntros "(#$ & #T & #V)". iFrame "T".
      by iApply (has_type_ptr_sub p1 o ty Hsz); iFrame "T V".
    Qed.

    Lemma eval_ptr_int_sub :
      Unfold (@eval_ptr_int_op) (eval_ptr_int_op EBI tu Bsub Z.opp).
    Proof.
      intros w s p1 p2 o ty Hsz ->. apply intro_ok.
      { right; left. eexists _, _, _, _, _. naive_solver. }
      iIntros "(#T & #$ & #V)". iFrame "T".
      by iApply (has_type_ptr_sub p1 (- o) ty Hsz); iFrame "T V".
    Qed.

    Lemma eval_ptr_ptr_sub :
      Unfold (@eval_ptr_ptr_sub_op) (eval_ptr_ptr_sub_op EBI tu).
    Proof.
      intros w p1 p2 o1 o2 base ty ????. apply intro_ok.
      { right; right; right. eexists _, _, _, _, _. naive_solver. }
      iIntros "(#$ & #$)". by iApply has_type_Vint_num.
    Qed.
  End axioms.
End EVAL_BINOP_IMPURE_MODEL.

(** ** Why the premises are [has_type] and not [valid_ptr]

    Drop the typing from the premises and [eval_binop_impure_well_typed]
    becomes refutable, which is what SkyLabsAI/auto#468 demonstrated and
    SkyLabsAI/BRiCk#321 responded to by deleting it. The shape relation alone
    relates [Vint (-1)] to <<unsigned int>>, because nothing in the shape
    constrains [o] against [Tnum w s] -- nor, for the pointers, [ty] against
    their alignment. *)
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
