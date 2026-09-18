(*
 * Copyright (c) 2020 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.iris.extra.proofmode.proofmode.
Require Import skylabs.prelude.base.
Require Import skylabs.prelude.option.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.semantics.values.
Require Import skylabs.lang.cpp.semantics.operator.
Require Import skylabs.lang.cpp.logic.pred.

Implicit Type (σ : genv).

(** [binop_needs_memory lhsT rhsT] is [true] exactly on the operand types at
    which [eval_binop_impure] has an introduction rule, i.e. those where
    evaluating the operator has to consult the abstract machine state.

    Every rule for [eval_binop_impure] -- [eval_ptr_eq], [eval_ptr_neq],
    [eval_ptr_{le,lt,ge,gt}], [eval_ptr_int_add], [eval_int_ptr_add],
    [eval_ptr_int_sub] and [eval_ptr_ptr_sub] -- has an *object pointer*
    ([Tptr]) on at least one side, and no rule for [eval_binop_pure] does.
    Note that [Tnullptr] is deliberately *not* included: [eval_eq_nullptr] and
    [eval_neq_nullptr] are pure. This is why we test [unptr] rather than
    [is_pointer].

    NOTE: this predicate is what makes [eval_binop] a case split rather than a
          disjunction, so it must be kept in sync with the introduction rules
          for [eval_binop_impure] below. All of them live in this file.
 *)
Definition binop_needs_memory (lhsT rhsT : type) : bool :=
  isSome (unptr lhsT) || isSome (unptr rhsT).

(** Discharging [binop_needs_memory _ _ = false]. On concrete types this is
    [reflexivity]; the lemmas below cover the type variables that arise in
    generic rules. *)
Lemma binop_needs_memory_unptr lhsT rhsT :
  unptr lhsT = None -> unptr rhsT = None -> binop_needs_memory lhsT rhsT = false.
Proof. by rewrite /binop_needs_memory => -> ->. Qed.

Lemma unptr_supports_arith ty : supports_arith ty -> unptr ty = None.
Proof.
  rewrite /unptr; destruct 1 as [Hty]; move: Hty; rewrite /arith_as.
  by destruct (drop_qualifiers ty).
Qed.

Lemma unptr_supports_rel ty : supports_rel ty -> unptr ty = None.
Proof.
  rewrite /unptr; destruct 1 as [[Hty|Hty]]; last by destruct (drop_qualifiers ty).
  by rewrite -/(unptr ty) (unptr_supports_arith _ Hty).
Qed.

Lemma binop_needs_memory_supports_rel lhsT rhsT :
  supports_rel lhsT -> supports_rel rhsT -> binop_needs_memory lhsT rhsT = false.
Proof. eauto using binop_needs_memory_unptr, unptr_supports_rel. Qed.

Lemma binop_needs_memory_supports_arith lhsT rhsT :
  supports_arith lhsT -> supports_arith rhsT -> binop_needs_memory lhsT rhsT = false.
Proof. eauto using binop_needs_memory_unptr, unptr_supports_arith. Qed.

(** Pointer [p'] is not at the beginning of a block. *)
Definition non_beginning_ptr `{cpp_logic} {σ} p' : mpred :=
  ∃ p o, [| p' = p ,, o /\
    (* ensure that o is > 0 *)
    some_Forall2 N.lt (ptr_vaddr p) (ptr_vaddr p') |] ∧ valid_ptr p.
#[global] Hint Opaque non_beginning_ptr : sl_opacity.

Section non_beginning_ptr.
  Context `{cpp_logic} {σ}.

  #[global] Instance non_beginning_ptr_persistent p : Persistent (non_beginning_ptr p) := _.
  #[global] Instance non_beginning_ptr_affine p : Affine (non_beginning_ptr p) := _.
  #[global] Instance non_beginning_ptr_timeless p : Timeless (non_beginning_ptr p) := _.
End non_beginning_ptr.

#[global] Typeclasses Opaque non_beginning_ptr.

Section comparable.
  Context `{cpp_logic} {σ}.

  (** * Pointer comparison operators *)
  (** For [Ble, Blt, Bge, Bgt] axioms on pointers. *)
  Definition ptr_ord_comparable p1 p2 (f : vaddr -> vaddr -> bool) res : mpred :=
    [| same_alloc p1 p2 |] ∗
    [| forall va1 va2, ptr_vaddr p1 = Some va1 -> ptr_vaddr p2 = Some va2 -> f va1 va2 = res |] ∗
    valid_ptr p1 ∗ valid_ptr p2.

  (* Two pointers into the same object are [ptr_ord_comparable]. *)
  Lemma ptr_ord_comparable_off_off o1 o2 base p1 p2 f res :
    p1 = base ,, o1 ->
    p2 = base ,, o2 ->
    (forall va1 va2, ptr_vaddr p1 = Some va1 -> ptr_vaddr p2 = Some va2 -> f va1 va2 = res) ->
    valid_ptr p1 ∗ valid_ptr p2 ⊢ ptr_ord_comparable p1 p2 f res.
  Proof.
    intros -> -> Hres.
    iIntros "#[V1 V2]". iFrame (Hres) "V1 V2" => {Hres}; rewrite !valid_ptr_alloc_id.
    iRevert "V1 V2"; iIntros "!%".
    exact: same_alloc_offset_2.
  Qed.

  Lemma ptr_ord_comparable_off o1 base p1 f res :
    p1 = base ,, o1 ->
    (forall va1 va2, ptr_vaddr p1 = Some va1 -> ptr_vaddr base = Some va2 -> f va1 va2 = res) ->
    valid_ptr p1 ∗ valid_ptr base ⊢ ptr_ord_comparable p1 base f res.
  Proof.
    intros -> Hres. eapply (ptr_ord_comparable_off_off o1 o_id base) => //.
    by rewrite offset_ptr_id.
  Qed.

  (** Skeleton for [Beq] and [Bneq] axioms on pointers.

   This specification follows the C++ standard
   (https://eel.is/c++draft/expr.eq#3), and is inspired by Cerberus's pointer
   provenance semantics for C, and Krebbers's thesis. We forbid cases where
   comparisons have undefined or unspecified behavior.
   As a deviation, we assume compilers do not perform lifetime-end pointer
   zapping (see http://www.open-std.org/jtc1/sc22/wg14/www/docs/n2443.pdf).

   (1) We always require both pointers to be valid.
   (2) Crucially, in all these semantics comparing pointers with distinct
       provenances (allocation ID) but the same address has non-deterministic
       results, so we forbid it. Hence, we must prevent ambiguous results.
       (a) Comparing two pointers with the same allocation ID is never
           ambiguous.
       (b) We assume non-null pointers can be reliably distinguished from
           [nullptr], because we don't support pointer zapping (unlike
           Krebbers and the standard).
       (c) Otherwise, we require that both pointers are jointly live, and
           prevent remaining potential confusion via [ptr_unambiguous_cmp].

   - Joint liveness is required in clause (c) because a dangling pointer and
     a non-null live pointer have different provenances but can have the same
     address, because the allocator could have reused the address of the
     dangling pointer.
   - Via [ptr_unambiguous_cmp], we forbid comparing a one-past-the-end
     pointer to an object with a pointer to the "beginning" of a different
     object, because that gives unspecified results [1], so we choose not to
     support this case. We use [non_beginning_ptr] to ensure a pointer is not
     to the beginning of a complete object.

   [1] From https://eel.is/c++draft/expr.eq#3.1:
   > If one pointer represents the address of a complete object, and another
     pointer represents the address one past the last element of a different
     complete object, the result of the comparison is unspecified.
   *)
  #[local] Definition ptr_unambiguous_cmp vt1 p2 : mpred :=
    [| vt1 = Strict |] ∨ non_beginning_ptr p2.

  (** Can these pointers be validly compared? *)
  (* Written to ease showing [ptr_comparable_symm]. *)
  Definition ptr_comparable_def p1 p2 res : mpred :=
    (* These premises let you assume that that [p1] and [p2] have an address. *)
    [| is_Some (ptr_vaddr p1) /\ is_Some (ptr_vaddr p2) |] -∗
    ∃ vt1 vt2,
      [| same_address_bool p1 p2 = res |] ∗
      (_valid_ptr vt1 p1 ∗ _valid_ptr vt2 p2) ∗
      ([| same_alloc p1 p2 |] ∨
        ([| p1 = nullptr |] ∨ [| p2 = nullptr |]) ∨
        ((live_ptr p1 ∧ live_ptr p2) ∗
          ptr_unambiguous_cmp vt1 p2 ∗ ptr_unambiguous_cmp vt2 p1)).
  Definition ptr_comparable_aux : seal ptr_comparable_def. Proof. by eexists. Qed.
  Definition ptr_comparable := ptr_comparable_aux.(unseal).
  Definition ptr_comparable_eq : ptr_comparable = _ := ptr_comparable_aux.(seal_eq).

  Lemma ptr_ord_comparable_comparable p1 p2 res :
    ptr_ord_comparable p1 p2 (λ va1 va2, bool_decide (va1 = va2)) res ⊢ ptr_comparable p1 p2 res.
  Proof.
    rewrite ptr_comparable_eq /ptr_comparable_def.
    iIntros "($ & %Hi & ? & ?)" ([[va1 Hs1] [va2 Hs2]]);
      iExists Relaxed, Relaxed; iFrame.
    by rewrite -(Hi _ _ Hs1 Hs2) (same_address_bool_eq Hs1 Hs2).
  Qed.

  Lemma ptr_comparable_symm p1 p2 res :
    ptr_comparable p1 p2 res ⊢ ptr_comparable p2 p1 res.
  Proof.
    rewrite ptr_comparable_eq /ptr_comparable_def.
    rewrite (comm and (is_Some (ptr_vaddr p2))); f_equiv.
    iDestruct 1 as (vt1 vt2) "H"; iExists vt2, vt1.
    (* To ease rearranging conjuncts or changing connectives, we repeat the
    body (which is easy to update), not the nesting structure. *)
    rewrite !(comm and (is_Some (ptr_vaddr p2)), comm same_address_bool p2, comm _ (_valid_ptr vt2 _),
      symmetry_iff same_alloc p2, comm _ [| p2 = _ |]%I, comm _ (live_ptr p2), comm _ (ptr_unambiguous_cmp vt2 _)).
    iStopProof. repeat f_equiv.
  Qed.

  Lemma nullptr_ptr_comparable {p res} :
    (is_Some (ptr_vaddr p) -> bool_decide (p = nullptr) = res) ->
    valid_ptr p ⊢ ptr_comparable p nullptr res.
  Proof.
    rewrite ptr_comparable_eq /ptr_comparable_def.
    iIntros "%HresI V" ([Haddr _]); iExists Relaxed, Relaxed.
    iDestruct (same_address_bool_null with "V") as %->.
    iFrame ((HresI Haddr) (eq_refl nullptr)) "V".
    iApply valid_ptr_nullptr.
  Qed.

  Lemma self_ptr_comparable p :
    valid_ptr p ⊢ ptr_comparable p p true.
  Proof.
    rewrite -ptr_ord_comparable_comparable /ptr_ord_comparable; iIntros "#V".
    iDestruct (same_alloc_refl with "V") as "$"; iFrame "V"; iIntros "!%".
    intros; simplify_eq. exact: bool_decide_true.
  Qed.

  Lemma ptr_comparable_off_off o1 o2 base p1 p2 res :
    p1 = base ,, o1 ->
    p2 = base ,, o2 ->
    same_address_bool p1 p2 = res ->
    valid_ptr p1 ∗ valid_ptr p2 ⊢ ptr_comparable p1 p2 res.
  Proof.
    intros ->-> Hs. rewrite -ptr_ord_comparable_comparable.
    apply: ptr_ord_comparable_off_off; [done..|].
    move=> va1 va2 Hs1 Hs2. by rewrite -(same_address_bool_eq Hs1 Hs2).
  Qed.

  Lemma ptr_comparable_off o1 base p1 res :
    p1 = base ,, o1 ->
    same_address_bool p1 base = res ->
    valid_ptr p1 ∗ valid_ptr base ⊢ ptr_comparable p1 base res.
  Proof.
    intros -> Hres. eapply (ptr_comparable_off_off o1 o_id base) => //.
    by rewrite offset_ptr_id.
  Qed.
End comparable.

(** ** Skeletons for the rules of the impure fragment

    These are parameterized by the evaluation relation so that the interface
    [EVAL_BINOP_IMPURE] below and its instance in [lang/cpp/model/operator.v]
    state the same rules rather than two hand-kept-in-sync copies. *)
Section skeletons.
  Context `{cpp_logic} {σ}.

  #[local] Notation EVAL :=
    (translation_unit -> BinOp -> type -> type -> type -> val -> val -> val -> mpred)
    (only parsing).

  (** Skeleton for [Beq] and [Bneq] axioms on pointers. *)
  Definition eval_ptr_eq_cmp_op (E : EVAL) tu (bo : BinOp) ty p1 p2 res : mpred :=
    E tu bo
      (Tptr ty) (Tptr ty) Tbool
      (Vptr p1) (Vptr p2) (Vbool res) ∗ True.

  (** Skeleton for [Ble, Blt, Bge, Bgt] axioms on pointers. *)
  Definition eval_ptr_ord_cmp_op (E : EVAL) tu (bo : BinOp) (f : vaddr -> vaddr -> bool) : Prop :=
    forall ty p1 p2 res,
      ptr_ord_comparable p1 p2 f res ⊢
      E tu bo
        (Tptr ty) (Tptr ty) Tbool
        (Vptr p1) (Vptr p2) (Vbool res) ∗ True.

  (** For non-comparison operations, we do not require liveness, unlike Krebbers.
  We require validity of the result to prevent over/underflow.
  (This is because we don't do pointer zapping, following Cerberus).
  Supporting pointer zapping would require adding [live_ptr] preconditions to
  these operators.
  https://eel.is/c++draft/basic.compound#3.1 *)

  (** Skeletons for ptr/int operators. *)

  Definition eval_ptr_int_op (E : EVAL) tu (bo : BinOp) (f : Z -> Z) : Prop :=
    forall w s p1 p2 o ty,
      is_Some (size_of σ ty) ->
      p2 = p1 ,, _sub (erase_qualifiers ty) (f o) ->
      valid_ptr p1 ∧ valid_ptr p2 ⊢
      E tu bo
                (Tptr ty) (Tnum w s) (Tptr ty)
                (Vptr p1)     (Vint o)   (Vptr p2).

  Definition eval_int_ptr_op (E : EVAL) tu (bo : BinOp) (f : Z -> Z) : Prop :=
    forall w s p1 p2 o ty,
      is_Some (size_of σ ty) ->
      p2 = p1 ,, _sub (erase_qualifiers ty) (f o) ->
      valid_ptr p1 ∧ valid_ptr p2 ⊢
      E tu bo
                (Tnum w s) (Tptr ty) (Tptr ty)
                (Vint o)   (Vptr p1)     (Vptr p2).

  (** Skeleton for the ptr/ptr subtraction axiom. *)
  Definition eval_ptr_ptr_sub_op (E : EVAL) tu : Prop :=
    forall w p1 p2 o1 o2 base ty,
      is_Some (size_of σ ty) ->
      p1 = base ,, _sub ty o1 ->
      p2 = base ,, _sub ty o2 ->
      (* Side condition to prevent overflow; needed per https://eel.is/c++draft/expr.add#note-1 *)
      has_type_prop (Vint (o1 - o2)) (Tnum w Signed) ->
      valid_ptr p1 ∧ valid_ptr p2 ⊢
      E tu Bsub
                (Tptr ty) (Tptr ty) (Tnum w Signed)
                (Vptr p1)     (Vptr p2)     (Vint (o1 - o2)).
End skeletons.

(** * The impure fragment of binary-operator evaluation

    [eval_binop_impure] is the part of the semantics that has to consult the
    abstract machine state. Its rules are gathered into a module type so that
    they form a closed, named interface: [lang/cpp/model/operator.v] provides
    an instance, and it is that instance -- checked by Coq against this
    signature -- which establishes that the rules are jointly satisfiable.

    That check is not decoration. [eval_binop_impure_well_typed] used to sit
    alongside these rules, asserting that [eval_binop_impure] relates operands
    to types they are values of, and it was refutable from them
    (SkyLabsAI/auto#468): nothing here constrains the integer operand of
    [eval_ptr_int_op] against its [Tnum], nor [ty] against the pointers. Any
    rule added below must be provable of the model, or the model must be
    extended along with it.

    NOTE: every rule here has an *object pointer* ([Tptr]) on at least one
          side. [binop_needs_memory] above relies on that; a rule that broke
          it would make [eval_binop] silently drop this fragment. *)
Module Type EVAL_BINOP_IMPURE.
  Parameter eval_binop_impure : forall `{cpp_logic} {σ},
      translation_unit -> BinOp -> forall (lhsT rhsT resT : type) (lhs rhs res : val), mpred.

  Section axioms.
    Context `{cpp_logic} {σ}.
    Variable tu : translation_unit.

    #[local] Notation EBI := (@eval_binop_impure _ _ _ _) (only parsing).

    Axiom eval_ptr_eq : forall ty p1 p2 res,
        ptr_comparable p1 p2 res
      ⊢ Unfold (@eval_ptr_eq_cmp_op) (eval_ptr_eq_cmp_op EBI tu Beq ty p1 p2 res).

    Axiom eval_ptr_neq : forall ty p1 p2 res,
      Unfold (@eval_ptr_eq_cmp_op)
        (eval_ptr_eq_cmp_op EBI tu Beq ty p1 p2 res
      ⊢ eval_ptr_eq_cmp_op EBI tu Bneq ty p1 p2 (negb res)).

    Axiom eval_ptr_le :
      Unfold (@eval_ptr_ord_cmp_op) (eval_ptr_ord_cmp_op EBI tu Ble N.leb).
    Axiom eval_ptr_lt :
      Unfold (@eval_ptr_ord_cmp_op) (eval_ptr_ord_cmp_op EBI tu Blt N.ltb).
    Axiom eval_ptr_ge :
      Unfold (@eval_ptr_ord_cmp_op) (eval_ptr_ord_cmp_op EBI tu Bge (fun x y => y <=? x)%N).
    Axiom eval_ptr_gt :
      Unfold (@eval_ptr_ord_cmp_op) (eval_ptr_ord_cmp_op EBI tu Bgt (fun x y => y <? x)%N).


  (**
  lhs + rhs (https://eel.is/c++draft/expr.add#1): one of rhs or lhs is a
  pointer to a completely-defined object type
  (https://eel.is/c++draft/basic.types#general-5), the other has integral or
  unscoped enumeration type. In this case, the result type has the type of
  the pointer.

  Liveness note: when adding int [i] to pointer [p], the standard demands
  that [p] points to an array (https://eel.is/c++draft/expr.add#4.2),
  With https://eel.is/c++draft/basic.compound#3.1 and
  https://eel.is/c++draft/basic.memobj#basic.stc.general-4, that implies that
  [p] has not been deallocated.
   *)
    Axiom eval_ptr_int_add :
      Unfold (@eval_ptr_int_op) (eval_ptr_int_op EBI tu Badd (fun x => x)).

    Axiom eval_int_ptr_add :
      Unfold (@eval_int_ptr_op) (eval_int_ptr_op EBI tu Badd (fun x => x)).

  (**
  lhs - rhs (https://eel.is/c++draft/expr.add#2.3): lhs is a pointer to
  completely-defined object type
  (https://eel.is/c++draft/basic.types#general-5), rhs has integral or
  unscoped enumeration type. In this case, the result type has the type of
  the pointer.
  Liveness note: as above (https://eel.is/c++draft/expr.add#4).
  *)
    Axiom eval_ptr_int_sub :
      Unfold (@eval_ptr_int_op) (eval_ptr_int_op EBI tu Bsub Z.opp).

  (**
  lhs - rhs (https://eel.is/c++draft/expr.add#2.2): both lhs and rhs must be
  pointers to the same completely-defined object types
  (https://eel.is/c++draft/basic.types#general-5).
  Liveness note: as above (https://eel.is/c++draft/expr.add#5.2).
  *)
    Axiom eval_ptr_ptr_sub :
      Unfold (@eval_ptr_ptr_sub_op) (eval_ptr_ptr_sub_op EBI tu).
  End axioms.
End EVAL_BINOP_IMPURE.

Declare Module Export EVAL_BINOP_IMPURE_AXIOM : EVAL_BINOP_IMPURE.

Section derived.
  Context `{cpp_logic} {σ}.
  Variable tu : translation_unit.

  #[local] Notation EBI := (@eval_binop_impure _ _ _ _) (only parsing).

  Lemma eval_ptr_nullptr_eq_l {ty vp res} :
    (is_Some (ptr_vaddr vp) -> bool_decide (vp = nullptr) = res) ->
    valid_ptr vp ⊢ Unfold (@eval_ptr_eq_cmp_op) (eval_ptr_eq_cmp_op EBI tu Beq ty vp nullptr res).
  Proof. intros ->%nullptr_ptr_comparable. by rewrite -eval_ptr_eq. Qed.

  Lemma eval_ptr_nullptr_eq_r {ty vp res} :
    (is_Some (ptr_vaddr vp) -> bool_decide (vp = nullptr) = res) ->
    valid_ptr vp ⊢ Unfold (@eval_ptr_eq_cmp_op) (eval_ptr_eq_cmp_op EBI tu Beq ty nullptr vp res).
  Proof. intros ->%nullptr_ptr_comparable. by rewrite ptr_comparable_symm -eval_ptr_eq. Qed.

  Lemma eval_ptr_self_eq ty p :
    valid_ptr p ⊢ Unfold (@eval_ptr_eq_cmp_op) (eval_ptr_eq_cmp_op EBI tu Beq ty p p true).
  Proof. by rewrite -eval_ptr_eq -self_ptr_comparable. Qed.
End derived.

Section with_Σ.
  Context `{cpp_logic} {σ}.


  (** [eval_binop] is the semantics of a binary operator in the logic. It
      discriminates on the operand types: the operators that need the abstract
      machine state are exactly the ones on object pointers (see
      [binop_needs_memory]), everything else is pure. *)
  Definition eval_binop tu (b : BinOp) (lhsT rhsT resT : type) (lhs rhs res : val) : mpred :=
    if binop_needs_memory lhsT rhsT
    then eval_binop_impure tu b lhsT rhsT resT lhs rhs res
    else [| eval_binop_pure tu b lhsT rhsT resT lhs rhs res |].

  Lemma eval_binop_pure_eq tu b lhsT rhsT resT lhs rhs res :
    binop_needs_memory lhsT rhsT = false ->
    eval_binop tu b lhsT rhsT resT lhs rhs res
      -|- [| eval_binop_pure tu b lhsT rhsT resT lhs rhs res |].
  Proof. by rewrite /eval_binop => ->. Qed.

  Lemma eval_binop_impure_eq tu b lhsT rhsT resT lhs rhs res :
    binop_needs_memory lhsT rhsT = true ->
    eval_binop tu b lhsT rhsT resT lhs rhs res
      -|- eval_binop_impure tu b lhsT rhsT resT lhs rhs res.
  Proof. by rewrite /eval_binop => ->. Qed.

  (** At the operand types where [eval_binop] is pure, well-typedness comes from
      [eval_binop_pure_well_typed]. *)
  Theorem eval_binop_well_typed tu bo ty1 ty2 ty3 v1 v2 v3 :
    tu ⊧ σ ->
    binop_needs_memory ty1 ty2 = false ->
    eval_binop tu bo ty1 ty2 ty3 v1 v2 v3
    |-- [| has_type_prop v1 ty1 /\ has_type_prop v2 ty2 /\ has_type_prop v3 ty3 |].
  Proof.
    intros ? Hpure; rewrite eval_binop_pure_eq//.
    iIntros "!%". exact: eval_binop_pure_well_typed.
  Qed.
End with_Σ.
