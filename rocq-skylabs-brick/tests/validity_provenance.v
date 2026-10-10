Require Import iris.bi.monpred.
Require Import iris.base_logic.lib.iprop.
Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.notations.
Require Import skylabs.lang.cpp.code_notations.
Require Import skylabs.lang.cpp.semantics.genv.
Require Import skylabs.lang.cpp.semantics.types.
Require Import skylabs.lang.cpp.model.inductive_pointers.
Require Import skylabs.lang.cpp.model.simple_pred.
Require Import skylabs.iris.extra.proofmode.proofmode.
Import PTRS_IMPL VALUES_DEFS_IMPL SimpleCPP.
Set Default Proof Using "Type*".

Section concrete_model.
  Context {thread_info : biIndex} {Σ : gFunctors}
    {Hlogic : SimpleCPP.cpp_logic thread_info Σ}.
  #[local] Existing Instance Hlogic.
  Context {σ : genv}.

  (** Validity still follows from a real allocation's block resource. *)
  Lemma allocated_base_valid aid va :
    aid <> null_alloc_id -> va <> 0%N ->
    blocks_own (alloc_ptr aid va) 0 1 ⊢
    _valid_ptr pred.Strict (alloc_ptr aid va).
  Proof.
    intros Haid Haddr. rewrite /_valid_ptr. iIntros "B". iRight.
    iExists 0%Z, 1%Z. iFrame "B".
    iSplit; first (iPureIntro; exists aid; split; done).
    iPureIntro. apply (raw_path_valid_nil _ _ _ _ va); try done. left; lia.
  Qed.

  Lemma allocated_one_past_valid aid :
    aid <> null_alloc_id ->
    blocks_own (alloc_ptr aid 8) 0 1 ⊢
    _valid_ptr pred.Relaxed (alloc_ptr aid 8 ,, o_sub σ "unsigned char"%cpp_type 1).
  Proof.
    intros Haid. rewrite /_valid_ptr _dot.unlock /DOT_dot /=.
    iIntros "B". iRight. iExists 0%Z, 1%Z. iFrame "B".
    iSplit; first (iPureIntro; exists aid; split; done).
    iPureIntro.
    change (raw_path_valid pred.Relaxed (alloc_ptr_ aid 8) 0 1
      ([] ++ [(o_sub_ "unsigned char"%cpp_type 1, 1%Z)])).
    apply (raw_path_valid_snoc _ _ _ _ _ _ 1%Z 9%N); try done.
    - apply (raw_path_valid_nil _ _ _ _ 8%N); try done. left; lia.
    - right; done.
  Qed.

  (** The distinguished null pointer retains relaxed validity. *)
  Lemma null_relaxed_valid : ⊢ _valid_ptr pred.Relaxed nullptr.
  Proof. apply valid_ptr_nullptr. Qed.

  Lemma null_zero_subscript_valid ty :
    is_Some (size_of σ ty) ->
    ⊢ _valid_ptr pred.Relaxed (nullptr ,, o_sub σ ty 0).
  Proof. intros Hsz. rewrite o_sub_0 // offset_ptr_id. apply valid_ptr_nullptr. Qed.

  Lemma null_offset_never_strict o :
    _valid_ptr pred.Strict (nullptr ,, o) ⊢ False.
  Proof.
    iIntros "H". iDestruct (strict_valid_ptr_off_nonnull with "H") as %H.
    contradiction.
  Qed.

  Lemma typed_null_offset_impossible ty o :
    type_ptr ty (nullptr ,, o) ⊢ False.
  Proof.
    iIntros "H". iDestruct (type_ptr_off_nonnull with "H") as %H.
    contradiction.
  Qed.

  Lemma null_zero_subscript_unsized ty :
    size_of σ ty = None ->
    _valid_ptr pred.Relaxed (nullptr ,, o_sub σ ty 0) ⊢ False.
  Proof.
    intros Hsz.
    have Heq : o_sub σ ty 0 = o_sub σ ty 1.
    { apply (sig_eq_pi _).
      rewrite /o_sub /= size_of_erase_qualifiers Hsz.
      rewrite /mkOffset /mk_offset_seg /= /simple_pointers_utils.o_sub_off.
      by rewrite size_of_erase_qualifiers Hsz. }
    rewrite Heq. apply VALID_PTR._valid_ptr_nullptr_sub_false. lia.
  Qed.

  (** Defined zero-sized layouts remain distinct from missing layouts. *)
  Lemma allocated_zero_sized_subscript_valid aid :
    aid <> null_alloc_id ->
    blocks_own (alloc_ptr aid 8) 0 1 ⊢
    _valid_ptr pred.Strict
      (alloc_ptr aid 8 ,, o_sub σ "unsigned char[0]"%cpp_type 1).
  Proof.
    intros Haid. rewrite /_valid_ptr _dot.unlock /DOT_dot /=.
    iIntros "B". iRight. iExists 0%Z, 1%Z. iFrame "B".
    iSplit; first (iPureIntro; exists aid; split; done).
    iPureIntro.
    change (raw_path_valid pred.Strict (alloc_ptr_ aid 8) 0 1
      ([] ++ [(o_sub_ "unsigned char[0]"%cpp_type 1, 0%Z)])).
    apply (raw_path_valid_snoc _ _ _ _ _ _ 0%Z 8%N); try done.
    - apply (raw_path_valid_nil _ _ _ _ 8%N); try done. left; lia.
    - left; lia.
  Qed.

  Lemma missing_layout_subscript_invalid vt p ty i :
    size_of σ ty = None ->
    _valid_ptr vt (p ,, o_sub σ ty i) ⊢ False.
  Proof.
    intros Hsz. iIntros "H".
    iDestruct (VALID_PTR.valid_o_sub_size with "H") as %Hsz'.
    rewrite Hsz in Hsz'. destruct Hsz' as [? Hsz']; discriminate.
  Qed.

  Lemma missing_base_offset_invalid p base derived :
    parent_offset σ derived base = None ->
    _valid_ptr pred.Strict (p ,, o_base σ derived base) ⊢ False.
  Proof.
    intros Hoff. iIntros "H".
    iDestruct (VALID_PTR.o_base_directly_derives with "H") as %Hoff'.
    rewrite Hoff in Hoff'. destruct Hoff' as [? Hoff']; discriminate.
  Qed.

  Lemma missing_derived_offset_invalid p base derived :
    parent_offset σ derived base = None ->
    _valid_ptr pred.Strict (p ,, o_derived σ base derived) ⊢ False.
  Proof.
    intros Hoff. iIntros "H".
    iDestruct (VALID_PTR.o_derived_directly_derives with "H") as %Hoff'.
    rewrite Hoff in Hoff'. destruct Hoff' as [? Hoff']; discriminate.
  Qed.
End concrete_model.
