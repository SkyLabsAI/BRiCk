Require Import iris.algebra.gmap.
Require Import iris.algebra.agree.
Require Import skylabs.iris.extra.base_logic.own_instances.
Require Import skylabs_brick.tests.field_validity.
Require Import iris.bi.monpred.
Require Import iris.base_logic.lib.iprop.
Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.notations.
Require Import skylabs.lang.cpp.code_notations.
Require Import skylabs.lang.cpp.semantics.genv.
Require Import skylabs.lang.cpp.semantics.types.
Require Import skylabs.lang.cpp.model.simple_pointers_utils.
Require Import skylabs.lang.cpp.model.inductive_pointers_utils.
Require Import skylabs.lang.cpp.model.inductive_pointers.
Require Import skylabs.lang.cpp.model.simple_pred.
Require Import skylabs.iris.extra.proofmode.proofmode.
Import PTRS_IMPL VALUES_DEFS_IMPL SimpleCPP address_sums.
Set Default Proof Using "Type*".

Section concrete_model.
  Context {thread_info : biIndex} {Σ : gFunctors}
    {Hlogic : SimpleCPP.cpp_logic thread_info Σ}.
  #[local] Existing Instance Hlogic.
  Context {σ : genv}.

  Lemma blocks_range_agree p l1 h1 l2 h2 :
    blocks_own p l1 h1 ∗ blocks_own p l2 h2 ⊢ ⌜(l1,h1) = (l2,h2)⌝.
  Proof.
    rewrite /blocks_own -own_op singleton_op.
    rewrite own_valid internal_cmra_valid_discrete singleton_valid.
    by iIntros "!%" => /= /to_agree_op_inv_L.
  Qed.

  Lemma boundary_field_not_strict aid f :
    o_field_off σ f = Some 1%Z ->
    blocks_own (alloc_ptr aid 8) 0 1 ⊢
    _valid_ptr pred.Strict (alloc_ptr aid 8 ,, o_field σ f) -∗ False.
  Proof.
    intros Hf. iIntros "B V".
    rewrite /_valid_ptr. iDestruct "V" as "[[_ %Hvt]|V]"; first discriminate.
    rewrite _dot.unlock /DOT_dot /=.
    iDestruct "V" as (l h) "(B' & _ & %Hpath)".
    iDestruct (blocks_range_agree with "[$B $B']") as %E.
    injection E as <- <-.
    rewrite /o_field /mkOffset /mk_offset_seg /= Hf /= in Hpath.
    destruct (Hpath [(o_field_ f,1%Z)] [] eq_refl) as (z & va & Hz & _ & _ & Hr).
    change (Some 1%Z = Some z) in Hz. injection Hz as <-.
    destruct Hr as [Hr|[_ [Hbad _]]]; [lia|discriminate].
  Qed.

  (** A positive subscript cannot pass through a one-past field, even when
      its element type has zero byte size. *)
  Lemma boundary_zero_stride_invalid aid f :
    o_field_off σ f = Some 1%Z ->
    blocks_own (alloc_ptr aid 8) 0 1 ⊢
    _valid_ptr pred.Relaxed
      (alloc_ptr aid 8 ,, o_field σ f ,, o_sub σ "unsigned char[0]"%cpp_type 1) -∗ False.
  Proof.
    intros Hf. iIntros "B V".
    iDestruct (VALID_PTR.strict_valid_ptr_field_sub
      (alloc_ptr aid 8) "unsigned char[0]"%cpp_type 1 f pred.Relaxed
      ltac:(lia) with "V") as "S".
    iApply (boundary_field_not_strict aid f Hf with "B S").
  Qed.

  (** Index zero is the identity and retains relaxed boundary validity. *)
  Lemma boundary_zero_index_valid aid f :
    aid <> null_alloc_id -> o_field_off σ f = Some 1%Z ->
    blocks_own (alloc_ptr aid 8) 0 1 ⊢
    _valid_ptr pred.Relaxed
      (alloc_ptr aid 8 ,, o_field σ f ,, o_sub σ "unsigned char[0]"%cpp_type 0).
  Proof.
    intros Haid Hf. rewrite o_sub_0; last done.
    rewrite offset_ptr_id. exact (one_past_field_relaxed aid f Haid Hf).
  Qed.

  Lemma interior_zero_stride_valid aid f :
    aid <> null_alloc_id -> o_field_off σ f = Some 1%Z ->
    blocks_own (alloc_ptr aid 8) 0 2 ⊢
    _valid_ptr pred.Strict
      (alloc_ptr aid 8 ,, o_field σ f ,, o_sub σ "unsigned char[0]"%cpp_type 1).
  Proof.
    intros Haid Hf. rewrite /_valid_ptr _dot.unlock /DOT_dot /=.
    iIntros "B". iRight. iExists 0%Z, 2%Z. iFrame "B".
    iSplit; first (iPureIntro; exists aid; split; done).
    iPureIntro. rewrite /o_field /mkOffset /mk_offset_seg /= Hf /=.
    change (raw_path_valid pred.Strict (alloc_ptr_ aid 8) 0 2
      ([(o_field_ f,1%Z)] ++ [(o_sub_ "unsigned char[0]"%cpp_type 1,0%Z)])).
    apply (raw_path_valid_snoc _ _ _ _ _ _ 1%Z 9%N); try done.
    - change (raw_path_valid pred.Strict (alloc_ptr_ aid 8) 0 2
        ([] ++ [(o_field_ f,1%Z)])).
      apply (raw_path_valid_snoc _ _ _ _ _ _ 1%Z 9%N); try done.
      + apply (raw_path_valid_nil _ _ _ _ 8%N); try done. left; lia.
      + left; lia.
    - left; lia.
  Qed.

  Lemma positive_stride_one_past_valid aid f :
    aid <> null_alloc_id -> o_field_off σ f = Some 1%Z ->
    blocks_own (alloc_ptr aid 8) 0 2 ⊢
    _valid_ptr pred.Relaxed
      (alloc_ptr aid 8 ,, o_field σ f ,, o_sub σ "unsigned char"%cpp_type 1).
  Proof.
    intros Haid Hf. rewrite /_valid_ptr _dot.unlock /DOT_dot /=.
    iIntros "B". iRight. iExists 0%Z, 2%Z. iFrame "B".
    iSplit; first (iPureIntro; exists aid; split; done).
    iPureIntro. rewrite /o_field /mkOffset /mk_offset_seg /= Hf /=.
    change (raw_path_valid pred.Relaxed (alloc_ptr_ aid 8) 0 2
      ([(o_field_ f,1%Z)] ++ [(o_sub_ "unsigned char"%cpp_type 1,1%Z)])).
    apply (raw_path_valid_snoc _ _ _ _ _ _ 2%Z 10%N); try done.
    - change (raw_path_valid pred.Strict (alloc_ptr_ aid 8) 0 2
        ([] ++ [(o_field_ f,1%Z)])).
      apply (raw_path_valid_snoc _ _ _ _ _ _ 1%Z 9%N); try done.
      + apply (raw_path_valid_nil _ _ _ _ 8%N); try done. left; lia.
      + left; lia.
    - right; done.
  Qed.
End concrete_model.
