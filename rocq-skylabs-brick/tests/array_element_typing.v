Require Import iris.bi.monpred.
Require Import iris.base_logic.lib.iprop.
Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.notations.
Require Import skylabs.lang.cpp.code_notations.
Require Import skylabs.lang.cpp.semantics.genv.
Require Import skylabs.lang.cpp.semantics.types.
Require Import skylabs.lang.cpp.model.inductive_pointers_utils.
Require Import skylabs.lang.cpp.model.inductive_pointers.
Require Import skylabs.lang.cpp.model.simple_pred.
Require Import skylabs_brick.tests.object_representation_bytes.
Require Import skylabs.iris.extra.proofmode.proofmode.
Import PTRS_IMPL VALUES_DEFS_IMPL SimpleCPP address_sums.
Set Default Proof Using "Type*".


Section array_regressions.
  Context {thread_info : biIndex} {Σ : gFunctors}
    {Hlogic : SimpleCPP.cpp_logic thread_info Σ}.
  #[local] Existing Instance Hlogic.
  Context {σ : genv}.

  (** Two elements, each a zero-length byte array. *)
  Lemma zero_array_source_typed aid :
    aid <> null_alloc_id -> blocks_own (alloc_ptr aid 8) 0 1 ⊢
    type_ptr "unsigned char[0][2]"%cpp_type (alloc_ptr aid 8).
  Proof.
    intros Haid. iIntros "#B". rewrite /type_ptr.
    iSplit.
    { iPureIntro. intros E. apply (f_equal ptr_alloc_id) in E.
      simpl in E. injection E as E. contradiction. }
    iSplit.
    { iPureIntro. exists 1%N. split.
      - by rewrite !align_of_array align_of_uchar.
      - apply aligned_ptr_min. }
    iSplit; first (iPureIntro; by exists 0%N).
    rewrite /_valid_ptr _dot.unlock /DOT_dot /=.
    have Hroot : raw_path_valid pred.Strict (alloc_ptr_ aid 8) 0 1 [].
    { apply (raw_path_valid_nil _ _ _ _ 8%N); try done. left; lia. }
    iSplit.
    - iRight. iExists 0%Z, 1%Z. iFrame "B".
      iSplit; first (iPureIntro; exists aid; split; done).
      iPureIntro. exact Hroot.
    - iRight. iExists 0%Z, 1%Z. iFrame "B".
      iSplit; first (iPureIntro; exists aid; split; done).
      iPureIntro.
      change (raw_path_valid pred.Relaxed (alloc_ptr_ aid 8) 0 1
        ([] ++ [(o_sub_ "unsigned char[0][2]"%cpp_type 1,0%Z)])).
      apply (raw_path_valid_snoc _ _ _ _ _ _ 0%Z 8%N); try done.
      left; lia.
  Qed.

  Lemma zero_stride_array_element_typed aid :
    aid <> null_alloc_id -> blocks_own (alloc_ptr aid 8) 0 1 ⊢
    type_ptr "unsigned char[0]"%cpp_type
      (alloc_ptr aid 8 ,, o_sub σ "unsigned char[0]"%cpp_type 1).
  Proof.
    intros Haid. iIntros "B".
    iDestruct (zero_array_source_typed aid Haid with "B") as "T".
    iApply (VALID_PTR.type_ptr_o_sub (alloc_ptr aid 8) 1 2 "unsigned char[0]"%cpp_type
      ltac:(lia) with "T").
  Qed.

  Lemma zero_stride_array_element_strict aid :
    aid <> null_alloc_id -> blocks_own (alloc_ptr aid 8) 0 1 ⊢
    _valid_ptr pred.Strict (alloc_ptr aid 8 ,, o_sub σ "unsigned char[0]"%cpp_type 1).
  Proof.
    intros Haid. iIntros "B".
    iDestruct (zero_stride_array_element_typed aid Haid with "B") as "T".
    by iApply (type_ptr_strict_valid with "T").
  Qed.

  Lemma array_element_cancels aid :
    aid <> null_alloc_id -> blocks_own (alloc_ptr aid 8) (-1) 1 ⊢
    type_ptr "unsigned char"%cpp_type (alloc_ptr aid 8).
  Proof.
    intros Haid. iIntros "B".
    iDestruct (byte_source_typed aid Haid with "B") as "T".
    have Hrule := VALID_PTR.type_ptr_o_sub (byte_source aid) 1 2 "unsigned char"%cpp_type
      ltac:(lia).
    rewrite /byte_source -offset_ptr_dot o_dot_sub /= o_sub_0 // offset_ptr_id in Hrule.
    by iApply Hrule.
  Qed.
End array_regressions.
