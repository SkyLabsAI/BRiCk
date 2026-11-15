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
Require Import skylabs.iris.extra.proofmode.proofmode.
Import PTRS_IMPL VALUES_DEFS_IMPL SimpleCPP address_sums.
Set Default Proof Using "Type*".

Section byte_typing.
  Context {thread_info : biIndex} {Σ : gFunctors}
    {Hlogic : SimpleCPP.cpp_logic thread_info Σ}.
  #[local] Existing Instance Hlogic.
  Context {σ : genv}.

  Definition byte_source aid : ptr :=
    alloc_ptr aid 8 ,, o_sub σ "unsigned char"%cpp_type (-1).

  Lemma byte_source_typed aid :
    aid <> null_alloc_id -> blocks_own (alloc_ptr aid 8) (-1) 1 ⊢
    type_ptr "unsigned char[2]"%cpp_type (byte_source aid).
  Proof.
    intros Haid. iIntros "#B". rewrite /type_ptr /byte_source.
    iSplit.
    { iPureIntro. rewrite _dot.unlock /DOT_dot /=. intros E.
      apply (f_equal ptr_alloc_id) in E. simpl in E.
      injection E as E. contradiction. }
    iSplit.
    { iPureIntro. exists 1%N. split.
      - by rewrite align_of_array align_of_uchar.
      - apply aligned_ptr_min. }
    iSplit; first (iPureIntro; by exists 2%N).
    rewrite /_valid_ptr _dot.unlock /DOT_dot /=.
    have Hsource : raw_path_valid pred.Strict (alloc_ptr_ aid 8) (-1) 1
        [(o_sub_ "unsigned char"%cpp_type (-1),(-1)%Z)].
    { change (raw_path_valid pred.Strict (alloc_ptr_ aid 8) (-1) 1
        ([] ++ [(o_sub_ "unsigned char"%cpp_type (-1),(-1)%Z)])).
      apply (raw_path_valid_snoc _ _ _ _ _ _ (-1)%Z 7%N); try done.
      - apply (raw_path_valid_nil _ _ _ _ 8%N); try done. left; lia.
      - left; lia. }
    iSplit.
    - iRight. iExists (-1)%Z, 1%Z. iFrame "B".
      iSplit; first (iPureIntro; exists aid; split; done).
      iPureIntro. exact Hsource.
    - iRight. iExists (-1)%Z, 1%Z. iFrame "B".
      iSplit; first (iPureIntro; exists aid; split; done).
      iPureIntro.
      change (raw_path_valid pred.Relaxed (alloc_ptr_ aid 8) (-1) 1
        ([(o_sub_ "unsigned char"%cpp_type (-1),(-1)%Z)] ++
         [(o_sub_ "unsigned char[2]"%cpp_type 1,2%Z)])).
      apply (raw_path_valid_snoc _ _ _ _ _ _ 1%Z 9%N); try done.
      right; done.
  Qed.

  Lemma byte_zero_typed aid :
    aid <> null_alloc_id -> blocks_own (alloc_ptr aid 8) (-1) 1 ⊢
    type_ptr "unsigned char"%cpp_type (byte_source aid).
  Proof.
    intros Haid. iIntros "B".
    iDestruct (byte_source_typed aid Haid with "B") as "T".
    have Hrule := type_ptr_obj_repr_byte "unsigned char[2]"%cpp_type
      (byte_source aid) 0 2 eq_refl ltac:(lia).
    rewrite o_sub_0 // offset_ptr_id in Hrule.
    by iApply Hrule.
  Qed.

  Lemma byte_one_cancels aid :
    aid <> null_alloc_id -> blocks_own (alloc_ptr aid 8) (-1) 1 ⊢
    type_ptr "unsigned char"%cpp_type (alloc_ptr aid 8).
  Proof.
    intros Haid. iIntros "B".
    iDestruct (byte_source_typed aid Haid with "B") as "T".
    have Hrule := type_ptr_obj_repr_byte "unsigned char[2]"%cpp_type
      (byte_source aid) 1 2 eq_refl ltac:(lia).
    rewrite /byte_source -offset_ptr_dot o_dot_sub /= o_sub_0 // offset_ptr_id in Hrule.
    by iApply Hrule.
  Qed.

  Lemma byte_one_past_valid aid :
    aid <> null_alloc_id -> blocks_own (alloc_ptr aid 8) (-1) 1 ⊢
    _valid_ptr pred.Relaxed (alloc_ptr aid 8 ,, o_sub σ "unsigned char"%cpp_type 1).
  Proof.
    intros Haid. iIntros "B".
    iDestruct (byte_one_cancels aid Haid with "B") as "T".
    by iApply (type_ptr_valid_plus_one with "T").
  Qed.

  Lemma byte_one_past_not_strict aid :
    blocks_own (alloc_ptr aid 8) (-1) 1 ⊢
    _valid_ptr pred.Strict (alloc_ptr aid 8 ,, o_sub σ "unsigned char"%cpp_type 1) -∗ False.
  Proof.
    iIntros "B V". rewrite /_valid_ptr.
    iDestruct "V" as "[[_ %Hbad]|V]"; first discriminate.
    rewrite _dot.unlock /DOT_dot /=.
    iDestruct "V" as (l h) "(B' & _ & %Hpath)".
    iDestruct (blocks_own_range_agree with "[$B $B']") as %E.
    injection E as <- <-.
    destruct (raw_path_valid_end _ _ _ _ _ Hpath)
      as (z & va & Hz & _ & _ & Hr).
    change (Some 1%Z = Some z) in Hz. injection Hz as <-.
    destruct Hr as [Hr|[Hbad _]]; [lia|discriminate].
  Qed.
End byte_typing.
