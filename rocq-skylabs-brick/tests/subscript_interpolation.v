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

Require Import skylabs_brick.tests.field_subscript_validity.

(** A well-formed stored segment need not use the current environment's size. *)
Definition stale_sub_offset : offset :=
  exist _ [(o_sub_ "unsigned char[0]"%cpp_type 1,1%Z)]
    (singleton_raw_offset_wf (os:=(o_sub_ "unsigned char[0]"%cpp_type 1,1%Z)) I).

Definition stale_sub_ptr aid : ptr := alloc_ptr aid 8 ,, stale_sub_offset.

Section concrete_model.
  Context {thread_info : biIndex} {Σ : gFunctors}
    {Hlogic : SimpleCPP.cpp_logic thread_info Σ}.
  #[local] Existing Instance Hlogic.
  Context {σ : genv}.

  Lemma stale_boundary_valid aid :
    aid <> null_alloc_id ->
    blocks_own (alloc_ptr aid 8) 0 1 ⊢ _valid_ptr pred.Relaxed (stale_sub_ptr aid).
  Proof.
    intros Haid. rewrite /_valid_ptr /stale_sub_ptr _dot.unlock /DOT_dot /=.
    iIntros "B". iRight. iExists 0%Z, 1%Z. iFrame "B".
    iSplit; first (iPureIntro; exists aid; split; done).
    iPureIntro.
    change (raw_path_valid pred.Relaxed (alloc_ptr_ aid 8) 0 1
      ([] ++ [(o_sub_ "unsigned char[0]"%cpp_type 1,1%Z)])).
    apply (raw_path_valid_snoc _ _ _ _ _ _ 1%Z 9%N); try done.
    - apply (raw_path_valid_nil _ _ _ _ 8%N); try done. left; lia.
    - right; done.
  Qed.

  Lemma stale_boundary_step_two_valid aid :
    aid <> null_alloc_id ->
    blocks_own (alloc_ptr aid 8) 0 1 ⊢
    _valid_ptr pred.Relaxed (stale_sub_ptr aid ,, o_sub σ "unsigned char[0]"%cpp_type 2).
  Proof.
    intros Haid. rewrite /_valid_ptr /stale_sub_ptr _dot.unlock /DOT_dot /=.
    iIntros "B". iRight. iExists 0%Z, 1%Z. iFrame "B".
    iSplit; first (iPureIntro; exists aid; split; done).
    iPureIntro.
    change (raw_path_valid pred.Relaxed (alloc_ptr_ aid 8) 0 1
      ([] ++ [(o_sub_ "unsigned char[0]"%cpp_type 3,1%Z)])).
    apply (raw_path_valid_snoc _ _ _ _ _ _ 1%Z 9%N); try done.
    - apply (raw_path_valid_nil _ _ _ _ 8%N); try done. left; lia.
    - right; done.
  Qed.

  Lemma stale_boundary_not_strict aid :
    blocks_own (alloc_ptr aid 8) 0 1 ⊢
    _valid_ptr pred.Strict (stale_sub_ptr aid) -∗ False.
  Proof.
    iIntros "B V".
    rewrite /_valid_ptr. iDestruct "V" as "[[_ %Hvt]|V]"; first discriminate.
    rewrite /stale_sub_ptr _dot.unlock /DOT_dot /=.
    iDestruct "V" as (l h) "(B' & _ & %Hpath)".
    iDestruct (blocks_range_agree with "[$B $B']") as %E.
    injection E as <- <-.
    destruct (Hpath [(o_sub_ "unsigned char[0]"%cpp_type 1,1%Z)] [] eq_refl)
      as (z & va & Hz & _ & _ & Hr).
    change (Some 1%Z = Some z) in Hz. injection Hz as <-.
    destruct Hr as [Hr|[_ [Hbad _]]]; [lia|discriminate].
  Qed.

  (** Relaxed interpolation remains available for zero-sized types, even
      when a stored displacement does not match the current type's size. *)
  Lemma zero_stride_relaxed_interpolation aid :
    aid <> null_alloc_id -> blocks_own (alloc_ptr aid 8) 0 1 ⊢
    _valid_ptr pred.Relaxed
      (stale_sub_ptr aid ,, o_sub σ "unsigned char[0]"%cpp_type 1).
  Proof.
    intros Haid. iIntros "#B".
    iDestruct (stale_boundary_valid aid Haid with "B") as "V0".
    iDestruct (stale_boundary_step_two_valid aid Haid with "B") as "V2".
    iApply (SimpleCPP._valid_ptr_sub 0 1 2 (stale_sub_ptr aid)
      "unsigned char[0]"%cpp_type pred.Relaxed pred.Relaxed pred.Relaxed
      ltac:(lia) ltac:(intros Hbad; discriminate) with "[V0] V2").
    by rewrite o_sub_0 // offset_ptr_id.
  Qed.

  Lemma zero_stride_has_no_positive_size :
    ~ exists sz, size_of σ "unsigned char[0]"%cpp_type = Some sz /\ (0 < sz)%N.
  Proof.
    intros (sz & Hsz & Hpos). change (Some 0%N = Some sz) in Hsz.
    injection Hsz as <-. lia.
  Qed.

  Lemma signed_left_endpoint_valid aid :
    aid <> null_alloc_id -> blocks_own (alloc_ptr aid 8) (-1) 1 ⊢
    _valid_ptr pred.Strict (alloc_ptr aid 8 ,, o_sub σ "unsigned char"%cpp_type (-1)).
  Proof.
    intros Haid. rewrite /_valid_ptr _dot.unlock /DOT_dot /=.
    iIntros "B". iRight. iExists (-1)%Z, 1%Z. iFrame "B".
    iSplit; first (iPureIntro; exists aid; split; done).
    iPureIntro.
    change (raw_path_valid pred.Strict (alloc_ptr_ aid 8) (-1) 1
      ([] ++ [(o_sub_ "unsigned char"%cpp_type (-1),(-1)%Z)])).
    apply (raw_path_valid_snoc _ _ _ _ _ _ (-1)%Z 7%N); try done.
    - apply (raw_path_valid_nil _ _ _ _ 8%N); try done. left; lia.
    - left; lia.
  Qed.

  Lemma signed_right_endpoint_valid aid :
    aid <> null_alloc_id -> blocks_own (alloc_ptr aid 8) (-1) 1 ⊢
    _valid_ptr pred.Relaxed (alloc_ptr aid 8 ,, o_sub σ "unsigned char"%cpp_type 1).
  Proof.
    intros Haid. rewrite /_valid_ptr _dot.unlock /DOT_dot /=.
    iIntros "B". iRight. iExists (-1)%Z, 1%Z. iFrame "B".
    iSplit; first (iPureIntro; exists aid; split; done).
    iPureIntro.
    change (raw_path_valid pred.Relaxed (alloc_ptr_ aid 8) (-1) 1
      ([] ++ [(o_sub_ "unsigned char"%cpp_type 1,1%Z)])).
    apply (raw_path_valid_snoc _ _ _ _ _ _ 1%Z 9%N); try done.
    - apply (raw_path_valid_nil _ _ _ _ 8%N); try done. left; lia.
    - right; done.
  Qed.

  (** The interior pointer cancels its trailing subscript completely. *)
  Lemma signed_cancellation_interpolation aid :
    aid <> null_alloc_id -> blocks_own (alloc_ptr aid 8) (-1) 1 ⊢
    _valid_ptr pred.Strict (alloc_ptr aid 8).
  Proof using Type* σ.

    intros Haid. iIntros "#B".
    iDestruct (signed_left_endpoint_valid aid Haid with "B") as "Vi".
    iDestruct (signed_right_endpoint_valid aid Haid with "B") as "Vk".
    have Hpositive : exists sz, size_of σ "unsigned char"%cpp_type = Some sz /\ (0 < sz)%N.
    { exists 1%N. split; [done|lia]. }
    have Hrule := SimpleCPP.strict_valid_ptr_sub_guarded 0 1 2
      (alloc_ptr aid 8 ,, o_sub σ "unsigned char"%cpp_type (-1))
      "unsigned char"%cpp_type pred.Strict pred.Relaxed ltac:(lia) Hpositive.
    rewrite !o_sub_0 // !offset_ptr_id in Hrule.
    rewrite -!offset_ptr_dot !o_dot_sub /= in Hrule.
    rewrite o_sub_0 // offset_ptr_id in Hrule.
    iApply (Hrule with "Vi Vk").
  Qed.
End concrete_model.
