Require Import iris.bi.monpred.
Require Import iris.base_logic.lib.iprop.
Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.notations.
Require Import skylabs.lang.cpp.code_notations.
Require Import skylabs.lang.cpp.semantics.alloc_id.
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

  Lemma allocated_field_valid aid f :
    aid <> null_alloc_id -> o_field_off σ f = Some 1%Z ->
    blocks_own (alloc_ptr aid 8) 0 2 ⊢
    _valid_ptr pred.Strict (alloc_ptr aid 8 ,, o_field σ f).
  Proof.
    intros Haid Hf. rewrite /_valid_ptr _dot.unlock /DOT_dot /=.
    iIntros "B". iRight. iExists 0%Z, 2%Z. iFrame "B".
    iSplit; first (iPureIntro; exists aid; split; done).
    iPureIntro. rewrite /o_field /mkOffset /mk_offset_seg /= Hf /=.
    change (raw_path_valid pred.Strict (alloc_ptr_ aid 8) 0 2
      ([] ++ [(o_field_ f, 1%Z)])).
    apply (raw_path_valid_snoc _ _ _ _ _ _ 1%Z 9%N); try done.
    - apply (raw_path_valid_nil _ _ _ _ 8%N); try done. left; lia.
    - left; lia.
  Qed.

  (** A field at the end of a range retains relaxed validity, preserving the
      boundary behavior of zero-sized members. *)
  Lemma one_past_field_relaxed aid f :
    aid <> null_alloc_id -> o_field_off σ f = Some 1%Z ->
    blocks_own (alloc_ptr aid 8) 0 1 ⊢
    _valid_ptr pred.Relaxed (alloc_ptr aid 8 ,, o_field σ f).
  Proof.
    intros Haid Hf. rewrite /_valid_ptr _dot.unlock /DOT_dot /=.
    iIntros "B". iRight. iExists 0%Z, 1%Z. iFrame "B".
    iSplit; first (iPureIntro; exists aid; split; done).
    iPureIntro. rewrite /o_field /mkOffset /mk_offset_seg /= Hf /=.
    change (raw_path_valid pred.Relaxed (alloc_ptr_ aid 8) 0 1
      ([] ++ [(o_field_ f, 1%Z)])).
    apply (raw_path_valid_snoc _ _ _ _ _ _ 1%Z 9%N); try done.
    - apply (raw_path_valid_nil _ _ _ _ 8%N); try done. left; lia.
    - right; done.
  Qed.

  Lemma allocated_nested_fields_valid aid f g :
    aid <> null_alloc_id ->
    o_field_off σ f = Some 1%Z -> o_field_off σ g = Some 1%Z ->
    blocks_own (alloc_ptr aid 8) 0 3 ⊢
    _valid_ptr pred.Strict (alloc_ptr aid 8 ,, o_field σ f ,, o_field σ g).
  Proof.
    intros Haid Hf Hg. rewrite /_valid_ptr _dot.unlock /DOT_dot /=.
    iIntros "B". iRight. iExists 0%Z, 3%Z. iFrame "B".
    iSplit; first (iPureIntro; exists aid; split; done).
    iPureIntro. rewrite /o_field /mkOffset /mk_offset_seg /= Hf Hg /=.
    change (raw_path_valid pred.Strict (alloc_ptr_ aid 8) 0 3
      ([(o_field_ f, 1%Z)] ++ [(o_field_ g, 1%Z)])).
    apply (raw_path_valid_snoc _ _ _ _ _ _ 2%Z 10%N); try done.
    - change (raw_path_valid pred.Strict (alloc_ptr_ aid 8) 0 3
        ([] ++ [(o_field_ f, 1%Z)])).
      apply (raw_path_valid_snoc _ _ _ _ _ _ 1%Z 9%N); try done.
      + apply (raw_path_valid_nil _ _ _ _ 8%N); try done. left; lia.
      + left; lia.
    - left; lia.
  Qed.

  (** All addresses are nonzero and the final displacement is in range, but
      the parent lies before the allocation's lower bound. *)
  Lemma out_of_range_prefix_rejected aid f :
    ~ raw_path_valid pred.Strict (alloc_ptr_ aid 8) 0 2
      [(o_sub_ "unsigned char"%cpp_type (-1), (-1)%Z); (o_field_ f, 2%Z)].
  Proof.
    intros Hpath.
    destruct (Hpath [(o_sub_ "unsigned char"%cpp_type (-1), (-1)%Z)]
      [(o_field_ f, 2%Z)] eq_refl) as (z & va & Hz & _ & _ & Hr).
    change (Some (-1)%Z = Some z) in Hz. injection Hz as <-.
    destruct Hr as [Hr|[Hbad _]]; [lia|discriminate].
  Qed.

  Lemma zero_address_parent_invalid aid vt :
    aid <> null_alloc_id ->
    _valid_ptr vt (alloc_ptr aid 8 ,, o_sub σ "unsigned char"%cpp_type (-8)) ⊢ False.
  Proof.
    intros Haid. iIntros "H".
    iDestruct (_valid_ptr_cases (resolve:=σ) with "H") as %Hcases.
    destruct Hcases as [Heq|[_ (va & Hva & Hnz)]].
    - apply (f_equal ptr_alloc_id) in Heq.
      rewrite _dot.unlock /DOT_dot /= in Heq.
      iPureIntro. injection Heq as E. apply Haid. exact E.
    - rewrite _dot.unlock /DOT_dot /= in Hva.
      injection Hva as E. subst va. contradiction.
  Qed.

  (** The previous model could validate this field from a block anchored at the
      field itself. Parent validity now excludes it, independently of storage. *)
  Lemma field_from_zero_parent_invalid aid f vt :
    aid <> null_alloc_id ->
    _valid_ptr vt
      (alloc_ptr aid 8 ,, o_sub σ "unsigned char"%cpp_type (-8) ,, o_field σ f) ⊢ False.
  Proof.
    intros Haid. rewrite VALID_PTR._valid_ptr_field.
    exact (zero_address_parent_invalid aid vt Haid).
  Qed.
End concrete_model.
