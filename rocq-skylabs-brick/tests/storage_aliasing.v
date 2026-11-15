Require Import skylabs.lang.cpp.algebra.cfrac.
Require Import iris.bi.monpred.
Require Import iris.base_logic.lib.iprop.
Require Import skylabs.prelude.base.
Require Import skylabs.prelude.option.
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

Section pure_aliases.
  Context {σ : genv}.

  Lemma zero_field_congruent aid f :
    o_field_off σ f = Some 0%Z ->
    ptr_cong σ (alloc_ptr aid 8) (alloc_ptr aid 8 ,, o_field σ f).
  Proof.
    intros Hf. exists (alloc_ptr aid 8), o_id, (o_field σ f).
    split; first by rewrite offset_ptr_id.
    split; first done.
    apply same_property_iff. exists 0%Z. split; first done.
    by rewrite /eval_offset /o_field /mkOffset /mk_offset_seg /= Hf.
  Qed.

  Lemma zero_field_distinct aid f :
    o_field_off σ f = Some 0%Z ->
    alloc_ptr aid 8 <> alloc_ptr aid 8 ,, o_field σ f.
  Proof.
    intros Hf E.
    apply (f_equal (fun p => match p with
      | invalid_ptr_ => [] | offset_ptr _ off => `off end)) in E.
    rewrite _dot.unlock /DOT_dot /= /o_field /mkOffset /mk_offset_seg /= Hf /= in E.
    discriminate.
  Qed.

  Lemma zero_field_storage_key aid f :
    o_field_off σ f = Some 0%Z ->
    storage_key (alloc_ptr aid 8) = storage_key (alloc_ptr aid 8 ,, o_field σ f).
  Proof.
    intros Hf. apply (storage_key_cong σ); first by exists 0%Z.
    by apply zero_field_congruent.
  Qed.
End pure_aliases.

Lemma distinct_allocations_keep_storage aid1 aid2 :
  aid1 <> aid2 -> storage_key (alloc_ptr aid1 8) <> storage_key (alloc_ptr aid2 8).
Proof.
  intros Hne E. rewrite /storage_key /alloc_ptr /lift_root_ptr /= in E.
  injection E as E. contradiction.
Qed.

Lemma undefined_storage_keys_injective root (off1 off2 : offset) :
  eval_raw_offset (`off1) = None -> eval_raw_offset (`off2) = None ->
  storage_key (offset_ptr root off1) = storage_key (offset_ptr root off2) -> off1 = off2.
Proof.
  intros H1 H2 E. rewrite /storage_key H1 H2 in E. by injection E.
Qed.

Section concrete_model.
  Context {thread_info : biIndex} {Σ : gFunctors}
    {Hlogic : SimpleCPP.cpp_logic thread_info Σ}.
  #[local] Existing Instance Hlogic.
  Context {σ : genv}.

  Lemma root_byte_typed aid :
    aid <> null_alloc_id -> blocks_own (alloc_ptr aid 8) 0 1 ⊢
    type_ptr "unsigned char"%cpp_type (alloc_ptr aid 8).
  Proof.
    intros Haid. iIntros "#B". rewrite /type_ptr.
    iSplit.
    { iPureIntro. intros E. apply (f_equal ptr_alloc_id) in E.
      simpl in E. injection E as E. contradiction. }
    iSplit.
    { iPureIntro. exists 1%N. split; [apply align_of_uchar|apply aligned_ptr_min]. }
    iSplit; first (iPureIntro; by exists 1%N).
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
        ([] ++ [(o_sub_ "unsigned char"%cpp_type 1,1%Z)])).
      apply (raw_path_valid_snoc _ _ _ _ _ _ 1%Z 9%N); try done.
      right; done.
  Qed.

  Lemma zero_field_byte_typed aid f :
    aid <> null_alloc_id -> o_field_off σ f = Some 0%Z ->
    blocks_own (alloc_ptr aid 8) 0 1 ⊢
    type_ptr "unsigned char"%cpp_type (alloc_ptr aid 8 ,, o_field σ f).
  Proof.
    intros Haid Hf. iIntros "#B". rewrite /type_ptr.
    iSplit.
    { iPureIntro. intros E. apply (f_equal ptr_alloc_id) in E.
      rewrite _dot.unlock /DOT_dot /= in E. injection E as E. contradiction. }
    iSplit.
    { iPureIntro. exists 1%N. split; [apply align_of_uchar|apply aligned_ptr_min]. }
    iSplit; first (iPureIntro; by exists 1%N).
    rewrite /_valid_ptr _dot.unlock /DOT_dot /=.
    have Hroot : raw_path_valid pred.Strict (alloc_ptr_ aid 8) 0 1 [].
    { apply (raw_path_valid_nil _ _ _ _ 8%N); try done. left; lia. }
    have Hfield : raw_path_valid pred.Strict (alloc_ptr_ aid 8) 0 1 [(o_field_ f,0%Z)].
    { change (raw_path_valid pred.Strict (alloc_ptr_ aid 8) 0 1 ([] ++ [(o_field_ f,0%Z)])).
      apply (raw_path_valid_snoc _ _ _ _ _ _ 0%Z 8%N); try done.
      left; lia. }
    iSplit.
    - iRight. iExists 0%Z, 1%Z. iFrame "B".
      iSplit; first (iPureIntro; exists aid; split; done).
      iPureIntro. rewrite /o_field /mkOffset /mk_offset_seg /= Hf /=. exact Hfield.
    - iRight. iExists 0%Z, 1%Z. iFrame "B".
      iSplit; first (iPureIntro; exists aid; split; done).
      iPureIntro. rewrite /o_field /mkOffset /mk_offset_seg /= Hf /=.
      change (raw_path_valid pred.Relaxed (alloc_ptr_ aid 8) 0 1
        ([(o_field_ f,0%Z)] ++ [(o_sub_ "unsigned char"%cpp_type 1,1%Z)])).
      apply (raw_path_valid_snoc _ _ _ _ _ _ 1%Z 9%N); try done.
      right; done.
  Qed.

  Lemma zero_field_typed_congruence aid f :
    aid <> null_alloc_id -> o_field_off σ f = Some 0%Z ->
    blocks_own (alloc_ptr aid 8) 0 1 ⊢
    ptr_congP σ (alloc_ptr aid 8) (alloc_ptr aid 8 ,, o_field σ f).
  Proof.
    intros Haid Hf. iIntros "#B". iSplit.
    - iPureIntro. by apply zero_field_congruent.
    - iSplit; [by iApply root_byte_typed|by iApply zero_field_byte_typed].
  Qed.

  (** Construct a ghost-backed source and transport its value and permission. *)
  Lemma ghost_alias_cell aid f q v :
    aid <> null_alloc_id -> o_field_off σ f = Some 0%Z ->
    blocks_own (alloc_ptr aid 8) 0 1 ∗ mem_inj_own (alloc_ptr aid 8) None ∗
    val_ (alloc_ptr aid 8) v q ∗ has_type_or_undef v Tbyte ⊢
    tptsto Tbyte q (alloc_ptr aid 8 ,, o_field σ f) v.
  Proof.
    intros Haid Hf. iIntros "(#B & M & V & Hv)".
    iDestruct (zero_field_typed_congruence aid f Haid Hf with "B") as "C".
    iApply (tptsto_ptr_congP_transport with "C").
    iApply tptsto_ghost_intro; first done.
    iFrame "M V Hv". by iApply root_byte_typed.
  Qed.

  (** Construct the physical source at the same injected address. *)
  Lemma physical_alias_cell aid f q v a vs :
    aid <> null_alloc_id -> o_field_off σ f = Some 0%Z ->
    blocks_own (alloc_ptr aid 8) 0 1 ∗ mem_inj_own (alloc_ptr aid 8) (Some a) ∗
    encodes Tbyte v vs ∗ bytes a vs q ∗ vbytes a vs (cfrac.cQp.frac q) ∗ has_type_or_undef v Tbyte ⊢
    tptsto Tbyte q (alloc_ptr aid 8 ,, o_field σ f) v.
  Proof.
    intros Haid Hf. iIntros "(#B & M & E & Bytes & VBytes & Hv)".
    iDestruct (zero_field_typed_congruence aid f Haid Hf with "B") as "C".
    iApply (tptsto_ptr_congP_transport with "C").
    iApply (tptsto_physical_intro Tbyte q (alloc_ptr aid 8) v a vs); first done.
    iFrame "M E Bytes VBytes Hv". by iApply root_byte_typed.
  Qed.

  Lemma ghost_alias_write aid f before after :
    aid <> null_alloc_id -> o_field_off σ f = Some 0%Z ->
    blocks_own (alloc_ptr aid 8) 0 1 ∗ mem_inj_own (alloc_ptr aid 8) None ∗
    val_ (alloc_ptr aid 8) before 1$m ∗ has_type_or_undef before Tbyte ∗
    has_type_or_undef after Tbyte ⊢
    |==> tptsto Tbyte 1$m (alloc_ptr aid 8 ,, o_field σ f) after.
  Proof.
    intros Haid Hf. iIntros "(#B & #M & V & Hbefore & Hafter)".
    iDestruct (ghost_alias_cell aid f 1$m before Haid Hf with "[$B $M $V $Hbefore]") as "T".
    iApply (tptsto_ghost_update with "[$T $Hafter M]").
    rewrite /mem_inj_own -(zero_field_storage_key aid f Hf). iExact "M".
  Qed.

  Lemma alias_byte_value_agree p1 p2 q1 q2 v1 v2 :
    ptr_cong σ p1 p2 ->
    tptsto Tbyte q1 p1 v1 ∗ tptsto Tbyte q2 p2 v2 ⊢ ⌜v1 = v2⌝.
  Proof.
    intros Hcong. iIntros "(T1 & T2)".
    iDestruct (tptsto_type_ptr with "T1") as "#P1".
    iDestruct (tptsto_type_ptr with "T2") as "#P2".
    iAssert (ptr_congP σ p1 p2) as "C".
    { iFrame "P1 P2". done. }
    iDestruct (tptsto_ptr_congP_transport with "C T1") as "T1".
    iDestruct (tptsto_agree with "T1 T2") as %E. done.
  Qed.
End concrete_model.
