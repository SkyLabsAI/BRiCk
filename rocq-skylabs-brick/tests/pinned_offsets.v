Require Import iris.bi.monpred.
Require Import iris.base_logic.lib.iprop.
Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.notations.
Require Import skylabs.lang.cpp.code_notations.
Require Import skylabs.lang.cpp.semantics.genv.
Require Import skylabs.lang.cpp.semantics.types.
Require Import skylabs.lang.cpp.algebra.cfrac.
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

  Lemma undefined_address_invalid vt p :
    ptr_vaddr p = None -> _valid_ptr vt p ⊢ False.
  Proof.
    intros Haddr. iIntros "V".
    iDestruct (_valid_ptr_vaddr (resolve:=σ) with "V") as %(va & Hva).
    congruence.
  Qed.

  Lemma underflow_invalid vt aid :
    _valid_ptr vt (alloc_ptr aid 8 ,, o_sub σ "unsigned char"%cpp_type (-9)) ⊢ False.
  Proof.
    apply undefined_address_invalid.
    rewrite _dot.unlock /DOT_dot /=. reflexivity.
  Qed.

  Lemma byte_offset_pinned_address p va i :
    ptr_vaddr p = Some va ->
    _valid_ptr pred.Relaxed (p ,, o_sub σ "unsigned char"%cpp_type i) ⊢
    ⌜(0 <= Z.of_N va + i)%Z⌝ ∗
    ⌜ptr_vaddr (p ,, o_sub σ "unsigned char"%cpp_type i) =
      Some (Z.to_N (Z.of_N va + i))⌝.
  Proof.
    intros Hp. iIntros "V".
    have Ho : eval_offset σ (o_sub σ "unsigned char"%cpp_type i) = Some i.
    { rewrite (eval_o_sub' σ _ i 1) //=. by rewrite Z.mul_1_l. }
    iDestruct (SimpleCPP.offset_pinned_ptr_pure σ _ i va p Ho Hp with "V")
      as "[%Hnonneg %Haddr]".
    iSplit; iPureIntro; done.
  Qed.

  (** An address does not require a physical-storage mapping. *)
  Lemma ghost_cell_retains_address ty p q v :
    is_heap_type ty ->
    type_ptr ty p ∗ mem_inj_own p None ∗ val_ p v q ∗ has_type_or_undef v ty ⊢
    ∃ va, ⌜ptr_vaddr p = Some va⌝ ∗ tptsto ty q p v.
  Proof.
    intros Hheap. iIntros "(#T & M & V & #Hv)".
    iDestruct (type_ptr_strict_valid with "T") as "Valid".
    iDestruct (_valid_ptr_vaddr (resolve:=σ) with "Valid") as %(va & Hva).
    iExists va. iSplit; first (iPureIntro; done).
    iApply tptsto_ghost_intro; first done. iFrame "T M V Hv".
  Qed.
End concrete_model.
