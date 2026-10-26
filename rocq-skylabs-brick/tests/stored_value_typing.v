Require Import iris.bi.monpred.
Require Import iris.base_logic.lib.iprop.
Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.semantics.genv.
Require Import skylabs.lang.cpp.semantics.ptrs.
Require Import skylabs.lang.cpp.algebra.cfrac.
Require Import skylabs.lang.cpp.model.inductive_pointers.
Require Import skylabs.lang.cpp.model.simple_pred.
Require Import skylabs.iris.extra.proofmode.proofmode.
Import PTRS_IMPL VALUES_DEFS_IMPL SimpleCPP.
Set Default Proof Using "Type*".

Definition bool_bytes (b : bool) : list runtime_val :=
  [Rval (if b then 1%N else 0%N)].

Section concrete_model.
  Context {thread_info : biIndex} {Σ : gFunctors}
    {Hlogic : SimpleCPP.cpp_logic thread_info Σ}.
  #[local] Existing Instance Hlogic.
  Context {σ : genv}.

  Lemma bool_value_type b : ⊢ has_type (Vbool b) Tbool.
  Proof.
    rewrite /has_type /Vbool /=. iSplit; iPureIntro.
    - apply has_type_prop_bool. by exists b.
    - done.
  Qed.

  (** Both representations can be constructed without assuming points-to. *)
  Lemma ghost_boolean_cell p q b :
    type_ptr Tbool p ∗ mem_inj_own p None ∗ val_ p (Vbool b) q ⊢
    tptsto Tbool q p (Vbool b).
  Proof.
    iIntros "(T & M & V)". iApply tptsto_ghost_intro; first done.
    iFrame. iLeft. iApply bool_value_type.
  Qed.

  Lemma physical_boolean_cell p q a b :
    type_ptr Tbool p ∗ mem_inj_own p (Some a) ∗
    bytes a (bool_bytes b) q ∗ vbytes a (bool_bytes b) q ⊢
    tptsto Tbool q p (Vbool b).
  Proof.
    iIntros "(T & M & B & V)".
    iApply (tptsto_physical_intro Tbool q p (Vbool b) a (bool_bytes b)); first done.
    iFrame. iSplit.
    - iPureIntro. by destruct b.
    - iLeft. iApply bool_value_type.
  Qed.

  Lemma ghost_boolean_write p before after :
    mem_inj_own p None ∗ tptsto Tbool 1$m p (Vbool before) ⊢
    |==> tptsto Tbool 1$m p (Vbool after).
  Proof.
    iIntros "(M & H)". iApply tptsto_ghost_update.
    iFrame. iLeft. iApply bool_value_type.
  Qed.

  Lemma ghost_forget_value ty p v :
    mem_inj_own p None ∗ tptsto ty 1$m p v ⊢
    |==> tptsto ty 1$m p Vundef.
  Proof.
    iIntros "(M & H)". iApply tptsto_ghost_update. iFrame. by iRight.
  Qed.

  (** The invariant constrains the value, not just the cell's address. *)
  Lemma stored_boolean_rejects_two p q :
    tptsto Tbool q p (Vint 2) ⊢ False.
  Proof.
    iIntros "H".
    iDestruct (SimpleCPP.tptsto_welltyped with "H") as "[[%H _]|%H]".
    - iPureIntro. apply has_bool_type in H. lia.
    - discriminate.
  Qed.

  Lemma stored_pointer_valid ty cell q p :
    tptsto (Tptr ty) q cell (Vptr p) ⊢
    _valid_ptr pred.Relaxed p ∗ ⌜aligned_ptr_ty ty p⌝.
  Proof.
    iIntros "H". iDestruct (SimpleCPP.tptsto_welltyped with "H") as "[H|%H]".
    - iDestruct "H" as "#H". iEval (rewrite has_type_ptr') in "H".
      iDestruct "H" as "[V %Ha]". iFrame "V". done.
    - discriminate.
  Qed.
End concrete_model.
