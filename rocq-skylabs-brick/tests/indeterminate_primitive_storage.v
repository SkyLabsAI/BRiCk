Require Import iris.bi.monpred.
Require Import iris.base_logic.lib.iprop.
Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.semantics.genv.
Require Import skylabs.lang.cpp.algebra.cfrac.
Require Import skylabs.lang.cpp.model.inductive_pointers.
Require Import skylabs.lang.cpp.model.simple_pred.
Require Import skylabs.iris.extra.proofmode.proofmode.
Import PTRS_IMPL VALUES_DEFS_IMPL SimpleCPP.
Set Default Proof Using "Type*".

Section encoding.
  Context {σ : genv}.

  Definition pointer_poison : list runtime_val :=
    repeat Rundef (bitsize.bytesNat (pointer_size_bitsize σ)).

  Lemma indeterminate_bool_encoding vs :
    pure_encodes Tbool Vundef vs <-> vs = [Rundef].
  Proof. done. Qed.

  Lemma indeterminate_pointer_encoding ty vs :
    pure_encodes (Tptr ty) Vundef vs <-> vs = pointer_poison.
  Proof. done. Qed.

  Lemma indeterminate_nullptr_encoding vs :
    pure_encodes Tnullptr Vundef vs <-> vs = pointer_poison.
  Proof. done. Qed.

  Lemma initialized_bool_encoding b :
    pure_encodes Tbool (Vbool b) [Rval (if b then 1%N else 0%N)].
  Proof. by destruct b. Qed.

  Lemma initialized_null_encoding ty :
    pure_encodes (Tptr ty) (Vptr nullptr) (cptr 0) /\
    pure_encodes Tnullptr (Vptr nullptr) (cptr 0).
  Proof. rewrite /pure_encodes /=. done. Qed.

  Lemma poison_bool_not_zero : ~ pure_encodes Tbool Vundef [Rval 0%N].
  Proof. discriminate. Qed.

  Lemma poison_pointer_not_null ty :
    ~ pure_encodes (Tptr ty) Vundef (cptr 0).
  Proof. exact: pure_encodes_undef_Z_to_bytes. Qed.

  Lemma poison_nullptr_not_null : ~ pure_encodes Tnullptr Vundef (cptr 0).
  Proof. exact: pure_encodes_undef_Z_to_bytes. Qed.
End encoding.

Section concrete_model.
  Context {thread_info : biIndex} {Σ : gFunctors}
    {Hlogic : SimpleCPP.cpp_logic thread_info Σ}.
  #[local] Existing Instance Hlogic.
  Context {σ : genv}.

  (** Construction from physical resources, without a points-to premise. *)
  Lemma physical_indeterminate_bool p q a :
    type_ptr Tbool p ∗ mem_inj_own p (Some a) ∗
    bytes a [Rundef] q ∗ vbytes a [Rundef] q ⊢
    tptsto Tbool q p Vundef.
  Proof.
    iIntros "(T & M & B & V)".
    iApply (tptsto_physical_intro Tbool q p Vundef a [Rundef]); first done.
    iFrame. iSplit; first done. by iRight.
  Qed.

  Lemma physical_indeterminate_pointer ty p q a :
    type_ptr (Tptr (erase_qualifiers ty)) p ∗ mem_inj_own p (Some a) ∗
    bytes a pointer_poison q ∗ vbytes a pointer_poison q ⊢
    tptsto (Tptr (erase_qualifiers ty)) q p Vundef.
  Proof.
    iIntros "(T & M & B & V)".
    iApply (tptsto_physical_intro (Tptr (erase_qualifiers ty)) q p Vundef a pointer_poison).
    { rewrite /is_heap_type /= erase_qualifiers_idemp bool_decide_true; done. }
    iFrame. iSplit; first done. by iRight.
  Qed.

  Lemma physical_indeterminate_nullptr p q a :
    type_ptr Tnullptr p ∗ mem_inj_own p (Some a) ∗
    bytes a pointer_poison q ∗ vbytes a pointer_poison q ⊢
    tptsto Tnullptr q p Vundef.
  Proof.
    iIntros "(T & M & B & V)".
    iApply (tptsto_physical_intro Tnullptr q p Vundef a pointer_poison); first done.
    iFrame. iSplit; first done. by iRight.
  Qed.
End concrete_model.
