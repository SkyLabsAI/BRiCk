Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.semantics.
Require Import skylabs.lang.cpp.logic.pred.
Require Import skylabs.lang.cpp.logic.heap_pred.
Require Import skylabs.iris.extra.proofmode.proofmode.
Set Default Proof Using "Type*".
Implicit Types (p : ptr) (ty : type).

Section with_cpp.
  Context `{Σ : cpp_logic} {σ : genv}.

  Lemma void_pointer_validity p : has_type (Vptr p) "void*"%cpp_type -|- valid_ptr p.
  Proof.
    rewrite has_type_ptr'.
    iSplit; first iIntros "[$ _]".
    iIntros "$ !%". apply aligned_ptr_ty_void.
  Qed.

  Lemma function_pointer_validity ft p :
    has_type (Vptr p) (Tptr (Tfunction ft)) -|- valid_ptr p.
  Proof.
    rewrite has_type_ptr'.
    iSplit; first iIntros "[$ _]".
    iIntros "$ !%". apply aligned_ptr_ty_function.
  Qed.

  Lemma sized_pointer_object_alignment ty sz p :
    size_of σ ty = Some sz ->
    has_type (Vptr p) (Tptr ty) |-- [| aligned_ptr_ty ty p |].
  Proof. intros _. rewrite has_type_ptr'. iIntros "[_ $]". Qed.

  Lemma function_pointer_storage_alignment ft p :
    reference_to (Tptr (Tfunction ft)) p |-- p |-> aligned_ofR (Tptr (Tfunction ft)).
  Proof.
    rewrite reference_to_elim aligned_ofR_aligned_ptr_ty. iIntros "[$ _]".
  Qed.

  Lemma function_reference_from_validity ft p :
    strict_valid_ptr p |-- reference_to (Tfunction ft) p.
  Proof.
    iIntros "#V". iApply reference_to_intro; first iExact "V".
    rewrite function_pointer_validity. by iApply strict_valid_valid.
  Qed.

  Lemma void_reference_alignment p :
    Observe (p |-> aligned_ofR "void"%cpp_type) (reference_to "void"%cpp_type p).
  Proof. apply _. Qed.

  Lemma function_reference_alignment ft p :
    Observe (p |-> aligned_ofR (Tfunction ft)) (reference_to (Tfunction ft) p).
  Proof. apply _. Qed.
End with_cpp.
