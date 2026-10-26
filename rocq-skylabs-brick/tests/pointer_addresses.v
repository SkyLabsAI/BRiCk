Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.notations.
Require Import skylabs.lang.cpp.code_notations.
Require Import skylabs.lang.cpp.semantics.genv.
Require Import skylabs.lang.cpp.semantics.types.
Require Import skylabs.lang.cpp.model.inductive_pointers.
Import PTRS_IMPL.
Set Default Proof Using "Type*".

Section addresses.
  Context {σ : genv}.

  Lemma positive_subscript_address aid :
    ptr_vaddr (alloc_ptr aid 8 ,, o_sub σ "unsigned char"%cpp_type 2) = Some 10%N.
  Proof. rewrite _dot.unlock /DOT_dot /=. reflexivity. Qed.

  Lemma negative_subscript_address aid :
    ptr_vaddr (alloc_ptr aid 8 ,, o_sub σ "unsigned char"%cpp_type (-2)) = Some 6%N.
  Proof. rewrite _dot.unlock /DOT_dot /=. reflexivity. Qed.

  Lemma subscript_underflow aid :
    ptr_vaddr (alloc_ptr aid 8 ,, o_sub σ "unsigned char"%cpp_type (-9)) = None.
  Proof. rewrite _dot.unlock /DOT_dot /=. reflexivity. Qed.

  (** Preserve the existing per-segment underflow checks on the stored path. *)
  Lemma intermediate_underflow aid :
    ptr_vaddr (alloc_ptr aid 8 ,, o_sub σ "signed char"%cpp_type 9
      ,, o_sub σ "unsigned char"%cpp_type (-9)) = None.
  Proof. rewrite _dot.unlock /DOT_dot /=. reflexivity. Qed.

  Lemma missing_layout_no_address p ty i :
    size_of σ ty = None -> ptr_vaddr (p ,, o_sub σ ty i) = None.
  Proof.
    intros Hsz. destruct (ptr_vaddr (p ,, o_sub σ ty i)) as [va|] eqn:E; last done.
    exfalso. have Hp := ptr_vaddr_defined σ _ (ex_intro _ va E).
    apply (ptr_offset_defined_dot σ) in Hp as [_ Hsub].
    have [sz Hsz'] := eval_o_sub_defined σ ty i Hsub. congruence.
  Qed.

  (** An invalid prefix cannot recover an address by discarding later offsets. *)
  Lemma missing_layout_prefix_no_address (p : ptr) ty i (o : offset) :
    size_of σ ty = None -> ptr_vaddr (p ,, o_sub σ ty i ,, o) = None.
  Proof.
    intros Hsz. destruct (ptr_vaddr (p ,, o_sub σ ty i ,, o)) as [va|] eqn:E;
      last done.
    exfalso. have Hp := ptr_vaddr_defined σ _ (ex_intro _ va E).
    apply (ptr_offset_defined_dot σ) in Hp as [Hp _].
    apply (ptr_offset_defined_dot σ) in Hp as [_ Hsub].
    have [sz Hsz'] := eval_o_sub_defined σ ty i Hsub. congruence.
  Qed.

  (** The positive-size premise of address injectivity is necessary. *)
  Lemma zero_sized_subscripts_share_address aid :
    ptr_vaddr (alloc_ptr aid 8 ,, o_sub σ "unsigned char[0]"%cpp_type 1) = Some 8%N /\
    ptr_vaddr (alloc_ptr aid 8 ,, o_sub σ "unsigned char[0]"%cpp_type 2) = Some 8%N.
  Proof. rewrite _dot.unlock /DOT_dot /=. split; reflexivity. Qed.
End addresses.
