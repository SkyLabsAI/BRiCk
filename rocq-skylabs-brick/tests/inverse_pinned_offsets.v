Require Import skylabs.lang.cpp.logic.pred.
Require Import skylabs.lang.cpp.semantics.genv.
Require Import skylabs.lang.cpp.semantics.values.
Require Import skylabs.lang.cpp.semantics.types.
Require Import skylabs.lang.cpp.notations.
Require Import skylabs.lang.cpp.code_notations.
Require Import skylabs.iris.extra.proofmode.proofmode.
Set Default Proof Using "Type*".

Section core.
  Context `{cpp_logic} {σ : genv}.

  (* The real public rule must not inhabit the old destination-only contract.
     Restoring that contract would make this command unexpectedly succeed. *)
  Fail Definition destination_only_inverse : forall o z va p,
    eval_offset σ o = Some z ->
    ptr_vaddr (p ,, o) = Some va ->
    valid_ptr (p ,, o) |--
      [| (0 <= Z.of_N va - z)%Z |] **
      [| ptr_vaddr p = Some (Z.to_N (Z.of_N va - z)) |] :=
    offset_inv_pinned_ptr_pure.

  Example source_valid_inverse o z va p :
    eval_offset σ o = Some z ->
    ptr_vaddr (p ,, o) = Some va ->
    valid_ptr p |--
      [| (0 <= Z.of_N va - z)%Z |] **
      [| ptr_vaddr p = Some (Z.to_N (Z.of_N va - z)) |].
  Proof. apply offset_inv_pinned_ptr_pure. Qed.

  (** The old destination-only contract would make the core logic inconsistent.
      It is a local hypothesis here, never an axiom of the regression. *)
  Lemma destination_only_inverse_refutable
      (old_inverse : forall o z va p,
        eval_offset σ o = Some z ->
        ptr_vaddr (p ,, o) = Some va ->
        valid_ptr (p ,, o) |--
          [| (0 <= Z.of_N va - z)%Z |] **
          [| ptr_vaddr p = Some (Z.to_N (Z.of_N va - z)) |]) :
    |-- (False : mpred).
  Proof.
    have Hsize : is_Some (size_of σ "unsigned char"%cpp_type) by eexists.
    have Hcancel :
      (nullptr ,, o_sub σ "unsigned char"%cpp_type (-1)) ,,
        o_sub σ "unsigned char"%cpp_type 1 = nullptr.
    { by rewrite -offset_ptr_dot o_dot_sub /= (o_sub_0 _ Hsize) offset_ptr_id. }
    have Heval : eval_offset σ (o_sub σ "unsigned char"%cpp_type 1) = Some 1%Z.
    { by rewrite (eval_o_sub' (σ:=σ) (ty:="unsigned char"%cpp_type) 1 eq_refl). }
    have Haddr : ptr_vaddr ((nullptr ,, o_sub σ "unsigned char"%cpp_type (-1)) ,,
        o_sub σ "unsigned char"%cpp_type 1) = Some 0%N.
    { by rewrite Hcancel ptr_vaddr_nullptr. }
    iDestruct (old_inverse _ _ _ _ Heval Haddr with "[]") as %[Hbad _].
    { rewrite Hcancel. iApply valid_ptr_nullptr. }
    lia.
  Qed.
End core.

Require Import skylabs.lang.cpp.logic.operator.

Section alignment_without_validity.
  Context `{cpp_logic} {σ : genv}.

  (* Address alignment is preserved even when the result cannot be valid. *)
  Example null_offset_aligned (n : Z) :
    |-- ([| aligned_ptr_ty "unsigned char"%cpp_type
              (nullptr ,, o_sub σ "unsigned char"%cpp_type n) |] : mpred).
  Proof.
    have Hsize : is_Some (size_of σ "unsigned char"%cpp_type) by eexists.
    iApply (aligned_ptr_ty_sub nullptr n "unsigned char"%cpp_type Hsize).
    iSplit; last by iApply valid_ptr_nullptr.
    iPureIntro.
    destruct Hsize as [sz Hsz].
    destruct (align_of_size_of_some _ _ Hsz) as (al & Hal & _).
    exists al. split; first done.
    left. exists 0%N. split; first exact ptr_vaddr_nullptr.
    apply N.divide_0_r.
  Qed.

  Example null_offset_invalid (n : Z) (Hn : n <> 0) :
    valid_ptr (nullptr ,, o_sub σ "unsigned char"%cpp_type n) |-- False.
  Proof. by apply _valid_ptr_nullptr_sub_false. Qed.
End alignment_without_validity.
