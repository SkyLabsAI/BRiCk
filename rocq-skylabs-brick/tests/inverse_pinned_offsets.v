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

Set Printing Width 4611686018427387903.
Set Printing Fully Qualified.
Print Assumptions destination_only_inverse_refutable.
