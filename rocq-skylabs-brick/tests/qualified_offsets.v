Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.notations.
Require Import skylabs.lang.cpp.code_notations.
Require Import skylabs.lang.cpp.model.inductive_pointers.
Import PTRS_IMPL.
Set Default Proof Using "Type*".
#[local] Open Scope Z_scope.

(** Top-level and nested qualifiers must identify the same subscript paths. *)
Lemma nested_qualifier_offset σ i :
  o_sub σ "const int* volatile"%cpp_type i = o_sub σ "int*"%cpp_type i.
Proof. rewrite -(o_sub_erase σ "const int* volatile"%cpp_type i). done. Qed.

Lemma mixed_qualifier_subscripts σ ty i j :
  o_sub σ (Tconst ty) i ,, o_sub σ (Tvolatile ty) j = o_sub σ ty (i + j).
Proof.
  rewrite -(o_sub_erase σ (Tconst ty) i)
    -(o_sub_erase σ (Tvolatile ty) j) /= o_dot_sub o_sub_erase.
  done.
Qed.

(** Erasure does not identify distinct unqualified element types. *)
Lemma distinct_integer_offsets σ :
  o_sub σ "int"%cpp_type 1 <> o_sub σ "unsigned int"%cpp_type 1.
Proof. discriminate. Qed.

(** Missing layouts still yield invalid offsets, including a zero index. *)
Lemma qualified_void_zero_offset σ :
  o_sub σ "const void"%cpp_type 0 = o_invalid σ.
Proof. done. Qed.
