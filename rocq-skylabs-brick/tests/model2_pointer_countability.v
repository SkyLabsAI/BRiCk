Require Import stdpp.gmap.
Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.model.inductive_pointers2.
Import inductive_pointers2.PTRS_IMPL.
Set Default Proof Using "Type*".

(** Finite maps distinguish absence of a pointer from a null pointer. *)
Lemma invalid_null_keys_distinct :
  let null := offset_ptr nullptr_ o_id in
  let cells : gmap ptr nat := <[null := 2%nat]> {[invalid_ptr_ := 1%nat]} in
  cells !! invalid_ptr_ = Some 1%nat /\ cells !! null = Some 2%nat.
Proof.
  cbn zeta. split.
  - rewrite lookup_insert_ne; [apply lookup_singleton_eq|discriminate].
  - apply lookup_insert_eq.
Qed.

(** Equal numeric addresses do not merge distinct allocations in a map. *)
Lemma allocation_provenance_keys_distinct aid1 aid2 va :
  aid1 <> aid2 ->
  let p1 := offset_ptr (alloc_ptr_ aid1 va) o_id in
  let p2 := offset_ptr (alloc_ptr_ aid2 va) o_id in
  let cells : gmap ptr nat := <[p2 := 2%nat]> {[p1 := 1%nat]} in
  cells !! p1 = Some 1%nat /\ cells !! p2 = Some 2%nat.
Proof.
  intros Hneq. cbn zeta. split.
  - rewrite lookup_insert_ne; first apply lookup_singleton_eq.
    intros Hsame. injection Hsame as Hsame. congruence.
  - apply lookup_insert_eq.
Qed.
