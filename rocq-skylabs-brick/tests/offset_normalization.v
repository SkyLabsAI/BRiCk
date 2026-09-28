Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.semantics.genv.
Require Import skylabs.lang.cpp.semantics.types.
Require Import skylabs.lang.cpp.model.inductive_pointers2.
Import PTRS_IMPL.
Set Default Proof Using "Type*".
#[local] Open Scope Z_scope.

(** A redex at the head and one below a field both prevent canonicality. *)
Lemma zero_subscript_not_canonical ty : ~ roff_canon [o_sub_ ty 0].
Proof.
  intros H. apply roff_canon_cons in H as [H _]. apply H with
    (s := [o_sub_ ty 0]) (t := []) (r := []); [done|constructor].
Qed.

Lemma trailing_redex_not_canonical f ty :
  ~ roff_canon [o_field_ f; o_sub_ ty 0].
Proof.
  intros H. apply (zero_subscript_not_canonical ty).
  exact (proj2 (proj1 (roff_canon_cons _ _) H)).
Qed.

Lemma merging_subscripts ty :
  normalize [o_sub_ ty 1; o_sub_ ty 2] = [o_sub_ ty 3].
Proof.
  apply norm_complete.
  - apply rtc_once. exists [], [], [o_sub_ ty 1; o_sub_ ty 2], [o_sub_ ty 3].
    split; first done. split; first done.
    change (roff_rw_local [o_sub_ ty 1; o_sub_ ty 2] [o_sub_ ty (1+2)]).
    constructor.
  - apply singleton_offset_canon. intros [ty' H]. discriminate H.
Qed.

Set Printing Fully Qualified.
Print Assumptions PTRS_IMPL.canon_syn_sem_eqv.
Print Assumptions PTRS_IMPL.find_redex_pass.
Print Assumptions PTRS_IMPL.norm_canon.
Print Assumptions PTRS_IMPL.offset_countable.
Print Assumptions PTRS_IMPL.ptr_vaddr_resp_leq.
Print Assumptions zero_subscript_not_canonical.
Print Assumptions trailing_redex_not_canonical.
Print Assumptions merging_subscripts.

Fail Check skylabs.lang.cpp.model.inductive_pointers2.irr.
Print Assumptions PTRS_IMPL.roff_canon_proof_irrel.
Print Assumptions PTRS_IMPL.offset_eq_dec.
