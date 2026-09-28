Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.semantics.genv.
Require Import skylabs.lang.cpp.semantics.types.
Require Import skylabs.lang.cpp.model.simple_pointers_utils.
Require Import skylabs.lang.cpp.model.inductive_pointers.
Import PTRS_IMPL.
Set Default Proof Using "Type*".
#[local] Open Scope Z_scope.

(** Two levels of inheritance cancel from the inside out, in either direction. *)
Lemma nested_base_derived derived middle base z1 z2 :
  raw_offset_collapse
    [(o_base_ derived middle, z1); (o_base_ middle base, z2);
     (o_derived_ base middle, -z2); (o_derived_ middle derived, -z1)] = [].
Proof.
  rewrite /raw_offset_collapse /= /offset_seg_cons /=.
  repeat (rewrite decide_True; last by split_and!; [..|lia]).
  done.
Qed.

Lemma nested_derived_base derived middle base z1 z2 :
  raw_offset_collapse
    [(o_derived_ base middle, -z2); (o_derived_ middle derived, -z1);
     (o_base_ derived middle, z1); (o_base_ middle base, z2)] = [].
Proof.
  rewrite /raw_offset_collapse /= /offset_seg_cons /=.
  repeat (rewrite decide_True; last by split_and!; [..|lia]).
  done.
Qed.

(** Equal displacements alone cannot identify a base or derived class. *)
Lemma mismatched_base_names derived base1 base2 z :
  base1 <> base2 ->
  raw_offset_collapse [(o_base_ derived base1, z); (o_derived_ base2 derived, -z)] =
    [(o_base_ derived base1, z); (o_derived_ base2 derived, -z)].
Proof.
  intros Hneq. rewrite /raw_offset_collapse /= /offset_seg_cons /=.
  rewrite decide_False; naive_solver.
Qed.

Lemma mismatched_derived_names derived1 derived2 base z :
  derived1 <> derived2 ->
  raw_offset_collapse [(o_base_ derived1 base, z); (o_derived_ base derived2, -z)] =
    [(o_base_ derived1 base, z); (o_derived_ base derived2, -z)].
Proof.
  intros Hneq. rewrite /raw_offset_collapse /= /offset_seg_cons /=.
  rewrite decide_False; naive_solver.
Qed.

(** Stored offsets can come from different layouts; matching names do not
    justify discarding a nonzero net displacement. *)
Lemma mismatched_displacements derived base z1 z2 :
  z1 + z2 <> 0 ->
  raw_offset_collapse [(o_base_ derived base, z1); (o_derived_ base derived, z2)] =
    [(o_base_ derived base, z1); (o_derived_ base derived, z2)] /\
  raw_offset_collapse [(o_derived_ base derived, z1); (o_base_ derived base, z2)] =
    [(o_derived_ base derived, z1); (o_base_ derived base, z2)].
Proof.
  intros Hneq. rewrite /raw_offset_collapse /= /offset_seg_cons /=.
  rewrite !decide_False; naive_solver.
Qed.

Lemma intervening_field derived base f z :
  raw_offset_collapse
    [(o_base_ derived base, z); (o_field_ f, 0); (o_derived_ base derived, -z)] =
    [(o_base_ derived base, z); (o_field_ f, 0); (o_derived_ base derived, -z)].
Proof. reflexivity. Qed.

(** Absent inheritance metadata must not become an addressable identity path. *)
Lemma missing_parent_no_address (σ : genv) (p : ptr) derived base :
  parent_offset σ derived base = None ->
  @ptr_vaddr σ (p ,, o_base σ derived base ,, o_derived σ base derived) = None.
Proof.
  intros Hparent.
  destruct (ptr_vaddr (p ,, o_base σ derived base ,, o_derived σ base derived))
    as [va|] eqn:E; last done.
  exfalso. have Hp := ptr_vaddr_defined σ _ (ex_intro _ va E).
  apply (ptr_offset_defined_dot σ) in Hp as [Hp _].
  apply (ptr_offset_defined_dot σ) in Hp as [_ Hbase].
  move: Hbase.
  rewrite /eval_offset /eval_raw_offset /= /mk_offset_seg /= /o_base_off Hparent /=.
  change (is_Some (@None Z) -> False). naive_solver.
Qed.

(** The reviewed pointer principle holds for every pointer, including complete
    objects: a downcast followed by its matching upcast is the identity. *)
Lemma derived_base_pointer_roundtrip (σ : genv) (p : ptr) base derived z :
  parent_offset σ derived base = Some z ->
  p ,, o_derived σ base derived ,, o_base σ derived base = p.
Proof.
  intros Hparent. apply o_derived_base. by exists z.
Qed.

(** Missing inheritance metadata also stays undefined in the reverse direction. *)
Lemma missing_parent_reverse_no_address (σ : genv) (p : ptr) derived base :
  parent_offset σ derived base = None ->
  @ptr_vaddr σ (p ,, o_derived σ base derived ,, o_base σ derived base) = None.
Proof.
  intros Hparent.
  destruct (ptr_vaddr (p ,, o_derived σ base derived ,, o_base σ derived base))
    as [va|] eqn:E; last done.
  exfalso. have Hp := ptr_vaddr_defined σ _ (ex_intro _ va E).
  apply (ptr_offset_defined_dot σ) in Hp as [Hp _].
  apply (ptr_offset_defined_dot σ) in Hp as [_ Hderived].
  move: Hderived.
  rewrite /eval_offset /eval_raw_offset /= /mk_offset_seg /= /o_derived_off Hparent /=.
  change (is_Some (@None Z) -> False). naive_solver.
Qed.
