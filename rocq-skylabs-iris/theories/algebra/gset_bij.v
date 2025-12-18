(*
 * Copyright (c) 2021 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Export iris.algebra.lib.gset_bij.
Require Import iris.algebra.proofmode_classes.
Require Import skylabs.prelude.base.

(** TODO: Upstream to [iris.algebra.lib.gset_bij].

Note: One might want to use this construction with types [A], [B]
equipped with an interesting setoid equality. In that case, we'd need
[Proper] and [Params] instances. *)
Section gset_bij.
  Context {SI : sidx} `{Countable A, Countable B}.
  Implicit Types (a : A) (b : B) (L : gset (A * B)).

  (** Useful corollary to [gset_bij_auth_extend] that also produces
      the new element. *)
  Lemma gset_bij_update_alloc {L} a b :
    (∀ b', (a, b') ∉ L) → (∀ a', (a', b) ∉ L) →
    gset_bij_auth (DfracOwn 1) L ~~> gset_bij_auth (DfracOwn 1) ({[(a, b)]} ∪ L) ⋅ gset_bij_elem a b.
  Proof.
    intros. etrans; first exact: gset_bij_auth_extend.
    rewrite {1}(core_id_extract (gset_bij_elem _ _) (gset_bij_auth _ _))//.
    apply bij_view_included. set_solver+.
  Qed.

  (** Proof mode *)
  #[global] Instance gset_bij_auth_is_op q q1 q2 L :
    IsOp q q1 q2 ->
    IsOp' (gset_bij_auth q L) (gset_bij_auth q1 L) (gset_bij_auth q2 L).
  Proof. by rewrite /IsOp' /IsOp gset_bij_auth_dfrac_op=>->. Qed.

End gset_bij.
#[global] Hint Opaque gset_bij_auth gset_bij_elem : typeclass_instances.
