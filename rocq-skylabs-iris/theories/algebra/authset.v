(*
 * Copyright (C) 2021 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Export stdpp.propset.

Require Export skylabs.iris.extra.algebra.base.
Require Import skylabs.iris.extra.algebra.restrict.

Set Default Proof Using "Type".

(** * CMRA: Auth/frag splits on sets, with strengthening

  This CMRA exposes:
    * AuthSet.frag (s : propset A)
    * AuthSet.auth (s : propset A)
  such that
    * ✓ (AuthSet.frag s1 ⋅ AuthSet.auth s2) <-> s1 ⊆ s2; and
    * AuthSet.frag s ~~> AuthSet.frag s' when s' ⊆ s (removing elements
      from a frag set is frame preserving).
  The CMRA is built using the `restrict.v` framework.
  This CMRA is used in ``lang/base_logic/lib/auth_set.v``.
*)

Canonical Structure propsetO {SI : sidx} (A : Type) : ofe := discreteO (propset A).

Notation _auth_setT A :=
  (prodR (optionR (exclR (propsetO A))) (optionR (exclR (propsetO A))))
  (only parsing).
Variant AuthSet : Prop :=.
#[local] Definition auth_set' {SI : sidx} (A : Type) :=
  wrapper AuthSet (_auth_setT A).
Notation auth_set A := (Reduce (auth_set' A)) (only parsing).

Section with_Type.
  Context {SI : sidx} `{A : Type, Countable A}.
  Implicit Types x y : _auth_setT A.
  Definition auth_set_Restrictor x :=
    forall s1 s2, fst x ≡ Excl' s1 -> snd x ≡ Excl' s2 -> s1 ⊆ s2.

  #[local] Lemma auth_set_cmra_restrict_ne n :
    Proper (dist n ==> impl) auth_set_Restrictor.
  Proof.
    case => a b; case => c d; case => /=; rewrite -2!discrete_iff => h1 h2.
      by move => h3 l1 l; rewrite -h1 -h2 => x y; apply: h3.
  Qed.
  #[local] Lemma auth_set_cmra_restrict_op_l n (x y : _auth_setT A) :
    ✓{n} (x ⋅ y) ->
    auth_set_Restrictor (x ⋅ y) → auth_set_Restrictor x.
  Proof.
    case: x => a b; case: y => c d /=; case => /= x y h1 l1 l /=.
    move => h2 h3; apply: h1; first by move: x; rewrite h2; case: c.
      by move: y; rewrite h3; case: d.
  Qed.

  #[global] Instance auth_set_Restriction :
    Restriction AuthSet (_auth_setT A) :=
    {| restrict := auth_set_Restrictor;
      cmra_restrict_ne := auth_set_cmra_restrict_ne;
      cmra_restrict_op_l := auth_set_cmra_restrict_op_l |}.
End with_Type.

Canonical Structure auth_setR {SI : sidx} (A : Type) :=
  restrictR AuthSet (_auth_setT A).

Module AuthSet.
  Definition frag_def {SI : sidx} {A} (s1 : propset A) : auth_set A :=
    Wrap (Excl' s1, None).
  Definition frag_aux : seal (@frag_def). Proof. by eexists. Qed.
  Definition frag := frag_aux.(unseal).
  Definition frag_eq : @frag = _ := frag_aux.(seal_eq).

  Arguments frag {_ _} _.

  Definition auth_def {SI : sidx} {A} (s2 : propset A) : auth_set A :=
    Wrap (None, Excl' s2).
  Definition auth_aux : seal (@auth_def). Proof. by eexists. Qed.
  Definition auth := auth_aux.(unseal).
  Definition auth_eq : @auth = _ := auth_aux.(seal_eq).

  Arguments auth {_ _} _.
End AuthSet.

Section Lemmas.
  Context {SI : sidx}.

  Lemma auth_set_validN_valid {A} n (x : auth_setR A) : ✓{n} x <-> ✓x.
  Proof. by rewrite restrict_validN restrict_valid. Qed.

  Lemma auth_set_valid_frag {A} (s1 : propset A) : ✓ AuthSet.frag s1.
  Proof.
    rewrite AuthSet.frag_eq restrict_valid; split => //.
    move => s1' l /=. do 2 inversion 1.
  Qed.

  Lemma auth_set_valid_auth {A} (l : propset A) : ✓ AuthSet.auth l.
  Proof.
    rewrite AuthSet.auth_eq restrict_valid; split => //.
    move => s1 l' /=. do 2 inversion 1.
  Qed.

  Lemma auth_set_auth_excl {A} (s1 s2 : propset A) :
    ~ ✓ (AuthSet.auth s1 ⋅ AuthSet.auth s2).
  Proof.
    rewrite AuthSet.auth_eq restrict_valid => []/=[]/=.
    inversion 1; simpl in *.
    match goal with H : ✓ (Excl' _ ⋅ Excl' _) |- _ => inversion H end.
  Qed.

  Lemma auth_set_frag_excl {A} (s1 s2 : propset A) :
    ~ ✓ (AuthSet.frag s1 ⋅ AuthSet.frag s2).
  Proof.
    rewrite AuthSet.frag_eq restrict_valid => []/=[]/=.
    inversion 1; simpl in *.
    match goal with H : ✓ (Excl' _ ⋅ Excl' _) |- _ => inversion H end.
  Qed.

  Lemma auth_set_valid_frag_auth {A} (s1 s2 : propset A) :
    ✓ (AuthSet.frag s1 ⋅ AuthSet.auth s2) <-> s1 ⊆ s2.
  Proof.
    rewrite AuthSet.frag_eq AuthSet.auth_eq; split.
    { by rewrite restrict_valid; case => /=; case => /= _ _; apply. }
    move => h; rewrite restrict_valid; split => // s1' l' /=.
    inversion 1. inversion 1. subst. inversion H2; subst. inversion H6; subst.
      by rewrite <-H4, <-H5.
  Qed.

  (** ** Removing elements from a frag set is frame preserving. *)
  Lemma auth_set_update_frag {A} (s' s : propset A) (_ : s' ⊆ s):
    AuthSet.frag s ~~> AuthSet.frag s'.
  Proof.
    move => n; case => x /=; last by apply: auth_set_valid_frag.
    case: x; case => a b; rewrite restrict_validN /=; case.
    rewrite AuthSet.frag_eq /=; case: a => //= X Y; split.
    { split => //=; rewrite /op/cmra_op/=; destruct b => //.
      rewrite Some_validN.
      by rewrite /valid/cmra_valid/=; case: X => /=; case: c Y. }
    simpl => x y /=. inversion 1. inversion 1. subst.
    have h2: b ≡ Excl' y.
    { clear X Y; case: b H4 H5; last by inversion 1.
      move => a; inversion 1; subst. inversion 1; subst. by rewrite H5. }
    have H2: s ⊆ y by apply: Y.
    inversion H3; subst. rewrite <-H8. clear - H H2. set_solver.
  Qed.

  Lemma auth_set_update {A} (s1' l' s1 l : propset A) (_ : s1' ⊆ l') :
    AuthSet.frag s1 ⋅ AuthSet.auth l ~~>
    AuthSet.frag s1' ⋅ AuthSet.auth l'.
  Proof.
    move => n; case => x /=; last first.
    { by rewrite -cmra_discrete_valid_iff auth_set_valid_frag_auth. }
    case: x => [][]a b.
    rewrite restrict_validN; case.
    rewrite AuthSet.auth_eq AuthSet.frag_eq /=; case => /= h1 h2.
    have ->: a = None by case: a h1.
    have ->: b = None by case: b h2. move => h3.
    rewrite /AuthSet.frag_def /AuthSet.auth_def restrict_validN /=.
    split => // lx ly /=. inversion 1; subst. inversion 1; subst.
    inversion H3; subst.
    inversion H5; subst. rewrite -H6 -H7. apply: H.
  Qed.

  #[global] Instance frag_proper {A} : Proper (equiv ==> equiv) (AuthSet.frag (A:=A)).
  Proof.
    move => x y E; rewrite AuthSet.frag_eq/AuthSet.frag_def.
    apply: Wrap_Proper; apply: pair_proper; last by [].
    apply: Some_proper; apply: Excl_proper; apply: E.
  Qed.

  #[global] Instance auth_proper {A} : Proper (equiv ==> equiv) (AuthSet.auth (A:=A)).
  Proof.
    move => x y E; rewrite AuthSet.auth_eq/AuthSet.auth_def.
    apply: Wrap_Proper; apply: pair_proper; first by [].
    apply: Some_proper; apply: Excl_proper; apply: E.
  Qed.

  #[local] Lemma auth_set_test :
    ✓ (AuthSet.frag {[ 1%N ]} ⋅ AuthSet.auth ({[ 1%N ]} ∪ {[ 2%N ]})).
  Proof.
    rewrite auth_set_valid_frag_auth.
    set_solver.
  Succeed Qed. Abort. (*NOTE: to avoid polluting search, or is #[local] enough?*)
End Lemmas.
