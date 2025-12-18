(*
 * Copyright (C) 2020 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Export skylabs.prelude.base.
Require Export skylabs.iris.extra.algebra.base.

#[local] Definition resource' {SI : sidx} (A : Type) : cmra := exclR (leibnizO A).
#[global] Notation resource A := (Reduce (resource' A)) (only parsing).

(* Type-indexed wrappers, used in the restrict cmra below *)
Record wrapper (I A : Type) := Wrap { unwrap : A }.
Add Printing Constructor wrapper.
Arguments Wrap {I A} _.
Arguments unwrap {I A} _.
#[global] Instance wrapper_equiv I A `{Equiv A} : Equiv (wrapper I A) :=
  fun x y => x.(unwrap) ≡ y.(unwrap).
#[global] Instance Wrap_Proper I A `{Equiv A} : Proper (equiv ==> equiv) (@Wrap I A).
Proof. by move => x y h. Qed.
#[global] Instance unwrap_Proper I A `{Equiv A} : Proper (equiv ==> equiv) (@unwrap I A).
Proof. by move => x y h. Qed.
#[global] Instance wrapper_Equivalence {I : Type} `{Equiv A} `{X : @Equivalence _ (≡@{A})} :
  Equivalence (≡@{wrapper I A}).
Proof.
  case: X => h1 h2 h3; split.
  { case => x; apply: h1. }
  { by case => x; case => y h4; apply: h2. }
  case => x; case => y; case => z; apply: h3.
Qed.
Lemma Wrap_eq_iff I `{X : Equiv A} (a b : A) :
  @Wrap I A a ≡ @Wrap I A b <-> a ≡ b.
Proof.
  split.
  - by rewrite /equiv/wrapper_equiv.
  - by rewrite /equiv/wrapper_equiv.
Qed.
#[global] Instance wrapper_LeibnizEquiv {I : Type} `{Equiv A} `{X : @LeibnizEquiv _ (≡@{A})} :
  @LeibnizEquiv _ (≡@{wrapper I A}).
Proof.
  case => x; case => y h; f_equal; apply: X.
  by rewrite -Wrap_eq_iff.
Qed.
#[global] Instance Wrap_inj I `{X : Equiv A} : Inj (≡@{A}) (≡@{wrapper I A}) Wrap.
Proof. by move => x y; rewrite Wrap_eq_iff. Qed.
#[global] Instance unwrap_inj I `{Equiv A, !Equivalence (≡@{A})}
  : Inj (≡@{wrapper I A}) (≡@{A}) unwrap.
Proof. by case => x; case => y /= ->. Qed.

Section with_ofeT.
Context {I : Type} {SI : sidx} {A : ofe}.
Implicit Types x y : wrapper I A.

#[local] Instance wrapper_Dist : Dist (wrapper I A) :=
  fun n x y => x.(unwrap) ≡{n}≡ y.(unwrap).
Lemma wrapper_dist n x y : x ≡{n}≡ y <-> x.(unwrap) ≡{n}≡ y.(unwrap).
Proof. by []. Qed.
Lemma Wrap_dist_iff n (a b : A) : @Wrap I A a ≡{n}≡ @Wrap I A b <-> a ≡{n}≡ b.
Proof.
  split.
  - by rewrite /equiv/wrapper_dist.
  - by rewrite /equiv/wrapper_dist.
Qed.
Lemma wrapper_ofe_mixin : OfeMixin (wrapper I A).
Proof.
  constructor.
  - case => x; case => y; rewrite Wrap_eq_iff; split.
    { by move => h n; rewrite /dist/wrapper_Dist/= h. }
    rewrite /dist/wrapper_Dist/=.
    rewrite -mixin_equiv_dist => //. apply: ofe_mixin.
  - move => n; split => //.
    { rewrite /dist/wrapper_Dist/= => x //. }
    { rewrite /dist/wrapper_Dist/= => x y //. }
    { by rewrite /dist/wrapper_Dist/= => x y z // -> ->. }
  - move => n m [x] [y].
    rewrite /dist/wrapper_Dist/=.
    apply: mixin_dist_le. apply: ofe_mixin.
Qed.
Canonical Structure wrapperO := Ofe _ wrapper_ofe_mixin.
End with_ofeT.

Section ofe_properties.
  Context {I : Type} {SI : sidx} {A : ofe}.

  #[global] Instance Wrap_ne : NonExpansive (@Wrap I A).
  Proof. solve_proper. Qed.
  #[global] Instance unwrap_ne : NonExpansive (@unwrap I A).
  Proof. solve_proper. Qed.

  #[global] Instance Wrap_inj_dist n : Inj (dist n) (dist n) (@Wrap I A).
  Proof. by move=>a b. Qed.
  #[global] Instance unwrap_inj_dist n : Inj (dist n) (dist n) (@unwrap I A).
  Proof. by move=>a b. Qed.
End ofe_properties.

(* Restriction cmra (derived from @swasey's restrict.v)*)

(*jgs: The operational typeclass approach causes prefix_test to fail
(missing Valid instance). I don't yet understand why.
Class CmraRestrictor (I A : Type) : Type := restrict : A -> Prop.
Class Restriction I (A : cmra) `{CmraRestrictor I A} :=
{ cmra_restrict_ne n : Proper (dist n ==> impl) restrict
; cmra_restrict_op_l n (x y : wrapper I A) :
    ✓{n} (x ⋅ y).(unwrap) →
    restrict (x ⋅ y).(unwrap) →
    restrict x.(unwrap) }.*)
Class Restriction (I : Type) {SI : sidx} (A : cmra) :=
{ restrict : A -> Prop
; cmra_restrict_ne n : Proper (dist n ==> impl) restrict
; cmra_restrict_op_l n (x y : A) :
    ✓{n} (x ⋅ y) ->
    restrict (x ⋅ y) ->
    restrict x }.

#[global] Arguments Build_Restriction _ {_} _ _ _ _ : assert.

Section with_Restriction.
Variables (I : Type).
Context {SI : sidx}.
Variables (A : cmra).
Context `{R : !Restriction I A}.
Instance restrict_valid_def : Valid (wrapper I A) :=
  λ x, ✓ x.(unwrap) ∧ restrict x.(unwrap).
Instance restrict_validN_def : ValidN (wrapper I A) :=
  λ n x, ✓{n} x.(unwrap) ∧ restrict x.(unwrap).
Notation "✓{ n }@{ A } x" := (@validN _ _ (cmra_validN A) n x)
  (at level 20, n at next level, only parsing) : stdpp_scope.
Notation "✓@{ A } x" := (@valid _ (cmra_valid A) x)
  (at level 20, only parsing) : stdpp_scope.
Lemma restrict_valid (x : wrapper I A) :
  ✓ x ↔ ✓@{A} x.(unwrap) ∧ restrict x.(unwrap).
Proof. by done. Qed.
Lemma restrict_validN (n : SI) (x : wrapper I A) :
  ✓{n} x ↔ ✓{n}@{A} x.(unwrap) ∧ restrict x.(unwrap).
Proof. done. Qed.

#[local] Instance wrapper_PCore : PCore (wrapper I A) :=
  fun x => Wrap <$> pcore x.(unwrap).
Lemma wrapper_pcore x : pcore x = Wrap <$> pcore x.(unwrap).
Proof. by []. Qed.
#[local] Instance wrapper_Op : Op (wrapper I A) :=
  fun x y => Wrap $ x.(unwrap) ⋅ y.(unwrap).
Lemma wrapper_op x : op x = fun y => Wrap $ x.(unwrap) ⋅ y.(unwrap).
Proof. by []. Qed.

Definition restrict_cmra_mixin : CmraMixin (wrapper I A).
Proof.
  split.
  - case => x /=; rewrite wrapper_op => n a b h /=.
    by apply: cmra_op_ne.
  - move => n; case => x; case => y; case => cx.
    rewrite wrapper_dist /= => h1 h2.
    case: (cmra_pcore_ne _ _ _ cx h1).
    { move: h2; rewrite wrapper_pcore /=.
      case: (cmra_pcore A x) => // [a|].
      { by case: (pcore x) => //= z; inversion 1; subst. }
      by case: (pcore x) => //= z; inversion 1; subst. }
    move => cy []h3 h4; exists (Wrap cy); split => //.
    move: h2; rewrite wrapper_pcore /=; case: (pcore x) => // z.
    by inversion 1; subst; rewrite wrapper_pcore /= h3.
  - intros n x1 x2 Hx []. split.
    exact: cmra_validN_ne. exact: cmra_restrict_ne.
  - case => x. rewrite restrict_valid /= cmra_valid_validN.
    setoid_rewrite restrict_validN. naive_solver eauto using @sidx_zero.
  - move => n x [?] => /restrict_validN /= [??]. split. exact: cmra_validN_le. done.
  - case => x; case => y; case => z; apply: cmra_assoc.
  - case => x; case => y; apply: cmra_comm.
  - case => x; case => cx; rewrite /pcore/wrapper_PCore/= => h.
    rewrite /op/wrapper_Op/=; move: (cmra_pcore_l x cx); case: (pcore x) h => //.
    move => a; inversion 1; subst; move/(_ eq_refl) => h1.
    by rewrite Wrap_eq_iff.
  - case => x; case => cx; rewrite /pcore/wrapper_PCore/= // => -.
    move: (cmra_pcore_idemp x cx); case: (pcore x) => // a /= h1; inversion 1; subst.
    move: (h1 eq_refl); case: (pcore cx) => /=.
    { move => a h2. f_equiv. move/Some_equiv_eq: h2 => [?] [[-> ->]] //. }
    rewrite !option_equiv_Forall2; inversion 1.
  - case => x; case => y; case => cx.
    case; case => a; rewrite /op/wrapper_Op/=.
    rewrite /pcore/wrapper_PCore/= Wrap_eq_iff => h1 h2.
    case: (cmra_pcore_mono x y cx); first by exists a.
    { by move: h2; case: (pcore x) => // ax /=; inversion 1; subst. }
    move => a' []h3 h4; exists (Wrap a'); split => //.
    { move: h3; case: (pcore y) => // b'; inversion 1; subst => //. }
    case: h4 => b' h4; exists (Wrap b'); rewrite /op /= Wrap_eq_iff.
    by rewrite h4.
  - move => n; case => x; case => y [] /= h h1.
    rewrite restrict_validN; split => /=; first by apply: cmra_validN_op_l.
    move: h1.
    have ->: x = (@Wrap I A x).(unwrap) by [].
    have ->: y = (@Wrap I A y).(unwrap) by [].
    move => h1. apply: cmra_restrict_op_l => //=.
  - move => n; case => x; case => y1; case => y2 /=.
    rewrite /validN/restrict_validN_def /=; case => h1 h2.
    rewrite /op/wrapper_op /= /dist/wrapper_dist /= => h3.
    case: (mixin_cmra_extend _ (cmra_mixin A) n x y1 y2 h1 h3) => z1 []z2 [] h4 []h5 h6.
    exists (Wrap z1), (Wrap z2). split => //.
Qed.

Canonical Structure restrictR :=
  Cmra' _ (@wrapper_ofe_mixin I _ A) restrict_cmra_mixin.
End with_Restriction.

#[global] Instance wrapper_OfeDiscrete I `{X : OfeDiscrete A} : OfeDiscrete (@wrapperO I _ A).
Proof. by move => []x []y; rewrite wrapper_dist /=; move/(X _) => ->. Qed.

Section with_Restriction.
  Context {I : Type} `{rx : Restriction I A} {r : restrictR I A}.
  Implicit Types x y : A.
  Implicit Types a b : restrictR I A.

  #[global] Instance restrict_CmraDiscrete {X : CmraDiscrete A} :
    CmraDiscrete (restrictR I A).
  Proof.
    case: X => h1 h2; constructor; first by apply: wrapper_OfeDiscrete.
    move => []x; rewrite restrict_validN /= => [][]h3 h4.
    by rewrite restrict_valid; split => //=; apply: h2.
  Qed.

  (** Updates *)
  Lemma restrict_update x y :
    (∀ mf, restrict (x ⋅? mf) → restrict (y ⋅? mf)) →
    x ~~> y → Wrap x ~~> Wrap y.
  Proof.
    move=>HP Hup n mz [X Y]. split.
    { case: mz X Y => //=.
      { move => a h1 h2; apply: (Hup n (Some $ unwrap a) h1). }
      by move => h1 h2; move: (HP None h2) => /= h3; apply: (Hup n None h1). }
    case: mz X Y => /=.
    { move => a h1 h2; move: (Hup n (Some $ unwrap a) h1) => h3.
      by apply: (HP (Some $ unwrap a)). }
    move => h1 h2; apply: (HP None h2).
  Qed.

  (** Local updates *)
  Lemma restrict_local_update x y x' y' :
    (restrict x → restrict x') →
    (x, y) ~l~> (x', y') → (Wrap x, Wrap y) ~l~> (Wrap x', Wrap y').
  Proof.
    move=>X Hup n mf /= [Y Z] Hx; split.
    { rewrite restrict_validN; split => /=; last by apply: X.
      case: mf Hx; first by move => a /= Hx; case: (Hup n (Some $ unwrap a)).
      by rewrite /= => h1; case: (Hup n None). }
    case: mf Hx; first by move => a /= Hx; case: (Hup n (Some $ unwrap a)).
    by rewrite /= => h1; case: (Hup n None).
  Qed.
End with_Restriction.
