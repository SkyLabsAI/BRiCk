(*
 * Copyright (c) 2022 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import iris.algebra.cmra.
Require Import iris.algebra.frac.
Require Import bluerock.prelude.bool.
Require Import bluerock.iris.extra.bi.split_frac.

#[local] Set Printing Coercions.

(** * Const/mutable fractions *)
(**
Overview:

- Type [cQp.t] pairs together a positive fraction [cQp.frac] with a
bit [cQp.is_const] tracking whether any C++ state governed by that
fraction is constant or mutable

- [cQp.mut] (short name [cQp.m]), [cQp.const] ([cQp.c]) inject
fractions into [cQp.t]

- [cQp.add] combines two const/mutable fractions using [&&] on the
booleans and [+] on the fractions

- [cQp.scale q] scales the fraction in a const/mutable fraction by
fraction [q]

- Canonical OFE, CMRA structures for [cQp.t]

- Module [cQp_compat] exports a coercion [cQp._mut : Qp >-> cQp.t]

Note: We extend the effects of [Import cQp_compat] in
../bi/cfractional.v. Import order matters.
*)

Declare Scope cQp_scope.
Delimit Scope cQp_scope with cQp.

Module cQp.

  #[projections(primitive)]
  Record t : Set := mk { is_const : bool ; frac : Qp }.
  #[global] Hint Opaque is_const frac : typeclass_instances.

  Notation mut := (mk false).
  Notation m := (mk false) (only parsing).
  Notation const := (mk true).
  Notation c := (mk true) (only parsing).

  Definition add (cq1 cq2 : t) : t :=
    mk (cq1.(is_const) && cq2.(is_const)) (cq1.(frac) + cq2.(frac)).
  #[global] Hint Opaque add : typeclass_instances.

  Definition scale (q : Qp) (cq : t) : t :=
    mk cq.(is_const) (q * cq.(frac)).
  #[global] Hint Opaque scale : typeclass_instances.

  Module Import notation.
    Add Printing Constructor t.
    #[global] Bind Scope cQp_scope with t.

    Infix "+" := add : cQp_scope.
  End notation.
  #[local] Open Scope cQp_scope.

  #[global] Instance t_inhabited : Inhabited t.
  Proof. apply populate, mk; apply inhabitant. Qed.
  #[global] Instance t_eq_dec : EqDecision t.
  Proof. solve_decision. Defined.
  #[global] Instance t_countable : Countable t.
  Proof.
    apply (inj_countable'
      (fun x => (x.(is_const), x.(frac)))
      (fun p => mk p.1 p.2)).
    abstract (by intros []).
  Defined.

  Lemma eta q : q = mk q.(is_const) q.(frac).
  Proof. done. Qed.

  (** Properties of [add] *)

  #[global] Instance add_comm : Comm (=) add.
  Proof.
    rewrite /add. intros x y. f_equal; by rewrite comm_L.
  Qed.

  #[global] Instance add_assoc : Assoc (=) add.
  Proof.
    rewrite /add. intros x y z. cbn. by rewrite !assoc_L.
  Qed.

  Lemma add_eq x y : x + y = Reduce (add x y).
  Proof. done. Qed.

  Lemma is_const_add x y : is_const (x + y) = is_const x && is_const y.
  Proof. done. Qed.
  Lemma frac_add x y : frac (x + y) = (frac x + frac y)%Qp.
  Proof. done. Qed.

  Lemma mk_add' c q1 q2 : mk c (q1 + q2) = mk c q1 + mk c q2.
  Proof. rewrite /add /=. by rewrite andb_diag. Qed.

  Lemma mk_add `{!split_frac.SplitFrac q q1 q2} c : mk c q = mk c q1 + mk c q2.
  Proof. by rewrite (split_frac q) mk_add'. Qed.

  Lemma mut_const' q1 q2 : mut (q1 + q2) = mut q1 + const q2.
  Proof. done. Qed.

  Lemma mut_const `{!split_frac.SplitFrac q q1 q2} : mut q = mut q1 + const q2.
  Proof. by rewrite (split_frac q). Qed.

  (** Properties of [scale] *)

  Lemma scale_eq q cq : scale q cq = Reduce (scale q cq).
  Proof. done. Qed.

  Lemma is_const_scale q cq : is_const (scale q cq) = is_const cq.
  Proof. done. Qed.
  Lemma frac_scale q cq : frac (scale q cq) = (q * frac cq)%Qp.
  Proof. done. Qed.

  Lemma scale_mk c q1 q2 : scale q1 (mk c q2) = mk c (q1 * q2).
  Proof. done. Qed.
  Lemma scale_mut q1 q2 : scale q1 (mut q2) = mut (q1 * q2).
  Proof. done. Qed.
  Lemma scale_const q1 q2 : scale q1 (const q2) = const (q1 * q2).
  Proof. done. Qed.

  Lemma scale_1 cq : scale 1 cq = cq.
  Proof. rewrite /scale. by rewrite Qp.mul_1_l. Qed.

  Lemma scale_comm q1 q2 q : scale q1 (scale q2 q) = scale q2 (scale q1 q).
  Proof. rewrite /scale. cbn. by rewrite !assoc_L [(q1*q2)%Qp]comm_L. Qed.

  Lemma scale_mul q1 q2 q : scale (q1 * q2) q = scale q1 (scale q2 q).
  Proof. rewrite/scale. cbn. by rewrite assoc_L. Qed.

  Lemma scale_add_l q1 q2 q : scale (q1 + q2) q = scale q1 q + scale q2 q.
  Proof.
    rewrite /scale/add. cbn.
    by rewrite Bool.andb_diag Qp.mul_add_distr_r.
  Qed.
  Lemma scale_add_r q q1 q2 : scale q (q1 + q2) = scale q q1 + scale q q2.
  Proof.
    rewrite /scale/add. cbn. by rewrite Qp.mul_add_distr_l.
  Qed.

  (** ** OFE *)

  Canonical Structure tO : ofe := leibnizO t.

  #[global] Instance: Params mk 0 := {}.
  #[global] Instance mk_ne : NonExpansive2 mk.
  Proof.
    intros n. by do 2!(intros ??; rewrite -discrete_iff leibniz_equiv_iff=>->).
  Qed.
  #[global] Instance mk_proper : Proper (equiv ==> equiv ==> equiv) mk.
  Proof. exact: ne_proper_2. Qed.

  #[global] Instance: Params is_const 0 := {}.
  #[global] Instance is_const_ne : NonExpansive is_const := _.
  #[global] Instance is_const_proper : Proper (equiv ==> equiv) is_const := _.

  #[global] Instance: Params frac 0 := {}.
  #[global] Instance frac_ne : NonExpansive frac := _.
  #[global] Instance frac_proper : Proper (equiv ==> equiv) frac := _.

  #[global] Instance mk_inj_eq : Inj2 eq eq eq mk.
  Proof. by intros ???? [= ->->]. Qed.
  #[global] Instance mk_inj_equiv : Inj2 equiv equiv equiv mk.
  Proof. intros ????. fold_leibniz. apply mk_inj_eq. Qed.
  #[global] Instance mk_inj_dist n : Inj2 (dist n) (dist n) (dist n) mk.
  Proof. intros ????. rewrite -!discrete_iff. apply mk_inj_equiv. Qed.

  (** ** CMRA *)

  Section cmra.
    #[local] Open Scope bool_scope.
    Implicit Types (x y : t).

    #[local] Instance t_op_instance : Op t := add.
    #[local] Instance t_pcore_instance : PCore t := fun x => None.
    #[local] Instance t_valid_instance : Valid t := fun x => ✓ x.(frac).

    Lemma t_op x y : x ⋅ y = x + y.
    Proof. done. Qed.
    Lemma t_pcore x : pcore x = None.
    Proof. done. Qed.
    Lemma t_valid x : ✓ x = ✓ x.(frac).
    Proof. done. Qed.
    Lemma t_included x y :
      x ≼ y <-> y.(is_const) <= x.(is_const) /\ (x.(frac) < y.(frac))%Qp.
    Proof.
      rewrite -frac_included. split.
      - intros [z ->%leibniz_equiv]. cbn. split. done. by exists (frac z).
      - intros [? [frac Hfrac]]. exists (mk y.(is_const) frac).
        rewrite t_op /add /=.
        rewrite Bool.andb_min_r//. by rewrite -frac_op -{}Hfrac.
    Qed.

    #[global] Instance mk_mono : Proper (flip Bool.le ==> Qp.lt ==> (≼)) mk.
    Proof. solve_proper_prepare. by rewrite t_included. Qed.
    #[global] Instance is_const_mono : Proper ((≼) ==> flip Bool.le) is_const.
    Proof. by intros x y [??]%t_included. Qed.
    #[global] Instance frac_mono : Proper ((≼) ==> Qp.lt) frac.
    Proof. by intros x y [??]%t_included. Qed.

    Lemma t_ra_mixin : RAMixin t.
    Proof.
      split; first [apply _|done|idtac].
      - (** ra_valid_op_l *) intros x y. rewrite t_op t_valid /=.
        exact: cmra_valid_op_l.
    Qed.
    Canonical Structure tR : cmra := discreteR t t_ra_mixin.

    #[global] Instance t_cmra_discrete : CmraDiscrete t.
    Proof. split. by apply _. done. Qed.

    #[global] Instance t_exclusive b : Exclusive (mk b 1).
    Proof.
      intros x. rewrite -cmra_discrete_valid_iff t_valid /=.
      exact: exclusive_l.
    Qed.
    #[global] Instance t_id_free x : IdFree x.
    Proof.
      apply: discrete_id_free=>y. rewrite t_valid=>/= Hv.
      rewrite t_op=>/mk_inj_equiv [] _ Heq.
      exact: (id_free_r x.(frac)).
    Qed.
    #[global] Instance t_cancelable q : Cancelable (mk true q).
    Proof.
      apply: discrete_cancelable=>y z.
      rewrite (eta y) !t_op /add /=.
      rewrite t_valid=>/= Hv. move=>/mk_inj_equiv [] -> Heq. f_equiv.
      exact: (cancelable q).
    Qed.
  End cmra.

  #[local] Definition _refl (c : bool) (q : Qp) : mk c q = mk c q := eq_refl _.
  #[deprecated(since="20221223")]
  Notation refl := _refl (only parsing).

  #[local] Lemma scale_combine' q1 q2 cq :
    scale q1 cq + scale q2 cq = scale (q1 + q2) cq.
  Proof. by rewrite scale_add_l. Qed.
  #[deprecated(since="20230106", note="use [cQp.scale_add_l].")]
  Notation scale_combine := scale_combine'.

End cQp.
Export cQp.notation.
Canonical Structure cQp.tO.
Canonical Structure cQp.tR.

(* as with C++, we make mutable the default *)
#[global] Coercion cQp.frac : cQp.t >-> Qp.

#[global] Notation "q '$m'" := (cQp.mut q) (format "q $m") : cQp_scope.
#[global] Notation "q '$c'" := (cQp.const q) (format "q $c") : cQp_scope.
#[global] Notation "1" := (1$m%cQp) (only parsing) : cQp_scope.


(** ** Backwards compatibility *)
(**
Old code can benefit from a coercion.
*)
Module cQp_compat.

  Module cQp.
    Export cfrac.cQp.

    Definition _mut : Qp -> t := mut.
    #[global] Arguments cQp._mut /.
  End cQp.

  Coercion cQp._mut : Qp >-> cQp.t.

  (**
  To enable the [_mut] coercion, we replay some [Qp] literals and
  (unambigous) operations in [cQp_scope], which is bound to type
  [cQp.t].
  *)
  Notation "1" := 1%Qp (only parsing) : cQp_scope.
  Notation "2" := 2%Qp (only parsing) : cQp_scope.
  Notation "3" := 3%Qp (only parsing) : cQp_scope.
  Notation "4" := 4%Qp (only parsing) : cQp_scope.
  Infix "/" := Qp.div (only parsing) : cQp_scope.
  Infix "*" := Qp.mul (only parsing) : cQp_scope.

End cQp_compat.

Section TEST.
  Variable TEST : cQp.t -> cQp.t -> cQp.t -> cQp.t -> Prop.

  Goal TEST 1 (cQp.c 1) 1$m (1/4)$c.
  (* TEST 1$m 1$c 1$m (1 / 4)$c *)
  Abort.

  Goal ∀ m c, TEST c (cQp.c m) 1$c m$m.
  (* ∀ (m : Qp) (c : cQp.t), TEST c m$c 1$c m$m *)
  Abort.

  Open Scope Qp.
  Variable f : Qp -> Qp.

  Goal ∀ m c, TEST c (cQp.c m) (f $ c)$c (f $ m/m) $m.
  (* ∀ (m : Qp) (c : cQp.t), TEST c m$c (f c)$c (f (m / m))$m *)
  Abort.

  Section with_compat.
  Import cQp_compat.

  (* TODO: to make this work without the [%Qp], we need to register the
     notations for [Qp] as notations in [cQq_scope]. *)
  Goal TEST 1 (cQp.c 1) (1/2) (cQp.c (1/4)).
  (* TEST 1%Qp 1$c (1 / 2)%Qp (1 / 4)$c *)
  Abort.
  End with_compat.

End TEST.
