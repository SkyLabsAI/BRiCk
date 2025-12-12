(*
 * Copyright (c) 2020-23 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
(** ** Primitive Conversions

    This file covers conversions between primitive types.
 *)
Require Import elpi.apps.locker.locker.

Require Import bluerock.prelude.base.
Require Import bluerock.prelude.numbers.
Require Export bluerock.prelude.arith.operator.
Require Import bluerock.lang.cpp.syntax.
Require Import bluerock.lang.cpp.semantics.values.
Require Import bluerock.lang.cpp.semantics.genv.
Require Import bluerock.lang.cpp.semantics.promotion.
Require Import bluerock.lang.cpp.semantics.characters.
Export characters.

#[local] Open Scope Z_scope.

(** Numeric conversions.

    This includes both conversions and promotions between fundamental
    numeric types and enumerations (which have underlying fundamental
    types).

    This relation only holds on well-typed values, see [conv_int_well_typed].
  *)
Definition conv_int {σ : genv} (tu : translation_unit) (from to : type) (v v' : val) : Prop :=
  has_type_prop v from /\
  match representation_type tu from , representation_type tu to with
  | Tbool , Tnum _ _ =>
      match is_true v with
      | Some v => v' = Vbool v
      | _ => False
      end
  | Tbool , Tchar_ _ =>
      match is_true v with
      | Some v => v' = Vchar (if v then 1 else 0)%N
      | _ => False
      end
  | Tnum _ _ , Tbool =>
      match v with
      | Vint v => v' = Vbool (bool_decide (v <> 0))
      | _ => False
      end
  | Tnum _ _ , Tnum sz Unsigned =>
      match v with
      | Vint v => v' = Vint (to_unsigned (int_rank.bitsize sz) v)
      | _ => False
      end
  | Tnum _ _ , Tnum sz Signed =>
      (* Prior to C++20, conversions to signed integer types were implementation
         defined if the source value can not be represented in the target value *)
      has_type_prop v (Tnum sz Signed) /\ v' = v
  | Tbool , Tbool => v = v'
  | Tchar_ _ , Tbool =>
      match v with
      | Vchar v => v' = Vbool (bool_decide (v <> 0%N))
      | _ => False
      end
  | Tnum sz sgn , Tchar_ ct =>
      match v with
      | Vint v =>
          v' = Vchar (to_char (int_rank.bitsN sz) sgn (char_type.bitsN ct) v)
      | _ => False
      end
  | Tchar_ ct , Tnum sz sgn =>
      match v with
      | Vchar v => v' = Vint (of_char (char_type.bitsN ct) (signedness_of_char σ ct) (int_rank.bitsN sz) sgn v)
      | _ => False
      end
  | Tchar_ ct , Tchar_ ct' =>
      match v with
      | Vchar v => v' = Vchar (to_char (char_type.bitsN ct) Unsigned (char_type.bitsN ct') v)
      | _ => False
      end
  | Tenum _ , _
  | _ , Tenum _ (* not reachable due to [representation_type] *)
  | _ , _ => False
  end.
Arguments conv_int !_ !_ _ _ /.

Section conv_int.
  Context `{Hmod : tu ⊧ σ}.

  (* TODO move *)
  Lemma has_type_prop_representation_type ty v :
    has_type_prop v ty -> has_type_prop v (representation_type tu ty).
  Proof using Hmod.
    induction ty; rewrite /representation_type /= //.
    { intros.
      rewrite /underlying_type.
      case_match => //.
      case_match => //.
      eapply has_type_prop_enum in H.
      destruct H as [?[?[?[?[??]]]]].
      subst.
      generalize (enum_compat (ODR Hmod H _ _ _ H0 H2)); intro; subst.
      tauto. }
    { intros.
      apply has_type_prop_qual_iff in H.
      by apply IHty. }
  Qed.

  Lemma has_type_prop_representation_type_not_raw ty v :
    ~~ is_raw v ->
    has_type_prop v ty <-> has_type_prop v (representation_type tu ty).
  Proof using Hmod.
    induction ty; rewrite /representation_type /= //.
    { split; intros.
      { rewrite /underlying_type.
        case_match => //.
        case_match => //.
        eapply has_type_prop_enum in H0.
        destruct H0 as [?[?[?[?[??]]]]].
        subst.
        generalize (enum_compat (ODR Hmod H0 _ _ _ H1 H3)); intro; subst.
        tauto. }
      { unfold underlying_type in H0.
        case_match; simpl in *; eauto.
        case_match; simpl in *; eauto.
        apply has_type_prop_enum. do 3 eexists; split; eauto. } }
    { intros.
      apply IHty in H.
      rewrite -has_type_prop_qual_iff. apply H. }
  Qed.
  (* END MOVE *)

  Lemma conv_int_well_typed ty ty' v v' :
       tu ⊧ σ -> (* TODO only needed if either type is a [Tenum] *)
       conv_int tu ty ty' v v' ->
       has_type_prop v ty /\ has_type_prop v' ty'.
  Proof using Hmod.
    rewrite /conv_int.
    destruct (representation_type tu ty) eqn:src_ty; rewrite /=; try tauto;
    destruct (representation_type tu ty') eqn:dst_ty; rewrite /=; try tauto;
    intuition;
    match goal with
    | H : representation_type ?tu ?ty = ?ty' , H' : has_type_prop _ ?ty |- _ =>
        generalize (has_type_prop_representation_type _ _ H'); rewrite H; intro
    end; repeat (case_match; try tauto);
      repeat match goal with
        | H : _ /\ _ |- _ => destruct H
        | H : exists x, _ |- _ => destruct H
        | H : representation_type _ ?ty = ?ty2 |- has_type_prop _ ?ty =>
            eapply has_type_prop_representation_type_not_raw => /=; try congruence; try rewrite H
        end; subst; eauto.
    { destruct v; simpl; try tauto.
      eapply has_int_type' in H2.
      destruct H2 as [[?[??]] | [?[??]]]; congruence. }
    { eapply has_int_type.
      red; rewrite /=/bitsize.max_val/trim.
      generalize (Z_mod_lt z (2 ^ int_rank.bitsN sz0) ltac:(lia)).
      destruct sz0 => /=; lia. }
    { eapply has_type_prop_char.
      eexists; split; eauto.
      rewrite to_char.unlock.
      generalize (Z_mod_lt z (2 ^ char_type.bitsN t) ltac:(lia)).
      destruct t; try lia. }
    { eapply has_bool_type. case_match; lia. }
    { eapply has_int_type.
      eapply has_type_prop_char' in H0.
      red.
      generalize (of_char_bounded (char_type.bitsN t) (signedness_of_char σ t) (int_rank.bitsN sz) sgn n
                    ltac:(destruct sz; simpl; lia)
                    ltac:(destruct t; simpl; lia)).
      rewrite /bitsize.min_val/bitsize.max_val.
      destruct sgn, sz; simpl; lia. }
    { apply has_type_prop_char; eexists; split; eauto.
      apply has_type_prop_char in H0.
      destruct H0 as [?[Hinv?]]; inversion Hinv; subst.
      generalize (to_char_bounded (char_type.bitsN t) Unsigned (char_type.bitsN t0) (Z.of_N x)); eauto. }
    { eapply has_bool_type; case_match; lia. }
    { eapply has_int_type. red; destruct sz, sgn, b => /=; lia. }
    { eapply has_type_prop_char'. destruct t => /=; lia. }
    { eapply has_type_prop_char; eexists; split; eauto. destruct t => /=; lia. }
    { eapply has_type_prop_bool in H0.
      destruct H0. subst. simpl. tauto. }
  Qed.

  (* Note that a no-op conversion on a raw value is not permitted. *)
  Lemma conv_int_num_id sz sgn v :
    let ty := Tnum sz sgn in
    ~~ is_raw v ->
    has_type_prop v ty ->
    conv_int tu ty ty v v.
  Proof using Hmod.
    rewrite /=/conv_int/underlying_type/=.
    intros ? Hty. split; eauto.
    destruct sgn. split; eauto.
    apply has_int_type' in Hty.
    destruct Hty as [(? & -> & Hty) | (? & -> & ?)]; last done.
    move: Hty. rewrite /bitsize.bound/bitsize.min_val/bitsize.max_val. intros.
    rewrite to_unsigned_id//.
    destruct sz; simpl in *; lia.
  Qed.

  (* conversion is deterministic *)
  Lemma conv_int_unique from to v :
      forall v' v'', conv_int tu from to v v' ->
                conv_int tu from to v v'' ->
                v' = v''.
  Proof using Hmod.
    rewrite /conv_int.
    repeat (case_match; try tauto); intuition; try congruence.
  Qed.
End conv_int.

(* This (effectively) lifts [conv_int] to arbitrary types.

   TODO: it makes sense for this to mirror the properties of [conv_int], but
   pointer casts require side-conditions that are only expressible in
   separation logic.
 *)
Definition convert {σ : genv} (tu : translation_unit) (from to : Rtype) (v : val) (v' : val) : Prop :=
  if is_pointer from && bool_decide (erase_qualifiers from = erase_qualifiers to) then
    (* TODO: this conservative *)
    has_type_prop v from /\ has_type_prop v' to /\ v' = v
  else if is_arithmetic from && is_arithmetic to then
    conv_int tu from to v v'
  else False.
