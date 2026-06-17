(*
 * Copyright (c) 2020-23 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
(** ** Primitive Conversions

    This file covers conversions between primitive types.
 *)
Require Import elpi.apps.locker.locker.

Require Import skylabs.prelude.base.
Require Import skylabs.prelude.numbers.
Require Export skylabs.prelude.arith.operator.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.semantics.values.
Require Import skylabs.lang.cpp.semantics.genv.
Require Import skylabs.lang.cpp.semantics.promotion.
Require Import skylabs.lang.cpp.semantics.characters.
Export characters.

#[local] Open Scope Z_scope.

Lemma to_signed_bounded sz z :
  bitsize.bound sz Signed (to_signed sz z).
Proof.
  rewrite /bitsize.bound/bitsize.min_val/bitsize.max_val/to_signed.
  destruct sz; rewrite /to_signed_bits /=; repeat case_bool_decide;
    try generalize (Z_mod_lt z (2 ^ 8) ltac:(lia));
    try generalize (Z_mod_lt z (2 ^ 16) ltac:(lia));
    try generalize (Z_mod_lt z (2 ^ 32) ltac:(lia));
    try generalize (Z_mod_lt z (2 ^ 64) ltac:(lia));
    try generalize (Z_mod_lt z (2 ^ 128) ltac:(lia)); lia.
Qed.

Lemma to_signed_eq sz z :
  to_signed sz z = to_signed_bits (bitsize.bitsN sz) z.
Proof.
  destruct sz; rewrite /to_signed/to_signed_bits; repeat case_bool_decide; reflexivity.
Qed.

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
      if lang_version.le lang_version.Cpp20 (language_version tu) then
        match v with
        | Vint v => v' = Vint (to_signed (int_rank.bitsize sz) v)
        | _ => False
        end
      else
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
    { eapply has_int_type. apply to_signed_bounded. }
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
  Lemma conv_int_num_id sz (sgn : signed) v :
    let ty := Tnum sz sgn in
    ~~ is_raw v ->
    has_type_prop v ty ->
    conv_int tu ty ty v v.
  Proof using Hmod.
    rewrite /=/conv_int/underlying_type/=.
    intros ? Hty. split; eauto.
    destruct sgn.
    { case_match; last by split; eauto.
      apply has_int_type' in Hty.
      destruct Hty as [(? & -> & Hty) | (? & -> & ?)]; last done.
      move: Hty. rewrite /bitsize.bound/bitsize.min_val/bitsize.max_val. intros.
      symmetry.
      rewrite to_signed_eq.
      f_equal.
      apply to_signed_bits_spec_low.
      destruct sz; simpl in *; lia. }
    { apply has_int_type' in Hty.
      destruct Hty as [(? & -> & Hty) | (? & -> & ?)]; last done.
      move: Hty. rewrite /bitsize.bound/bitsize.min_val/bitsize.max_val. intros.
      rewrite to_unsigned_id//.
      destruct sz; simpl in *; lia. }
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

(** Floating point conversions.

    Source references:
    - Boolean conversions are specified by C++ [conv.bool]:
      <https://eel.is/c++draft/conv.bool#1>. Zero converts to [false];
      every other floating-point value converts to [true]. In particular, a
      NaN is not a zero value, so it converts to [true].
    - Floating-integral conversions are specified by C++ [conv.fpint]:
      <https://eel.is/c++draft/conv.fpint#1> and
      <https://eel.is/c++draft/conv.fpint#2>. Float-to-integral truncates
      when the truncated value is representable; otherwise the behavior is
      undefined. Integral-to-float is exact when possible and otherwise has an
      implementation-defined adjacent rounding choice.
    - Floating-to-floating conversions are specified by C++ [conv.double]:
      <https://eel.is/c++draft/conv.double#1>. Out-of-range conversions are
      undefined; in-range inexact conversions have implementation-defined
      adjacent choices.

    The operations [float_value.of_int], [float_value.to_int], and
    [float_value.cast] encode those implementation-defined choices and
    undefined cases. In particular, [float_value.to_int] returns [None] when
    there is no defined
    truncated integer value, such as NaN or infinity; destination
    representability is checked by the [has_type_prop] side condition below.
 *)
Definition conv_float {σ : genv} (tu : translation_unit) (from to : type) (v v' : val) : Prop :=
  has_type_prop v from /\
  match representation_type tu from , representation_type tu to with
  | Tbool , Tfloat_ f =>
      match is_true v with
      | Some b => v' = Vfloat f (float_value.of_int f (if b then 1 else 0))
      | None => False
      end
  | Tnum _ _ , Tfloat_ f =>
      match v with
      | Vint z => v' = Vfloat f (float_value.of_int f z)
      | _ => False
      end
  | Tchar_ ct , Tfloat_ f =>
      match v with
      | Vchar n =>
          v' = Vfloat f (float_value.of_int f (char_to_Z_for_float σ ct n))
      | _ => False
      end
  | Tfloat_ _ , Tbool =>
      match v with
      | Vfloat f z => v' = Vbool (float_value.is_true z)
      | _ => False
      end
  | Tfloat_ _ , Tnum _ _ =>
      match v with
      | Vfloat f z =>
          match float_value.to_int f z with
          | Some n => v' = Vint n /\ has_type_prop (Vint n) to
          | None => False
          end
      | _ => False
      end
  | Tfloat_ _ , Tchar_ ct =>
      match v with
      | Vfloat f z =>
          match float_to_char σ f ct z with
          | Some n => v' = Vchar n
          | None => False
          end
      | _ => False
      end
  | Tfloat_ _ , Tfloat_ f =>
      match v with
      | Vfloat f' z =>
          match float_value.cast f' f z with
          | Some z' => v' = Vfloat f z'
          | None => False
          end
      | _ => False
      end
  | _ , _ => False
  end.
Arguments conv_float !_ !_ _ _ /.

Section conv_float.
  Context `{Hmod : tu ⊧ σ}.

  Lemma conv_float_well_typed ty ty' v v' :
       tu ⊧ σ ->
       conv_float tu ty ty' v v' ->
       has_type_prop v ty /\ has_type_prop v' ty'.
  Proof using Hmod.
    rewrite /conv_float.
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
    all: try solve [eapply has_float_type].
    all: try solve [eapply float_to_char_has_type; eassumption].
    all: try solve [eapply has_bool_type; case_match; lia].
    all: try solve [
      match goal with
      | H : has_type_prop ?v ?ty, E : representation_type tu ?ty = ?r
        |- has_type_prop ?v ?r =>
          rewrite -E; eapply has_type_prop_representation_type; exact H
      end].
    all: try solve [
      apply has_type_prop_char';
      match goal with
      | |- (0 <= to_char ?from ?sgn ?bits ?z < 2 ^ ?bits)%N =>
          generalize (to_char_bounded from sgn bits z); lia
      end].
  Qed.

  Lemma conv_float_unique from to v :
      forall v' v'', conv_float tu from to v v' ->
                conv_float tu from to v v'' ->
                v' = v''.
  Proof using Hmod.
    rewrite /conv_float.
    repeat (case_match; try tauto); intuition; try congruence.
  Qed.

  Lemma conv_float_id ft (fv fv' : float_type.car ft) :
      float_value.cast ft ft fv = Some fv' ->
      conv_float tu (Tfloat_ ft) (Tfloat_ ft) (Vfloat ft fv) (Vfloat ft fv').
  Proof using Hmod.
    intros Hcast. rewrite /conv_float. cbn [representation_type drop_qualifiers erase_qualifiers].
    split; first apply has_float_type.
    change (match float_value.cast ft ft fv with
            | Some z' => Vfloat ft fv' = Vfloat ft z'
            | None => False
            end).
    by rewrite Hcast.
  Qed.

  Lemma conv_float_to_bool ft (fv : float_type.car ft) :
      conv_float tu (Tfloat_ ft) Tbool (Vfloat ft fv)
        (Vbool (float_value.is_true fv)).
  Proof using Hmod.
    rewrite /conv_float /=. split; first apply has_float_type. done.
  Qed.

  Lemma conv_float_cast from to (fv : float_type.car from) fv' :
      float_value.cast from to fv = Some fv' ->
      conv_float tu (Tfloat_ from) (Tfloat_ to) (Vfloat from fv) (Vfloat to fv').
  Proof using Hmod.
    intros Hcast. rewrite /conv_float. cbn [representation_type drop_qualifiers erase_qualifiers].
    split; first apply has_float_type.
    change (match float_value.cast from to fv with
            | Some z' => Vfloat to fv' = Vfloat to z'
            | None => False
            end).
    by rewrite Hcast.
  Qed.

  Lemma conv_float_int_to_float ty sz sgn ft z :
      representation_type tu ty = Tnum sz sgn ->
      has_type_prop (Vint z) ty ->
      conv_float tu ty (Tfloat_ ft) (Vint z) (Vfloat ft (float_value.of_int ft z)).
  Proof using Hmod.
    intros Hrepr Hty. rewrite /conv_float Hrepr /=. by split.
  Qed.

  Lemma conv_float_bool_to_float ft b :
      conv_float tu Tbool (Tfloat_ ft) (Vbool b)
        (Vfloat ft (float_value.of_int ft (if b then 1 else 0))).
  Proof using Hmod.
    rewrite /conv_float /=. split.
    - rewrite has_type_prop_bool. by eexists.
    - by destruct b.
  Qed.

  Lemma conv_float_char_to_float ct ft n :
      has_type_prop (Vchar n) (Tchar_ ct) ->
      conv_float tu (Tchar_ ct) (Tfloat_ ft) (Vchar n)
        (Vfloat ft (float_value.of_int ft (char_to_Z_for_float σ ct n))).
  Proof using Hmod.
    intros Hty. rewrite /conv_float /=. by split.
  Qed.

  Lemma conv_float_to_int ty sz sgn ft (fv : float_type.car ft) z :
      representation_type tu ty = Tnum sz sgn ->
      float_value.to_int ft fv = Some z ->
      has_type_prop (Vint z) ty ->
      conv_float tu (Tfloat_ ft) ty (Vfloat ft fv) (Vint z).
  Proof using Hmod.
    intros Hrepr Hto Hty. rewrite /conv_float Hrepr /=. split; first apply has_float_type.
    by rewrite Hto.
  Qed.

  Lemma conv_float_to_char ft ct (fv : float_type.car ft) n :
      float_to_char σ ft ct fv = Some n ->
      conv_float tu (Tfloat_ ft) (Tchar_ ct) (Vfloat ft fv) (Vchar n).
  Proof using Hmod.
    intros Hto. rewrite /conv_float /=. split; first apply has_float_type.
    by rewrite Hto.
  Qed.

  Lemma conv_float_enum_to_float nm sz sgn ft z :
      representation_type tu (Tenum nm) = Tnum sz sgn ->
      has_type_prop (Vint z) (Tenum nm) ->
      conv_float tu (Tenum nm) (Tfloat_ ft) (Vint z)
        (Vfloat ft (float_value.of_int ft z)).
  Proof using Hmod.
    intros Hrepr Hty. rewrite /conv_float Hrepr /=. by split.
  Qed.

  Lemma conv_float_to_enum nm sz sgn ft (fv : float_type.car ft) z :
      representation_type tu (Tenum nm) = Tnum sz sgn ->
      float_value.to_int ft fv = Some z ->
      has_type_prop (Vint z) (Tenum nm) ->
      conv_float tu (Tfloat_ ft) (Tenum nm) (Vfloat ft fv) (Vint z).
  Proof using Hmod.
    intros Hrepr Hto Hty. rewrite /conv_float Hrepr /=. split; first apply has_float_type.
    by rewrite Hto.
  Qed.

  Lemma conv_float_widen (fv : float_type.car float_type.Ffloat) fv' :
      float_value.cast float_type.Ffloat float_type.Fdouble fv = Some fv' ->
      conv_float tu Tfloat Tdouble (Vfloat float_type.Ffloat fv) (Vfloat float_type.Fdouble fv').
  Proof using Hmod. apply conv_float_cast. Qed.

  Lemma conv_float_narrow (fv : float_type.car float_type.Fdouble) fv' :
      float_value.cast float_type.Fdouble float_type.Ffloat fv = Some fv' ->
      conv_float tu Tdouble Tfloat (Vfloat float_type.Fdouble fv) (Vfloat float_type.Ffloat fv').
  Proof using Hmod. apply conv_float_cast. Qed.
End conv_float.

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
    conv_int tu from to v v' \/ conv_float tu from to v v'
  else False.
