(*
 * Copyright (c) 2020-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
(** * Type-level semantics of type promotions

    This captures the rules that C++ uses to promote values to integral types for
    the purposes of performing computation.

    This file contains *only* static-semantics, i.e. determining what casts should
    be performed. The dynamic semantics of casts is defined in [semantics/cast.v]
 *)

Require Import bluerock.prelude.base.
Require Import bluerock.prelude.numbers.
Require Export bluerock.prelude.arith.operator.
Require Import bluerock.lang.cpp.syntax.
Require Import bluerock.lang.cpp.semantics.values.

#[local] Open Scope Z_scope.

(** [underlying_type tu nm] is the type that underlies [Tenum nm].
 *)
Definition underlying_type (tu : translation_unit) (nm : globname) : option type :=
  match tu.(types) !! nm with
  | Some (Genum ty _) => Some $ drop_qualifiers ty
  | _ => None
  end.

(** [representation_type tu ty] is the type that underlies [ty] if [ty] is an [enum],
    otherwise, it is the orginal type.

    Note that if the [enum] is not defined in the translation unit, then the result
    it the original [enum].
 *)
Definition representation_type (tu : translation_unit) (ty : type) : type :=
  match drop_qualifiers ty with
  | Tenum nm as ty => default ty $ underlying_type tu nm
  | ty => ty
  end.

Succeed Example underlying_int : forall tu, representation_type tu Tint = Tint :=
  ltac:(compute; auto).
Succeed Example underlying_int : forall tu, representation_type tu (Tconst Tint) = Tint :=
  ltac:(compute; auto).

(** [underlying_unqual_type tu ty] is the unqualified type that underlies [ty].

    This is the strip qualifiers function if [ty] is not an `enum`.

 *)
Definition underlying_unqual_type (tu : translation_unit) (ty : type) : type :=
  let '(cv, ty') := decompose_type ty in
  match ty' with
  | Tenum nm as ty =>
      match tu.(types) !! nm with
      | Some (Genum ty _) => ty
      | _ => ty'
      end
  | _ => ty'
  end.

Succeed Example underlying_int : forall tu, underlying_unqual_type tu (Tconst Tint) = Tint :=
  ltac:(compute; auto).

Section representable.
  Context {σ : genv}.
  (* [fully_representable a b] is [true] if all (well-typed) values of [a] values of [b] *)
  Definition fully_representable (a b : type) : bool :=
    let to_equiv ty :=
      match ty with
      | Tnum a b => Some $ integral_type.mk a b
      | Tchar_ ct => Some $ equivalent_int_type _ ct
      | _ => None
      end
    in
    let min ty := (fun '(integral_type.mk sz sgn) => int_rank.min_val sz sgn) <$> to_equiv ty in
    let max ty := (fun '(integral_type.mk sz sgn) => int_rank.max_val sz sgn) <$> to_equiv ty in
    match min a , min b , max a , max b with
    | Some an , Some bn , Some ax , Some bx =>
        bool_decide (bn <= an /\ ax <= bx)%Z
    | _ , _ , _ , _ => false
    end.

  (* [first_representable ty ls] gets the first type in [ls] that is able to
     fully represent [ty]
   *)
  Fixpoint first_representable (ty : type) (ls : list type) : option type :=
    match ls with
    | nil => None
    | l :: ls => if fully_representable ty l then Some l else first_representable ty ls
    end.
End representable.

(** ** Integral Promotion
    This is used to promote a type to a type that supports arithmetic operators.
    For example, it converts types smaller than `int` to `int` (of some signedness).
    Because it converts `enum` types to integral types, it takes a [translation_unit].

    The operation is partial for non-integral types, e.g. struct types.

    Note that integral promotion does *not* change the value in the C++ semantics;
    however, it does change from [Vchar] to an equivalent [Vint] in BRiCk's
    architecture-independent semantics.

    > A prvalue of an integer type other than `bool`, `char8_t`, `char16_t`,
    > `char32_t`, or `wchar_t` whose integer conversion rank ([conv.rank])
    > is less than the rank of `int` can be converted to a prvalue of type `int`
    > if int can represent all the values of the source type; otherwise, the
    > source prvalue can be converted to a prvalue of type `unsigned int`.

    <https://eel.is/c++draft/conv.prom>

 *)
Definition promote_integral {σ : genv} (tu : translation_unit) (ty : type) : option type :=
  match representation_type tu ty with
    (* signed char or short can be converted to int *)
  | Tschar
  | Tshort => Some Tint
    (* unsigned char or unsigned short can be converted to int if it can hold its entire
        value range, and unsigned int otherwise *)
  | Tuchar as ty
  | Tushort as ty => Some $ if fully_representable ty Tint then Tint else Tuint
  | Tnum _ _ as ty => Some ty
  | Tchar =>
      Some $ let rty := if σ.(char_signed) is Signed then Tschar else Tuchar in
             if fully_representable rty Tint then Tint else Tuint
  | Twchar
  | Tchar_ char_type.C8
  | Tchar_ char_type.C16
  | Tchar_ char_type.C32 =>
    (* wchar_t, char8_t (since C++20), char16_t, and char32_t
       (since C++11) can be converted to the first type from the
       following list able to hold their entire value range: int,
       unsigned int, long, unsigned long, long long,
       unsigned long long (since C++11) *)

      first_representable ty [Tint;Tuint;Tlong;Tulong;Tlonglong;Tulonglong]
  | Tenum nm => None
      (* unreachable because of [underlying_type] and because the
          underlying type of an `enum` must be a fundamental type. *)
      (* an unscoped enumeration type whose underlying type
        is not fixed can be converted to the first type from the following
        list able to hold their entire value range: int, unsigned int, long,
        unsigned long, long long, or unsigned long long, extended integer
        types with higher conversion rank (in rank order, signed given
        preference over unsigned) (since C++11). If the value range is
        greater, no integral promotions apply;

        an unscoped enumeration type whose underlying type is
        fixed can be converted to its underlying type, and, if the
        underlying type is also subject to integral promotion, to the
        promoted underlying type. Conversion to the unpromoted underlying
        type is better for the purposes of overload resolution)

        NOTE: this only applies to `unscoped` enumerations; however, the
        program will never contain these sorts of implicit conversions for
        scoped enumerations, so we do not need to check this fact.
          *)
  | Tbool => Some Tint
  | Tptr _
  | Tref _
  | Trv_ref _
  | Tvoid
  | Tarray _ _
  | Tincomplete_array _
  | Tvariable_array _ _
  | Tnamed _
  | Tfunction _
  | Tmember_pointer _ _
  | Tfloat_ _
  | Tnullptr
  | Tarch _ _ => None
  | Tqualified _ _ => None (* unreachable *)
  | Tunsupported _ => None
  | Tparam _
  | Tresult_param _
  | Tresult_global _
  | Tresult_parenlist _ _
  | Tresult_member_call _ _ _
  | Tresult_member _ _
  | Tresult_unop _ _
  | Tresult_binop _ _ _
  | Tdecltype _ (* ?? *)
  | Texprtype _ (* ?? *)
  | Tauto
  | Tresult_call _ _ => None
  end.

Goal forall {σ : genv} tu, promote_integral tu Tchar = Some Tint.
Proof.
  intros. rewrite /promote_integral/=.
  destruct (char_signed σ); done.
Succeed Qed. Abort.
Goal forall {σ : genv} tu, promote_integral tu Twchar = Some (integral_type.to_type $ equivalent_int_type _ char_type.Cwchar).
Proof.
  intros. rewrite /promote_integral/equivalent_int_type/=.
  rewrite /fully_representable/=.
  destruct (wchar_signed σ); done.
Succeed Qed. Abort.

(* Test cases *)
Succeed Example promote_short : forall {σ : genv} tu,
    promote_integral tu Tshort = Some Tint :=
  ltac:(compute; reflexivity).
Succeed Example promote_uchar : forall {σ : genv} tu,
    promote_integral tu Tuchar = Some Tint :=
  ltac:(compute; reflexivity).
Succeed Example promote_schar : forall {σ : genv} tu,
    promote_integral tu Tschar = Some Tint :=
  ltac:(compute; reflexivity).

(** ** Arithmetic Promotion
  This computes a "join" on the types of the two arguments to an arithmetic
  operator.

  https://eel.is/c++draft/expr.arith.conv#1.3

  (1.3.1) If both operands have the same type, no further conversion is needed.
  (1.3.2) Otherwise, if both operands have signed integer types or both have
          unsigned integer types, the operand with the type of lesser integer
          conversion rank is converted to the type of the operand with greater
          rank.
  (1.3.3) Otherwise, if the operand that has unsigned integer type has rank
          greater than or equal to the rank of the type of the other operand,
          the operand with signed integer type is converted to the type of the
          operand with unsigned integer type.
  (1.3.4) Otherwise, if the type of the operand with signed integer type can
          represent all of the values of the type of the operand with unsigned
          integer type, the operand with unsigned integer type is converted to
          the type of the operand with signed integer type.
  (1.3.5) Otherwise, both operands are converted to the unsigned integer type
          corresponding to the type of the operand with signed integer type.
  *)
Definition promote_arith (ty1 ty2 : type) : option type :=
  match ty1 , ty2 with
  | Tnum sz1 sgn1 , Tnum sz2 sgn2 =>
      if bool_decide (sgn1 = sgn2) then
        Some $ Tnum (int_rank.t_max sz1 sz2) sgn1
      else
        let (ssz, usz) := match sgn1 with
                          | Signed => (sz1, sz2)
                          | Unsigned => (sz2, sz1)
                          end
        in
        if bool_decide (int_rank.t_le ssz usz) then
          Some $ Tnum usz Unsigned
        else if bool_decide (int_rank.t_le usz ssz) then
          Some $ Tnum ssz Signed
        else
          Some $ Tnum ssz Unsigned
  | _ , _ => None
  end.

(* Test cases *)
Succeed Example promote_int_long : promote_arith Tint Tlong = Some Tlong := eq_refl.
Succeed Example promote_int_ulong : promote_arith Tint Tulong = Some Tulong := eq_refl.
Succeed Example promote_uint_long : promote_arith Tuint Tlong = Some Tlong := eq_refl.
