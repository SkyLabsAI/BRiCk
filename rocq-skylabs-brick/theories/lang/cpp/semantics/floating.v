(*
 * Copyright (c) 2026 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(** Flocq-backed representation helpers for C++ floating point values. *)
Require Import skylabs.prelude.base.
Require Import skylabs.prelude.numbers.
Require Import skylabs.lang.cpp.syntax.
Require Import Flocq.IEEE754.Binary.
Require Import Flocq.IEEE754.Bits.

#[local] Open Scope Z_scope.

Module cpp_float.
  Record t : Set := mk {
    ty : float_type.t;
    bits : Z;
  }.

  #[global] Instance t_eq_dec : EqDecision t := ltac:(solve_decision).

  Definition bits_bound (ft : float_type.t) (z : Z) : Prop :=
    0 <= z < 2 ^ Z.of_N (float_type.bitsN ft).

  Definition valid (f : t) : Prop :=
    bits_bound f.(ty) f.(bits).

  Definition zero_bits (_ : float_type.t) : Z := 0.

  Definition neg_zero_bits (ft : float_type.t) : Z :=
    2 ^ (Z.of_N (float_type.bitsN ft) - 1).

  Definition is_zero_bits (ft : float_type.t) (z : Z) : bool :=
    bool_decide (z = zero_bits ft \/ z = neg_zero_bits ft).

  Definition is_true (f : t) : bool :=
    negb (is_zero_bits f.(ty) f.(bits)).

  Definition zero (ft : float_type.t) : t :=
    mk ft (zero_bits ft).

  Definition of_bits (ft : float_type.t) (bits : Z) : t :=
    mk ft bits.

  Definition has_type (f : t) (ft : float_type.t) : Prop :=
    f.(ty) = ft /\ valid f.

  Definition binary16 := binary_float 11 16.
  Definition binary128 := binary_float 113 16384.

  Definition default_nan_pl16 : { nan : binary16 | is_nan 11 16 nan = true } :=
    exist _ (@B754_nan 11 16 false xH (refl_equal true)) (refl_equal true).
  Definition unop_nan_pl16 (f : binary16) : { nan : binary16 | is_nan 11 16 nan = true } :=
    match f as f with
    | @B754_nan _ _ s pl Hpl => exist _ (@B754_nan 11 16 s pl Hpl) (refl_equal true)
    | _ => default_nan_pl16
    end.

  Definition default_nan_pl128 : { nan : binary128 | is_nan 113 16384 nan = true } :=
    exist _ (@B754_nan 113 16384 false xH (refl_equal true)) (refl_equal true).
  Definition unop_nan_pl128 (f : binary128) : { nan : binary128 | is_nan 113 16384 nan = true } :=
    match f as f with
    | @B754_nan _ _ s pl Hpl => exist _ (@B754_nan 113 16384 s pl Hpl) (refl_equal true)
    | _ => default_nan_pl128
    end.

  Definition b16_of_bits : Z -> binary16 :=
    binary_float_of_bits 10 5 (refl_equal _) (refl_equal _) (refl_equal _).
  Definition bits_of_b16 : binary16 -> Z :=
    bits_of_binary_float 10 5.

  Definition b128_of_bits : Z -> binary128 :=
    binary_float_of_bits 112 15 (refl_equal _) (refl_equal _) (refl_equal _).
  Definition bits_of_b128 : binary128 -> Z :=
    bits_of_binary_float 112 15.

  Definition to_flocq_type (ft : float_type.t) : Type :=
    match ft with
    | float_type.Ffloat16 => binary16
    | float_type.Ffloat => binary32
    | float_type.Fdouble => binary64
    | float_type.Flongdouble => binary128
    | float_type.Ffloat128 => binary128
    end.

  Definition to_flocq (f : t) : to_flocq_type f.(ty) :=
    match f.(ty) as ft return to_flocq_type ft with
    | float_type.Ffloat16 => b16_of_bits f.(bits)
    | float_type.Ffloat => b32_of_bits f.(bits)
    | float_type.Fdouble => b64_of_bits f.(bits)
    | float_type.Flongdouble => b128_of_bits f.(bits)
    | float_type.Ffloat128 => b128_of_bits f.(bits)
    end.

  Definition bits_of_flocq (ft : float_type.t) : to_flocq_type ft -> Z :=
    match ft as ft return to_flocq_type ft -> Z with
    | float_type.Ffloat16 => bits_of_b16
    | float_type.Ffloat => bits_of_b32
    | float_type.Fdouble => bits_of_b64
    | float_type.Flongdouble => bits_of_b128
    | float_type.Ffloat128 => bits_of_b128
    end.

  Definition from_flocq (ft : float_type.t) (f : to_flocq_type ft) : t :=
    mk ft (bits_of_flocq ft f).

  Definition same_type (a b : t) : bool :=
    bool_decide (a.(ty) = b.(ty)).

  Definition promote_type (l r : float_type.t) : float_type.t :=
    match l, r with
    | float_type.Ffloat128, _ | _, float_type.Ffloat128 => float_type.Ffloat128
    | float_type.Flongdouble, _ | _, float_type.Flongdouble => float_type.Flongdouble
    | float_type.Fdouble, _ | _, float_type.Fdouble => float_type.Fdouble
    | float_type.Ffloat, _ | _, float_type.Ffloat => float_type.Ffloat
    | float_type.Ffloat16, float_type.Ffloat16 => float_type.Ffloat16
    end.

  Definition promote (ft : float_type.t) (f : t) : option t :=
    if bool_decide (f.(ty) = ft) then Some f else None.

  Definition binop (op16 : binary16 -> binary16 -> binary16)
      (op32 : binary32 -> binary32 -> binary32)
      (op64 : binary64 -> binary64 -> binary64)
      (op128 : binary128 -> binary128 -> binary128)
      (a b : t) : option t :=
    if bool_decide (a.(ty) = b.(ty)) then
      Some $
      match a.(ty) as ft return a.(ty) = ft -> t with
      | float_type.Ffloat16 =>
          fun _ => from_flocq float_type.Ffloat16
                     (op16 (b16_of_bits a.(bits)) (b16_of_bits b.(bits)))
      | float_type.Ffloat =>
          fun _ => from_flocq float_type.Ffloat
                     (op32 (b32_of_bits a.(bits)) (b32_of_bits b.(bits)))
      | float_type.Fdouble =>
          fun _ => from_flocq float_type.Fdouble
                     (op64 (b64_of_bits a.(bits)) (b64_of_bits b.(bits)))
      | float_type.Flongdouble =>
          fun _ => from_flocq float_type.Flongdouble
                     (op128 (b128_of_bits a.(bits)) (b128_of_bits b.(bits)))
      | float_type.Ffloat128 =>
          fun _ => from_flocq float_type.Ffloat128
                     (op128 (b128_of_bits a.(bits)) (b128_of_bits b.(bits)))
      end eq_refl
    else None.

  Definition neg (f : t) : t :=
    match f.(ty) as ft return f.(ty) = ft -> t with
    | float_type.Ffloat16 =>
        fun _ => from_flocq float_type.Ffloat16 (Bopp 11 16 unop_nan_pl16 (b16_of_bits f.(bits)))
    | float_type.Ffloat =>
        fun _ => from_flocq float_type.Ffloat (b32_opp (b32_of_bits f.(bits)))
    | float_type.Fdouble =>
        fun _ => from_flocq float_type.Fdouble (b64_opp (b64_of_bits f.(bits)))
    | float_type.Flongdouble =>
        fun _ => from_flocq float_type.Flongdouble (Bopp 113 16384 unop_nan_pl128 (b128_of_bits f.(bits)))
    | float_type.Ffloat128 =>
        fun _ => from_flocq float_type.Ffloat128 (Bopp 113 16384 unop_nan_pl128 (b128_of_bits f.(bits)))
    end eq_refl.

  (** Dynamic arithmetic is axiomatized for now; the representation above still
      pins values and object representations to Flocq IEEE formats. *)
  Parameter add sub mul div : t -> t -> option t.
  Parameter cast : float_type.t -> t -> t.
  Parameter of_Z : float_type.t -> Z -> t.
  Parameter to_Z : t -> option Z.

  Parameter compare : t -> t -> option comparison.
End cpp_float.
