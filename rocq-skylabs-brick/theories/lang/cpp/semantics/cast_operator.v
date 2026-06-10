(*
 * Copyright (c) 2020-23 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
(**
   Semantics of arithmetic operators on primitives.
   This does not include the semantics of pointer operations because they
   require side conditions on the abstract machine state.
 *)

Require Import skylabs.prelude.base.
Require Import skylabs.prelude.numbers.
Require Export skylabs.prelude.arith.operator.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.semantics.values.
Require Import skylabs.lang.cpp.semantics.promotion.
Require Import skylabs.lang.cpp.semantics.cast.

#[local] Open Scope Z_scope.

(** ** Binary Operator Static Semantics

    The static (type-level) promotion semantics of binary operators
  *)
Notation Tptrdiff_t := Tlonglong (only parsing).

Definition supported_float_type (ty : type) : option float_type.t :=
  match drop_qualifiers ty with
  | Tfloat_ ft => if fp_supported ft then Some ft else None
  | _ => None
  end.

Definition usual_float_arith (tu : translation_unit) (ty1 ty2 : type) : option type :=
  match supported_float_type ty1, supported_float_type ty2 with
  | Some Fdouble, Some (Ffloat | Fdouble) => Some Tdouble
  | Some Ffloat, Some Fdouble => Some Tdouble
  | Some Ffloat, Some Ffloat => Some Tfloat
  | Some Fdouble, None =>
      match promote_integral tu ty2 with
      | Some _ => Some Tdouble
      | None => None
      end
  | None, Some Fdouble =>
      match promote_integral tu ty1 with
      | Some _ => Some Tdouble
      | None => None
      end
  | Some Ffloat, None =>
      match promote_integral tu ty2 with
      | Some _ => Some Tfloat
      | None => None
      end
  | None, Some Ffloat =>
      match promote_integral tu ty1 with
      | Some _ => Some Tfloat
      | None => None
      end
  | _, _ => None
  end.

Definition convert_type_float_op (b : BinOp) (to : type) : option (type * type * type) :=
  match b with
  | Badd | Bsub | Bmul | Bdiv => Some (to, to, to)
  | Beq | Bneq | Blt | Ble | Bgt | Bge => Some (to, to, Tbool)
  | Bmod | Band | Bor | Bxor | Bshl | Bshr | Bcmp
  | Bdotp | Bdotip | Bunsupported _ => None
  end.

(** For a binary operation between two types, determine the type of the result and the necessary conversions on the operands.

This is used for both pointer and arithmetic operators.

The first two components of the result are the types to which the
left and right operands should be converted, and the third component
is the type of the result of the operation.
 *)
Definition convert_type_op (tu : translation_unit) (b : BinOp) (ty1 ty2 : type)
  : option (type * type * type) :=
  if is_pointer ty1 && is_pointer ty2 then
    (* pointer-pointer operations *)
    match b with
    | Bsub => Some (ty1, ty2, Tptrdiff_t)
    | _ => None
    end
  else if is_pointer ty1 && is_arithmetic ty2 then
    (* pointer-integer operations *)
    match b with
    | Bsub | Badd =>
      match promote_integral tu ty2 with
      | Some ty2 => Some (ty1, ty2, ty1)
      | _ => None
      end
    | _ => None
    end
  else if is_arithmetic ty1 && is_pointer ty2 then
    (* integer-pointer operations *)
    match b with
    | Bsub | Badd =>
      match promote_integral tu ty1 with
      | Some ty1 => Some (ty1, ty2, ty2)
      | _ => None
      end
    | _ => None
    end
  else if is_arithmetic ty1 && is_arithmetic ty2 then
    match usual_float_arith tu ty1 ty2 with
    | Some to => convert_type_float_op b to
    | None =>
    (* integer-integer operations *)
    match promote_integral tu ty1 , promote_integral tu ty2 with
    | Some ity1 , Some ity2 =>
      match b with
      | Bshl | Bshr =>
        (* heterogeneous operators *)
        Some (ity1, ity2, ity1)
      | Badd | Bsub | Bmul | Bdiv | Bmod
      | Band | Bor | Bxor =>
        (* homogeneous operators *)
        match promote_arith ity1 ity2 with
        | Some to => Some (to, to, to)
        | _ => None
        end
      | Beq | Bneq
      | Blt | Ble | Bgt | Bge =>
        let same_enum :=
          match drop_qualifiers ty1 , drop_qualifiers ty2 with
          | Tenum nm1 , Tenum nm2 => if bool_decide (nm1 = nm2) then true else false
          | _ , _ => false
          end
        in
        if same_enum then
          (* Technically, this is only permitted for unscoped enumerations;
             however, the dynamic semantics lines up with the comparison on
             scoped enumerations so we do not test.
           *)
          Some (drop_qualifiers ty1, drop_qualifiers ty2, Tbool)
        else
          (* homogeneous operators *)
          match promote_arith ity1 ity2 with
          | Some to => Some (to, to, to)
          | _ => None
          end
      | Bcmp => None
      | Bdotp
      | Bdotip
      | Bunsupported _ => None
      end
    | _ , _ => None
    end
    end
  else None.
