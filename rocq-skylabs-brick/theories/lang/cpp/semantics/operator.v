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

Require Import bluerock.prelude.base.
Require Import bluerock.prelude.numbers.
Require Export bluerock.prelude.arith.operator.
Require Import bluerock.lang.cpp.syntax.
Require Import bluerock.lang.cpp.semantics.values.

#[local] Open Scope Z_scope.

(* [arith_as ty] returns [Some (sz, sgn)] if arithmetic operations are allowed on
   the type [ty] using the size [sz] and the signedness [sgn].
 *)
Definition arith_as (ty : type) : option (int_rank.t * signed) :=
  match drop_qualifiers ty with
  | Tnum sz sgn => if bool_decide (int_rank.t_le int_rank.Iint sz) then Some (sz, sgn) else None
  | _ => None
  end.

Class supports_arith (ty : type) : Prop :=
  { _ : arith_as ty <> None }.

#[global] Instance: supports_arith Tint.
Proof. constructor; compute; congruence. Qed.
#[global] Instance: supports_arith Tuint.
Proof. constructor; compute; congruence. Qed.
#[global] Instance: supports_arith Tlong.
Proof. constructor; compute; congruence. Qed.
#[global] Instance: supports_arith Tulong.
Proof. constructor; compute; congruence. Qed.
#[global] Instance: supports_arith Tlonglong.
Proof. constructor; compute; congruence. Qed.
#[global] Instance: supports_arith Tulonglong.
Proof. constructor; compute; congruence. Qed.

Succeed Example supports_arith_long : supports_arith Tlong := _.
Succeed Example supports_arith_ulong : supports_arith Tulong := _.

Module Type OPERATOR_INTF_FUNCTOR
  (Import P : PTRS_INTF)
  (Import INTF : VALUES_INTF_FUNCTOR PTRS_INTF_AXIOM).
  (** * Operator semantics

      To support implementation-defined semantics and semantics that differs
      (usually by removing undefined behavior) between language versions,
      we expose these as relations, though they could also be exposed as
      partial functions.
   *)

  (** [eval_unop tu op argT resT arg res] holds when evaluating
      [op] on [arg] (such that [has_type_prop arg argT]) result in [res]
      (and [has_type_prop res resT]).

      NOTE: the reasoning principles for [eval_unop] require that
            the values are well-typed.
   *)
  Parameter eval_unop : forall {σ : genv},
      translation_unit -> UnOp -> forall (argT resT : type) (arg res : val), Prop.

  Axiom eval_unop_pure_well_typed : forall `{MOD : tu ⊧ σ} uo ty1 ty2 v1 v2,
      eval_unop tu uo ty1 ty2 v1 v2 ->
      has_type_prop v1 ty1 /\ has_type_prop v2 ty2.

  (** [eval_binop_pure tu op lhsT rhsT resultT lhsV rhsV resultV] holds when
      evaluating [lhsV `op` rhsV] (such that [has_type_prop lhsV lhsT] and
      [has_type_prop rhsV rhsT]) results in [resultT] (and
      [has_type_prop resultV resultT]).

      NOTE: the reasoning principles for [eval_binop_pure] require that
            the values are well-typed.
   *)
  Parameter eval_binop_pure : forall `{σ : genv},
      translation_unit -> BinOp -> forall (lhsT rhsT resT : type) (lhs rhs res : val), Prop.

  Axiom eval_binop_pure_well_typed : forall `{MOD : tu ⊧ σ} bo ty1 ty2 ty3 v1 v2 v3,
      eval_binop_pure tu bo ty1 ty2 ty3 v1 v2 v3 ->
      has_type_prop v1 ty1 /\ has_type_prop v2 ty2 /\ has_type_prop v3 ty3.

Section operator_axioms.
  Context {σ : genv} (tu : translation_unit).
  #[local] Notation eval_unop := (eval_unop tu).
  #[local] Notation eval_binop_pure := (eval_binop_pure tu).

(** * Unary Operators *)

(* The builtin unary `!` operator logically negates its argument, i.e. `true` -> `false` and
   `false` -> `true`.
   https://eel.is/c++draft/expr.unary.op#9
 *)
Axiom eval_not_bool : forall a,
    eval_unop Unot Tbool Tbool (Vbool a) (Vbool (negb a)).

(* The builtin unary `~` operator computes the bitwise negation of the operator
   https://eel.is/c++draft/expr.unary.op#10

   NOTE [Z.lnot a = -1 - a]
 *)
Axiom eval_unop_not : forall w (sgn : signed) (a : Z),
    let b := match sgn with
             | Signed => -1 - a
             | Unsigned => bitFlipZU (int_rank.bitsN w) a
             end in
    has_type_prop (Vint b) (Tnum w sgn) ->
    eval_unop Ubnot (Tnum w sgn) (Tnum w sgn)
              (Vint a) (Vint b).

(* The builtin unary `+` operator is the identity on arithmetic types.
   https://eel.is/c++draft/expr.unary.op#7
 *)
Axiom eval_plus_int : forall `{supports_arith ty} a,
    has_type_prop (Vint a) ty ->
    eval_unop Uplus ty ty (Vint a) (Vint a).

(* The builtin unary `-` operator calculates the negative of its
   promoted operand. For unsigned a, the value of -a is 2^b -a, where b
   is the number of bits after promotion.
   https://eel.is/c++draft/expr.unary.op#8
 *)
Axiom eval_minus_int : forall ty a c,
    has_type_prop (Vint a) ty ->
    match arith_as ty with
    | Some (_, Signed) => c = 0 - a
    | Some (w, Unsigned) => c = trim (int_rank.bitsN w) (0 - a)
    | None => False
    end ->
    has_type_prop (Vint c) ty ->
    eval_unop Uminus ty ty (Vint a) (Vint c).

(** * Binary Operators *)

(** ** Arithmetic Operators

    (includes: `+`, `-`, `*`, `/`, and `%`)
    These are type homogeneous, i.e. both arguments must be the same type.
    Further, these operations only apply to arithmetic types with rank
    greater than or equal to `int`.

    NOTE: Integral conversions will occur outside of [eval_binop_pure] to
          make the arguments homogeneous.
 *)
Let eval_int_op (bo : BinOp) (o : Z -> Z -> Z) : Prop :=
  forall ty (a b c : Z),
    has_type_prop (Vint a) ty ->
    has_type_prop (Vint b) ty ->
    match arith_as ty with
    | Some (_, Signed) => c = o a b
    | Some (sz, Unsigned) => c = trim (int_rank.bitsN sz) (o a b)
    | None => False
    end ->
    has_type_prop (Vint c) ty ->
    eval_binop_pure bo ty ty ty (Vint a) (Vint b) (Vint c).

Axiom eval_add : Hnf (eval_int_op Badd Z.add).
Axiom eval_sub : Hnf (eval_int_op Bsub Z.sub).
Axiom eval_mul : Hnf (eval_int_op Bmul Z.mul).

(* The binary operator / divides the first operand by the second, after usual
   arithmetic conversions.
   The quotient is truncated towards zero (fractional part is discarded),
   since C++11.
   If the second operand is zero, the behavior is undefined.
   If the quotient is not representable, then the behavior is undefined.

   See https://eel.is/c++draft/expr.mul#4
 *)
Axiom eval_div : forall `{supports_arith ty} (a b : Z),
    b <> 0%Z ->
    has_type_prop (Vint a) ty ->
    has_type_prop (Vint b) ty ->
    let c := Z.quot a b in
    has_type_prop (Vint c) ty ->
    eval_binop_pure Bdiv ty ty ty (Vint a) (Vint b) (Vint c).
Axiom eval_mod : forall `{supports_arith ty} (a b : Z),
    b <> 0%Z ->
    has_type_prop (Vint a) ty ->
    has_type_prop (Vint b) ty ->
    has_type_prop (Vint (Z.quot a b)) ty ->
    let c := Z.rem a b in
    eval_binop_pure Bmod ty ty ty (Vint a) (Vint b) (Vint c).

(** ** bitwise operators

    (includes: `&`, `|`, and `^`)
    These are type homogeneous, i.e. both arguments must be the same type.
    Further, these operations only apply to arithmetic types with rank
    greater than or equal to `int`.

    NOTE: Integral conversions will occur outside of [eval_binop_pure] to
          make the arguments homogeneous.

 *)
Let eval_int_bitwise_op (bo : BinOp) (o : Z -> Z -> Z) : Prop :=
  forall ty (_ : supports_arith ty) (a b : Z),
    has_type_prop (Vint a) ty ->
    has_type_prop (Vint b) ty ->
    let c := o a b in (* note that bitwise operators respect bounds *)
    eval_binop_pure bo ty ty ty (Vint a) (Vint b) (Vint c).

(* bitwise(logical) operators *)
Axiom eval_or : Hnf (eval_int_bitwise_op Bor Z.lor).
Axiom eval_and : Hnf (eval_int_bitwise_op Band Z.land).
Axiom eval_xor : Hnf (eval_int_bitwise_op Bxor Z.lxor).
Arguments eval_or _ {_} _ _ _ _.
Arguments eval_and _ {_} _ _ _ _.
Arguments eval_xor _ {_} _ _ _ _.



(** ** Shifting Operators

    (includes: `<<` and `>>`)
    Note that these are *not* homogeneous but boths sides must still be
    arithmetic types. The result type is always the type of the left-hand-side.
 *)

(* C++14 <= VER < C++20 *)
(* The value of E1 << E2 is E1 left-shifted E2 bit positions; vacated
   bits are zero-filled. If E1 has an unsigned type, the value of the
   result is E1 * 2^E2, reduced modulo one more than the maximum value
   representable in the result type. Otherwise, if E1 has a signed
   type and non-negative value, and E1 * 2 ^ E2 is representable in
   the corresponding unsigned type of the result type, then that
   value, converted to the result type, is the resulting value;
   otherwise, the behavior is undefined.  *)
(* The behavior is undefined if the right operand is negative, or
   greater than or equal to the length in bits of the promoted left
   operand.
In overload resolution against user-defined operators, for every pair of promoted integral types L and R, the following function signatures participate in overload resolution:

L operator<<(L, R)
L operator>>(L, R)

NOTE: Shift operators are *not* homogeneous.
  *)

Axiom eval_shl : forall ty `{supports_arith ty_by} w sgn (a b : Z),
    arith_as ty = Some (w, sgn) ->
    (0 <= b < int_rank.bitsN w)%Z ->
    (0 <= a)%Z ->
    has_type_prop (Vint a) ty ->
    has_type_prop (Vint b) ty_by ->
    let c := match sgn with
             | Signed => Z.shiftl a b
             | Unsigned => trim (int_rank.bitsN w) (Z.shiftl a b)
             end in
    has_type_prop (Vint c) ty ->
    eval_binop_pure Bshl ty ty_by ty (Vint a) (Vint b) (Vint c).

(* C++14 <= VER < C++20: The value of E1 >> E2 is E1 right-shifted E2 bit
   positions. If E1 has an unsigned type or if E1 has a signed type
   and a non-negative value, the value of the result is the integral
   part of the quotient of E1/(2^E2). If E1 has a signed type and a
   negative value, the resulting value is implementation-defined. *)
Axiom eval_shr : forall ty `{supports_arith ty_by} w sgn (a b : Z),
    arith_as ty = Some (w, sgn) ->
    (0 <= b < int_rank.bitsN w)%Z ->
    (0 <= a)%Z ->
    has_type_prop (Vint a) ty ->
    has_type_prop (Vint b) ty_by ->
    let c := match sgn with
             | Signed => Z.shiftr a b
             | Unsigned => trim (int_rank.bitsN w) (Z.shiftr a b)
             end in
    has_type_prop (Vint c) ty ->
    eval_binop_pure Bshr ty ty_by ty (Vint a) (Vint b) (Vint c).

(** ** comparison operators

    (includes: `<`, `<=`, `==`, `!=`, `>=`, `>`, and `<=>`)
    These are type-homogeneous on inputs and have an output
    of either `bool` (in C++) or `int` (in C).
 *)

(** Relational comparisons are allowed on *scoped* enumerations
    in addition to integral types. We relax this to also allow
    comparisons on unscoped enumerations.

    This is safe because the dynamic semantics of comparison is
    defined the same way as it is on the underlying type.

    In addition, the BRiCk AST explicitly contains the conversions
    for unscoped enumerations, so, in practice, comparison of naked
    unscoped enumeration values will never occur.
 *)
Class supports_rel (ty : type) : Prop :=
{ _ : supports_arith ty \/
      match drop_qualifiers ty with
      | Tenum _ => True
      | _ => False
      end }.

#[global] Instance: supports_rel Tint.
Proof. constructor; left; refine _. Qed.
#[global] Instance: supports_rel Tuint.
Proof. constructor; left; refine _. Qed.
#[global] Instance: supports_rel Tlong.
Proof. constructor; left; refine _. Qed.
#[global] Instance: supports_rel Tulong.
Proof. constructor; left; refine _. Qed.
#[global] Instance: supports_rel Tlonglong.
Proof. constructor; left; refine _. Qed.
#[global] Instance: supports_rel Tulonglong.
Proof. constructor; left; refine _. Qed.
#[global] Instance: forall nm, supports_rel (Tenum nm).
Proof. constructor; right; exact I. Qed.


(** [relop_result_type ty] holds on types [ty] that can be the result of a
    relational operator comparison, e.g. `==` or `<`.
    In C++ this is the type `bool`, in C this is the type `int`.

    NOTE: We rely on the AST to have the appropriate type for the language
          being used.
 *)
Definition relop_result_type (ty : type) : Prop :=
  match ty with
  | Tint (* this is literally the type `int`, *not* any numeric type *)
  | Tbool => True
  | _ => False
  end.

(* injection of [bool] into [Z]
 *)
Definition b2i (b : bool) : Z := if b then 1 else 0.

(* Integer conversions are used to compare unscoped enumeration types but not
   scoped ones. Therefore, we include comparisons on enum. The values are
   compared after integer conversion.

   Note that the [has_type_prop] facts guarantees that the enum is valid if [ty] is
   an enum.
 *)
#[local] Definition eval_int_rel_op (o : Z -> Z -> Prop) {RD : RelDecision o} (bo : BinOp) : Prop :=
  forall ty (_ : supports_rel ty) ty' (av bv : Z),
    let a := Vint av in
    let b := Vint bv in
    relop_result_type ty' ->
    has_type_prop a ty ->
    has_type_prop b ty ->
    eval_binop_pure bo ty ty ty' a b (Vbool $ bool_decide (o av bv)).

Axiom eval_eq : Hnf (eval_int_rel_op eq Beq).
Axiom eval_neq : Hnf (eval_int_rel_op (fun a b => a <> b) (RD:=ltac:(red; refine _)) Bneq).
Axiom eval_lt : Hnf (eval_int_rel_op Z.lt Blt).
Axiom eval_gt : Hnf (eval_int_rel_op Z.gt Bgt).
Axiom eval_le : Hnf (eval_int_rel_op Z.le Ble).
Axiom eval_ge : Hnf (eval_int_rel_op Z.ge Bge).
Arguments eval_eq _ {_}.
Arguments eval_neq _ {_}.
Arguments eval_lt _ {_}.
Arguments eval_le _ {_}.
Arguments eval_gt _ {_}.
Arguments eval_ge _ {_}.

End operator_axioms.
End OPERATOR_INTF_FUNCTOR.

(* Collect all the axioms. *)

Module Export OPERATOR_INTF_AXIOM <: OPERATOR_INTF_FUNCTOR PTRS_INTF_AXIOM VALUES_INTF_AXIOM.
  Include OPERATOR_INTF_FUNCTOR PTRS_INTF_AXIOM VALUES_INTF_AXIOM.
End OPERATOR_INTF_AXIOM.
