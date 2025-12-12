(*
 * Copyright (c) 2023-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bluerock.lang.cpp.mparser.prelude.
Require Import bluerock.lang.cpp.syntax.types.
Require Import bluerock.lang.cpp.syntax.typing. (* TODO: use [typed]? *)
Require Import bluerock.lang.cpp.syntax.overloadable.
Require Import bluerock.lang.cpp.parser.expr.

Include ParserExpr.

(** ** Template-only derived expressions emitted by cpp2v *)
(**
Clang's parser delays reasoning about templated code until
instantiation/specialization time.

This means cpp2v can emit terms without meaningful type information.
We account for this in two steps:

1/ For terms where cpp2v may omit a type inferrable from subterms, we
define functions taking an optional type, and either infer a type or
construct an appropriate unresolved term.

2/ For direct initializers where cpp2v may omit a dependent target
type, our language makes such types optional (e.g., in
[Eunresolved_parenlist]) and we fill in those types from context.

TODO: We can probably improve on the following simple
[{BinOp,UnOp].resolve] setup; for example, by considering the set of
candidate overloads. Consider the following examples.

<<
template<typename T>
void test() {
  struct S {
    int val;
    S& operator=(const T& t) { val = t.getval(); return *this; }
  };
  T t;
  S s;
  s = t;	// Could be resolved to type `S&`.

  struct C {
    int val;
    C& operator=(int) { val = 1; return *this; }
    C& operator=(float) { val = 2; return *this; }
  };
  C c;
  c = s;	// Ought to remain unresolved. The choice of overload depends on `T`.
}
>>

*)
Module BinOp.

  Definition is_unresolved (t : Mtype) : bool :=
    match drop_qualifiers (drop_reference t) with
    | Tdecltype _
    | Texprtype _
    | Tauto
    | Tresult_param _
    | Tparam _
    | Tresult_binop _ _ _
    | Tresult_unop _ _
    | Tresult_call _ _
    | Tresult_member_call _ _ _
    | Tresult_member _ _
    | Tresult_parenlist _ _ => true
    | _ => false
    end.

  (** TODO: Arguably misplaced *)
  Definition Ebinary_operator (r : RBinOp) : MExpr -> MExpr -> Mexprtype -> MExpr :=
    match r with
    | Rbinop op => Ebinop op
    | Rassign => Eassign
    | Rassign_op op => Eassign_op op
    | Rsubscript => Esubscript
    end.

  (** The type of binary operators emitted by cpp2v *)
  Definition t : Set := MExpr -> MExpr -> option Mexprtype -> MExpr.

  Definition resolve : Set := Mexprtype -> Mexprtype -> Mexprtype.
  Definition infer (op : RBinOp) (resolve : resolve) : t := fun l r m =>
    let R : Mexprtype -> MExpr := Ebinary_operator op l r in
    match m with
    | Some t => R t
    | None =>
      let lt := type_of l in
      let rt := type_of r in
      if is_unresolved lt || is_unresolved rt then
        Eunresolved_binop op l r
      else
        R $ resolve lt rt
    end.

  Definition resolve_left : resolve := fun tl tr => tl.

  (**
  https://en.cppreference.com/w/cpp/language/operator_member_access#Built-in_subscript_operator
  *)
  Definition infer_subscript : t := fun l r ot =>
    let tl := decltype_of_expr l in
    let tr := decltype_of_expr r in
    let is_idx (t : Mdecltype) : bool :=
      match t with
      | Tnum _ _ | Tchar_ _ | Tbool => true
      | _ => false
      end
    in
    let is_ary (t : Mdecltype) : option (Mtype * (MExpr -> MExpr)) :=
      match t with
      | Tref (Tptr ety) => Some (ety, fun e => Ecast core.Cl2r e)
      | Tref (Tarray ety _ | Tincomplete_array ety | Tvariable_array ety _) =>
          Some (ety, fun e => e)
      | Trv_ref (Tarray ety _ | Tincomplete_array ety | Tvariable_array ety _) =>
          Some (ety, fun e => e)
      | _ => None
      end
    in
    let default := Eunresolved_binop Rsubscript l r in
    if is_idx tl then
      match is_ary tr with
      | None => default
      | Some (ty, C) => Esubscript l (C r) ty
      end
    else if is_idx tr then
           match is_ary tl with
           | None => default
           | Some (ty, C) => Esubscript (C l) r ty
           end
         else default.

  (**
  https://en.cppreference.com/w/cpp/language/operator_arithmetic#Additive_operators
  *)
  Definition resolve_add : resolve := fun tl tr =>
    match drop_qualifiers tl, drop_qualifiers tr with
    | (Tnum _ _ | Tenum _), Tptr _ => tr
    | _, _ => tl
    end.
  Definition ptrdiff_t : Mtype := Tlong.	(** TODO: Impl. defined *)
  Definition resolve_sub : resolve := fun tl tr =>
    match drop_qualifiers tl, drop_qualifiers tr with
    | Tptr tl, Tptr tr =>
      if bool_decide (drop_qualifiers tl = drop_qualifiers tr)
      then ptrdiff_t
      else Tunsupported "[mparser] Ebinop Bsub: incompatible pointer types"
    | _, _ => tl
    end.
  Definition resolve_comparison : resolve := fun tl tr =>
    Tbool.
  Definition resolve_todo (msg : PrimString.string) : resolve := fun tl tr =>
    Tunsupported ("[mparser] Ebinop todo: " ++ msg).

  Definition resolve_binop (op : BinOp) : resolve :=
    match op with
    | Badd => resolve_add
    | Bsub => resolve_sub
    | Band | Bdiv | Bmul | Bor | Bmod | Bshl | Bshr | Bxor => resolve_left
    | Bcmp | Beq | Bge | Bgt | Ble | Blt | Bneq => resolve_comparison
    | Bdotp => resolve_todo "Bdotp"
    | Bdotip => resolve_todo "Bdotip"
    | Bunsupported op => fun _ _ => Tunsupported ("[mparser] Ebinop unsupported: " ++ op)
    end.

End BinOp.

Definition Eassign : BinOp.t :=
  BinOp.infer Rassign BinOp.resolve_left.
Definition Eassign_op (op : BinOp) : BinOp.t :=
  BinOp.infer (Rassign_op op) BinOp.resolve_left.
Definition Esubscript : BinOp.t :=
  BinOp.infer_subscript.
Definition Ebinop (op : BinOp) : BinOp.t :=
  BinOp.infer (Rbinop op) $ BinOp.resolve_binop op.

Module UnOp.

  (** TODO: Arguably misplaced *)
  Definition Eunary_operator (r : RUnOp) : MExpr -> Mexprtype -> MExpr :=
    match r with
    | Runop op => Eunop op
    | Rpreinc => Epreinc
    | Rpredec => Epredec
    | Rpostinc => Epostinc
    | Rpostdec => Epostdec
    | Rstar => Ederef
    | Rarrow => Ederef (* << not used, BRiCk prints this as [Eunresolved_member] *)
    end.

  Definition t : Set := MExpr -> option Mexprtype -> MExpr.

  Definition resolve : Set := Mexprtype -> option Mexprtype.
  Definition infer (op : RUnOp) (resolve : resolve) : t := fun e m =>
    let R : Mexprtype -> MExpr := Eunary_operator op e in
    match m with
    | Some t => R t
    | None =>
      let t := type_of e in
      match op , t with
      | Rpreinc , (Tptr _) => Epreinc e t
      | Rpredec , (Tptr _) => Epredec e t
      | Rpostinc , (Tptr _) => Epostinc e t
      | Rpostdec , (Tptr _) => Epostdec e t
      | Runop Uplus , Tptr _ => Eunop Uplus e Tlonglong
      | _ , _ =>
        if is_dependentT t then
          Eunresolved_unop op e
        else
          match resolve t with
          | None => Eunresolved_unop op e
          | Some t => R t
          end
      end
    end.

  Definition todo : resolve := fun t =>
    None (* Tunsupported "[mparser] todo: Eunop inference". *).

  Definition is_ptr : resolve := fun t =>
    match drop_qualifiers t with
    | Tptr t => Some t
    | _ => None
    end.

End UnOp.

Definition Eunop (op : UnOp) : UnOp.t := UnOp.infer (Runop op) UnOp.todo.
Definition Epreinc : UnOp.t := UnOp.infer Rpreinc UnOp.is_ptr.
Definition Epredec : UnOp.t := UnOp.infer Rpredec UnOp.is_ptr.
Definition Epostinc : UnOp.t := UnOp.infer Rpostinc UnOp.is_ptr.
Definition Epostdec : UnOp.t := UnOp.infer Rpostdec UnOp.is_ptr.
#[local] Definition Earrow : UnOp.t := UnOp.infer Rarrow UnOp.is_ptr.
Definition Ederef : UnOp.t := UnOp.infer Rstar UnOp.is_ptr.

(* TODO: the handling of [Eunresolved_member] isn't quite right *)
Definition Eunresolved_member (arrow : bool) (base : MExpr) (i : Mname) : MExpr :=
  if arrow then
    Eunresolved_member (Earrow base None) i
  else
    Eunresolved_member base i.

(** ** Template-only derived variable declarations emitted by cpp2v *)

#[local] Definition set_declared_type (t : Mdecltype) (e : MExpr) : MExpr :=
  match e with
  | Eunresolved_parenlist None es => Eunresolved_parenlist (Some t) es
  (**
  TODO: The same treatment for other direct initiailization
  expressions.
  *)
  | _ => e
  end.
