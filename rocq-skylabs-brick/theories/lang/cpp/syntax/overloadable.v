(*
 * Copyright (c) 2023-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bluerock.lang.cpp.syntax.prelude.
Require Import bluerock.lang.cpp.syntax.preliminary.

(** ** Unary, dependent expression constructor names *)

Variant RUnOp : Set :=
| Runop (op : UnOp)
| Rpreinc
| Rpredec
| Rpostinc
| Rpostdec
| Rstar
| Rarrow
.
#[global] Instance RUnOp_eq_ec : EqDecision RUnOp.
Proof. solve_decision. Defined.
Section countable.
  #[local] Notation OP x := (GenLeaf x).

  #[global] Instance RUnOp_countable : Countable RUnOp.
  Proof.
    apply (inj_countable' (fun op =>
      match op with
      | Runop op => GenNode 0 [OP op]
      | Rpreinc => GenNode 1 []
      | Rpredec => GenNode 2 []
      | Rpostinc => GenNode 3 []
      | Rpostdec => GenNode 4 []
      | Rstar => GenNode 5 []
      | Rarrow => GenNode 6 []
      end) (fun tree =>
      match tree with
      | GenNode 0 [OP op] => Runop op
      | GenNode 1 [] => Rpreinc
      | GenNode 2 [] => Rpredec
      | GenNode 3 [] => Rpostinc
      | GenNode 4 [] => Rpostdec
      | GenNode 5 [] => Rstar
      | GenNode 6 [] => Rarrow
      | _ => Rpreinc	(* dummy *)
      end)).
    abstract (by intros []).
  Defined.
End countable.

(** ** Binary, dependent expression constructor names *)

Variant RBinOp : Set :=
| Rbinop (op : BinOp)
| Rassign
| Rassign_op (op : BinOp)
| Rsubscript
.
#[global] Instance RBinOp_eq_ec : EqDecision RBinOp.
Proof. solve_decision. Defined.
Section countable.
  #[local] Notation OP x := (GenLeaf x).
  #[global] Instance RBinOp_countable : Countable RBinOp.
  Proof.
    apply (inj_countable' (fun op =>
      match op with
      | Rbinop op => GenNode 0 [OP op]
      | Rassign => GenNode 1 []
      | Rassign_op op => GenNode 2 [OP op]
      | Rsubscript => GenNode 3 []
      end) (fun t =>
      match t with
      | GenNode 0 [OP op] => Rbinop op
      | GenNode 1 [] => Rassign
      | GenNode 2 [OP op] => Rassign_op op
      | GenNode 3 [] => Rsubscript
      | _ => Rassign	(* dummy *)
      end)).
    abstract (by intros []).
  Defined.
End countable.
