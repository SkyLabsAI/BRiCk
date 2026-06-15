(*
 * Copyright (c) 2020-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import skylabs.lang.cpp.syntax.

(** ** Evaluation Order *)
Variant t : Set :=
| nd (* fully non-deterministic *)
| l_nd (* left then non-deterministic, calls.
          We use this for left-to-right *binary* operators *)
| rl (* right-to-left, assignment operators (post C++17) *).

Definition since_cpp17 (ver : lang_version.t) : bool :=
  negb (lang_version.lt ver lang_version.Cpp17).

(* The order of evaluation for each operator *when overloaded* *)
Definition order_of (ver : lang_version.t) (oo : OverloadableOperator) : t :=
  match oo with
  | OOTilde | OOExclaim => nd
  | OOPlusPlus | OOMinusMinus =>
    (* The evaluation order only matters for operator calls. For those, these
       are unary operators with a possible [Eint 0] as a second argument (to
       distinguish post-fix). The implicit argument is *always* a constant
       integer, so nothing is needed *)
    l_nd
  | OOStar => nd (* multiplication or deref *)
  | OOArrow => nd (* deref *)

  (* binary operators *)
  | OOPlus | OOMinus | OOSlash | OOPercent
  | OOCaret | OOAmp | OOPipe => nd

  (* shift operators are sequenced left-to-right: https://eel.is/c++draft/expr.shift#4. *)
  | OOLessLess | OOGreaterGreater =>
    if since_cpp17 ver then l_nd else nd
  (* Assignment operators -- ordered right-to-left*)
  | OOEqual
  | OOPlusEqual  | OOMinusEqual | OOStarEqual
  | OOSlashEqual | OOPercentEqual | OOCaretEqual | OOAmpEqual
  | OOPipeEqual  | OOLessLessEqual | OOGreaterGreaterEqual =>
    if since_cpp17 ver then rl else nd
  (* Comparison operators -- non-deterministic *)
  | OOEqualEqual | OOExclaimEqual
  | OOLess | OOGreater
  | OOLessEqual | OOGreaterEqual
  | OOSpaceship => nd

  | OOComma => l_nd (* http://eel.is/c++draft/expr.compound#expr.comma-1 *)
  | OOArrowStar =>
    if since_cpp17 ver then l_nd else nd
    (* left-to-right: http://eel.is/c++draft/expr.mptr.oper#4 *)

  | OOSubscript => if since_cpp17 ver then l_nd else nd
  (* ^^ for primitives, the order is determined by the types, but when overloading
     the "object" is always on the left. http://eel.is/c++draft/expr.sub#1 *)

  (* Short circuiting *)
  | OOAmpAmp | OOPipePipe => l_nd
  (* ^^ for primitives, the evaluation is based on short-circuiting, but when
     overloading it is left-to-right. <http://eel.is/c++draft/expr.log.and#1>
     and <http://eel.is/c++draft/expr.log.and#1> *)

  | OOCall => if since_cpp17 ver then l_nd else nd
  (* ^^ post-C++17, the evaluation order for calls is the function first and then the
     arguments, sequenced non-deterministically. This holds for <<f(x)>> as well as
     <<(f.*foo)(x)>> (where <<(f.*foo)>> is sequenced before the evaluation of <<x>> *)
  | OONew _ | OODelete _ | OOCoawait => nd
  end.
