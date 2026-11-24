(*
 * Copyright (c) 2020-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.syntax.core.
Require Import skylabs.prelude.bytestring.

Set Primitive Projections.

Export core(Stmt(..)).
Export core(VarDecl(..)).

Notation Stmt := Stmt.
Notation MStmt := Stmt (only parsing).

Notation VarDecl := VarDecl.
Notation MVarDecl := VarDecl (only parsing).

Definition Sskip : Stmt := Sseq nil.

(* This performs a syntactic check on [s] to ensure that there are no [case] or [default]
   statements. This is used to avoid missing one of these statements which would compromise
   the soundness of [wp_switch_block]
 *)
Fixpoint no_case (s : Stmt) : bool :=
  match s with
  | Sseq ls => forallb no_case ls
  | Sdecl _ => true
  | Sif _ _ _ a b
  | Sif_consteval a b => no_case a && no_case b
  | Swhile _ _ s => no_case s
  | Sfor _ _ _ _ s => no_case s
  | Sdo s _ => no_case s
  | Sattr _ s => no_case s
  | Sswitch _ _ _ _ => true
  | Scase _
  | Sdefault => false
  | Sbreak
  | Scontinue
  | Sreturn _
  | Sreturn_nrvo _ _
  | Sexpr _
  | Sasm _ _ _ _ _ => true
  | Slabeled _ s => no_case s
  | Sgoto _ => true
  | Sunsupported _ => false
  end.

(** [stmt_decl s] is [Some ds] when [s] is the declaration statement
    [Sdecl ds], possibly labeled or with attributes. This is the single
    notion of declaration statement: [wp_switch_block] treats such a statement
    as a barrier that no [case] may follow, since the variables it declares
    would be missing from the scope that follows. *)
Fixpoint stmt_decl (s : Stmt) : option (list VarDecl) :=
  match s with
  | Sdecl ds => Some ds
  | Slabeled _ s | Sattr _ s => stmt_decl s
  | _ => None
  end.

Definition is_decl (s : Stmt) : bool := if stmt_decl s is Some _ then true else false.
