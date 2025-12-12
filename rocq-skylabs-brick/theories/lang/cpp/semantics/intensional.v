(*
 * Copyright (c) 2020 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
(* This file contains intensional functions necessary to
 * describe the semantics of our AST.
 *
 * It would be great if we could eliminate this, but it
 * requires some more thought.
 *
 * Another option would be to completely pre-process the
 * AST and remove these nodes.
 *)
Require Import bluerock.lang.cpp.syntax.

(* TODO: this should probably be moved to syntax/types *)

(* this determines whether a type is initializable from a primitive.
 *)
Fixpoint prim_initializable (t : type) : bool :=
  match t with
  | Tptr _
  | Tnum _ _
  | Tchar_ _
  | Tbool
  | Tenum _
  | Tnullptr => true
  | Tqualified _ t => prim_initializable t
  | _ => false
  end.
