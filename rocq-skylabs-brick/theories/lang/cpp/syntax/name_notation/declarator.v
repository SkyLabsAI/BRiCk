(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.lang.cpp.syntax.core.

(* An omitted bound is allowed only in the outermost dimension of each
   array type. Pointer declarators can separate distinct array types. *)
Fixpoint is_incomplete_array (ty : type) : bool :=
  match ty with
  | Tincomplete_array _ => true
  | Tqualified _ t => is_incomplete_array t
  | _ => false
  end.

(* Check the declarator spine. Function parameters are checked separately
   by the recursive parser/printer calls for each parameter type. *)
Fixpoint valid_array_bounds (ty : type) : bool :=
  match ty with
  | Tarray t _ | Tincomplete_array t | Tvariable_array t _ =>
      negb (is_incomplete_array t) && valid_array_bounds t
  | Tptr t | Tref t | Trv_ref t | Tqualified _ t | Tmember_pointer _ t =>
      valid_array_bounds t
  | Tfunction ft => valid_array_bounds ft.(ft_return)
  | _ => true
  end.
