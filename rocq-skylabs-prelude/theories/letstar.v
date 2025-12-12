(*
 * Copyright (C) 2021-2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import stdpp.base.
Require Import bluerock.prelude.reserved_notation.

(** * Syntax for straight-line CPS function calls

   [let* x, y, z := t in f] is short for [t $ fun x y z => f].
   This corresponds to the bind operator of the CPS monad.

   It is best used for code that calls CPS functions which do not mess with the
   control flow.

   For example, instead of writing

   [force_app list1 list2 $ fun result => ..]

   we can instead write
   [let* result := force_app list1 list2 in ...]

   This will also avoid a right-ward drift in function code
   multiple CPS functions.

   The notation supports arbitrary numbers of binders, patterns,
   as well as type annotations in parentheses:
   [let* (a : unit), '(existT _ _ _), b := ... in ...]
 *)
Notation "'let*' x , .. , z := t 'in' f" :=
  (t (fun x => .. (fun z => f) ..)) (only parsing) : stdpp_scope.
Notation "'let*' := t 'in' f" := (t f) (only parsing) : stdpp_scope.
