(*
 * Copyright (c) 2023-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bluerock.prelude.prelude.

(** ** Errors *)
(**
Unmatchable errors to aid debugging. To use this type, write the
following:

<<
  mlock Definition error_name ...error arguments... : Error.t := inhabitant.
>>

Often, it is best to define an error as close to its use site as
possible so that it is easy to search/grep for.

Note: there is minimal maintence cost to declaring new errors, so
verbose errors can be good.

 *)
Module Type ERROR.
  Parameter t : Set.
  #[global] Declare Instance exc : Inhabited t.
End ERROR.

Module Error : ERROR.
  Definition t := unit.
  Definition exc : Inhabited t := _.
End Error.
