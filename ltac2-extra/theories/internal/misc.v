(*
 * Copyright (C) 2020-2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import skylabs.ltac2.extra.internal.init.
Require Import skylabs.ltac2.extra.internal.plugin.

Module Misc.
  Import Ltac2.Ltac2.

  Ltac2 @ external eval_whd_with_dbs_and_with_flags :
    bool -> ident list -> Std.red_flags -> constr -> constr :=
    "ltac2_extensions" "eval_whd".

  (* [gen_evar typeclass_candidate ty] generates an evar of type [ty].
     [typeclass_candidate] decides if the evar should be considered a
     candidate for typeclass search. *)
  Ltac2 @ external gen_evar : bool -> constr -> constr :=
    "ltac2_extensions" "gen_evar".

  Ltac2 @ external constr_eq_nounivs : constr -> constr -> bool :=
    "ltac2_extensions" "constr_eq_nounivs".

  Ltac2 @ external infer_conv : constr -> constr -> bool :=
    "ltac2_extensions" "infer_conv".

  Ltac2 @ external has_undef_evar : constr -> bool :=
    "ltac2_extensions" "has_undef_evar".

  Ltac2 @ external liftn : int -> int -> constr -> constr :=
    "ltac2_extensions" "liftn".

  Ltac2 @ external define_evar : evar -> constr -> bool :=
    "ltac2_extensions" "define_evar".

  Ltac2 @ external pattern_of_constr : constr -> pattern :=
    "ltac2_extensions" "pattern_of_constr".
End Misc.
