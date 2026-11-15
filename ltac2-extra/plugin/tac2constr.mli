(*
 * Copyright (C) 2021-2023 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

open Ltac2_plugin

val to_constr : Evd.evar_map -> Tac2val.valexpr -> Constr.t
val of_constr : Constr.t -> Tac2val.valexpr

val reference_tag : (Names.GlobRef.t, Names.GlobRef.Set.t, Tac2val.valexpr Names.GlobRef.Map.t) Tac2core.map_tag
val evar_tag : (Evar.t, Evar.Set.t, Tac2val.valexpr Evar.Map.t) Tac2core.map_tag

module ConstrSet : sig
  include (Set.S with type elt = Constr.t)

  val repr : t Tac2ffi.repr
end

module ConstrMap : sig
  include (Map.S with type key = Constr.t)

  type vmap = Tac2val.valexpr t

  val repr : vmap Tac2ffi.repr
end
